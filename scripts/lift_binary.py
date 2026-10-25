#!/usr/bin/env python3
"""Lift an RV64 ELF to addressed Sail IR and generate a Lean lifting certificate.

The Python ELF reader and decoder propose nodes. Lean independently checks every
node's bytes with its ELF loader and its meaning with Sail's actual decoder.
--proof-module imports a Lean module exporting contract : Lifted.Contract.
The driver checks that its proved program matches the lifted instructions and
transfers its Hoare theorem to the binary. Lifting alone does NOT establish
equivalence to a source program.
"""

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys

from verify_binary import ALLOWED_AXIOMS, ROOT, run


def signed(value: int, width: int) -> int:
    return value - (1 << width) if value & (1 << (width - 1)) else value


@dataclass(frozen=True)
class Instruction:
    address: int
    word: int
    op: str
    rd: int = 0
    rs1: int = 0
    rs2: int = 0
    imm: int = 0
    sail: str = ""


def decode(address: int, word: int) -> Instruction:
    """A candidate decoder; no result is certified until Lean checks Sail decode."""
    opcode, rd = word & 127, (word >> 7) & 31
    funct3, rs1, rs2, funct7 = (word >> 12) & 7, (word >> 15) & 31, (word >> 20) & 31, word >> 25
    reg = lambda n: f"(.Regidx {n})"
    raw_imm, imm = word >> 20, signed(word >> 20, 12)
    if opcode in (0x33, 0x3b):
        ops = {(0, 0): "add", (0, 32): "sub", (1, 0): "sll", (2, 0): "slt",
               (3, 0): "sltu", (4, 0): "xor", (5, 0): "srl", (5, 32): "sra",
               (6, 0): "or", (7, 0): "and"}
        op = ops.get((funct3, funct7))
        if op and (opcode == 0x33 or op in ("add", "sub", "sll", "srl", "sra")):
            tag = "RTYPE" if opcode == 0x33 else "RTYPEW"
            op += "w" if opcode == 0x3b else ""
            return Instruction(address, word, op, rd, rs1, rs2, sail=
                               f".{tag} ({reg(rs2)}, {reg(rs1)}, {reg(rd)}, .{op.upper()})")
    elif opcode == 0x13:
        ops = {0: "addi", 2: "slti", 3: "sltiu", 4: "xori", 6: "ori", 7: "andi"}
        if funct3 in ops:
            op = ops[funct3]
            return Instruction(address, word, op, rd, rs1, imm=imm, sail=
                               f".ITYPE ({raw_imm}, {reg(rs1)}, {reg(rd)}, .{op.upper()})")
        if (funct3, word >> 26) in ((1, 0), (5, 0), (5, 16)):
            op = "slli" if funct3 == 1 else "srai" if word >> 26 else "srli"
            return Instruction(address, word, op, rd, rs1, imm=raw_imm & 63, sail=
                               f".SHIFTIOP ({raw_imm & 63}, {reg(rs1)}, {reg(rd)}, .{op.upper()})")
    elif opcode == 0x1b:
        if funct3 == 0:
            return Instruction(address, word, "addiw", rd, rs1, imm=imm, sail=
                               f".ADDIW ({raw_imm}, {reg(rs1)}, {reg(rd)})")
        if (funct3, funct7) in ((1, 0), (5, 0), (5, 32)):
            op = "slliw" if funct3 == 1 else "sraiw" if funct7 else "srliw"
            return Instruction(address, word, op, rd, rs1, imm=rs2, sail=
                               f".SHIFTIWOP ({rs2}, {reg(rs1)}, {reg(rd)}, .{op.upper()})")
    elif opcode == 0x63 and funct3 in (0, 1, 4, 5, 6, 7):
        raw = ((word >> 31) << 12) | (((word >> 7) & 1) << 11) | (((word >> 25) & 63) << 5) | (((word >> 8) & 15) << 1)
        op = {0: "beq", 1: "bne", 4: "blt", 5: "bge", 6: "bltu", 7: "bgeu"}[funct3]
        return Instruction(address, word, op, rs1=rs1, rs2=rs2, imm=signed(raw, 13), sail=
                           f".BTYPE ({raw}, {reg(rs2)}, {reg(rs1)}, .{op.upper()})")
    elif opcode == 0x6f:
        raw = ((word >> 31) << 20) | (((word >> 12) & 255) << 12) | (((word >> 20) & 1) << 11) | (((word >> 21) & 1023) << 1)
        return Instruction(address, word, "jal", rd, imm=signed(raw, 21), sail=
                           f".JAL ({raw}, {reg(rd)})")
    elif opcode == 0x67 and funct3 == 0:
        return Instruction(address, word, "jalr", rd, rs1, imm=imm, sail=
                           f".JALR ({raw_imm}, {reg(rs1)}, {reg(rd)})")
    elif opcode == 0x03 and funct3 == 3:
        return Instruction(address, word, "ld", rd, rs1, imm=imm, sail=
                           f".LOAD ({raw_imm}, {reg(rs1)}, {reg(rd)}, false, 8)")
    elif opcode == 0x23 and funct3 == 3:
        raw = ((word >> 25) << 5) | ((word >> 7) & 31)
        return Instruction(address, word, "sd", rs1=rs1, rs2=rs2, imm=signed(raw, 12), sail=
                           f".STORE ({raw}, {reg(rs2)}, {reg(rs1)}, 8)")
    elif opcode in (0x17, 0x37):
        op = "auipc" if opcode == 0x17 else "lui"
        return Instruction(address, word, op, rd, imm=signed(word & 0xfffff000, 32), sail=
                           f".UTYPE ({word >> 12}, {reg(rd)}, .{op.upper()})")
    raise ValueError(f"Unsupported instruction 0x{word:08x} at 0x{address:x}")


def read_elf(data: bytes, symbol: str | None = None) -> tuple[int, list[Instruction]]:
    if len(data) < 64 or data[:7] != b"\x7fELF\x02\x01\x01":
        raise ValueError("Expected ELF64 little-endian executable")
    kind, machine, version = struct.unpack_from("<HHI", data, 16)
    if (kind, machine, version) != (2, 243, 1) or struct.unpack_from("<I", data, 48)[0] != 0:
        raise ValueError("Expected static RV64 ELF without compressed/ABI extension flags")
    entry, phoff, shoff = struct.unpack_from("<QQQ", data, 24)
    phsize, phnum, shsize, shnum = struct.unpack_from("<HHHH", data, 54)
    if phsize != 56 or phoff < 64 or phoff + phsize * phnum > len(data):
        raise ValueError("Invalid ELF program header table")
    interval = None
    if symbol:
        if shsize != 64 or shoff + shsize * shnum > len(data):
            raise ValueError("Missing or malformed symbol table")
        sections = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + shsize * i) for i in range(shnum)]
        matches = []
        for section in sections:
            if section[1] != 2:
                continue
            if section[9] != 24 or section[6] >= len(sections) or section[4] + section[5] > len(data):
                raise ValueError("Malformed symbol table")
            strings = sections[section[6]]
            names = data[strings[4]:strings[4] + strings[5]]
            for pos in range(section[4], section[4] + section[5], 24):
                name, info, _, _, address, size = struct.unpack_from("<IBBHQQ", data, pos)
                if names[name:].split(b"\0", 1)[0].decode("utf-8", errors="replace") == symbol and info & 15 == 2:
                    matches.append((address, address + size))
        if len(matches) != 1 or matches[0][0] == matches[0][1]:
            raise ValueError(f"Expected one nonempty function symbol {symbol!r}")
        interval = matches[0]
    nodes = []
    for i in range(phnum):
        kind, flags, offset, address, _, filesz, memsz, _ = struct.unpack_from("<IIQQQQQQ", data, phoff + phsize * i)
        if kind in (2, 3):
            raise ValueError("Dynamic executables are unsupported")
        if kind != 1:
            continue
        if filesz > memsz or offset + filesz > len(data) or address + memsz > 1 << 64:
            raise ValueError("Invalid load segment")
        if not flags & 1:
            continue
        start, end = address, address + filesz
        if interval:
            start, end = max(start, interval[0]), min(end, interval[1])
        if start >= end:
            continue
        if start % 4 or end % 4:
            raise ValueError("Executable range must contain whole aligned 32-bit instructions")
        nodes.extend(decode(pc, struct.unpack_from("<I", data, offset + pc - address)[0])
                     for pc in range(start, end, 4))
    if not nodes or len({node.address for node in nodes}) != len(nodes):
        raise ValueError("Empty or overlapping executable ranges")
    if interval and [n.address for n in nodes] != list(range(*interval, 4)):
        raise ValueError("Function is not fully backed by executable file bytes")
    return entry, sorted(nodes, key=lambda node: node.address)


def lean_module(name: str) -> str:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", name):
        raise ValueError("Expected a Lean module name, e.g. Riscvc.Binary.Choose")
    return name


def certificate_source(data: bytes, entry: int, nodes: list[Instruction], proof_module: str | None = None,
                       start: int | None = None, imports: list[str] | None = None) -> str:
    imports = list(dict.fromkeys([*(imports or []), *([proof_module] if proof_module else [])]))
    lines = ["import Riscvc.Binary.Lifted", "import Riscvc.Examples", "import Riscvc.RecursiveExamples"]
    lines += [f"import {lean_module(module)}" for module in imports]
    lines += ["",
             "set_option maxRecDepth 100000", "set_option maxHeartbeats 16000000",
             "set_option backward.isDefEq.respectTransparency false",
             "set_option linter.unusedSimpArgs false", "namespace LiftedBinary",
             "open Riscvc Riscvc.Binary Riscvc.Binary.Lifted Riscvc.Binary.SailProofs",
             "open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions", "",
             f"-- Complete input ELF SHA-256: {hashlib.sha256(data).hexdigest()}",
             "def bytes : ELF.Bytes := #["]
    lines += ["  " + ", ".join(str(x) for x in data[i:i + 32]) + ("," if i + 32 < len(data) else "")
              for i in range(0, len(data), 32)]
    lines += ["]", "def image : ELF.Image := (ELF.parse bytes).getD ⟨#[], 0, []⟩",
              "theorem parsed : ELF.parse bytes = some image := by rfl",
              f"theorem entry : image.entry = 0x{entry:x} := by decide",
              f"def start : Word := 0x{entry if start is None else start:x}", ""]
    for i, node in enumerate(nodes):
        lines += [f"def node{i} : Node := ⟨0x{node.address:x}, 0x{node.word:08x}, {node.sail}⟩",
                  f"theorem node{i}_valid : node{i}.Valid image := by",
                  "  constructor", "  · decide", "  · intro s hs", "    obtain ⟨hp, hc, hm⟩ := hs",
                  f"    simp [node{i}, encdec_backwards, currentlyEnabled, get_xLPE, hartSupports,",
                  "      readReg, PreSail.readReg, get, getThe, MonadStateOf.get,",
                  "      EStateM.get, bind, EStateM.bind, pure, EStateM.pure, hp, hc, hm]",
                  "    rfl", ""]
    lines += ["def program : Program := [" + ", ".join(f"node{i}" for i in range(len(nodes))) + "]",
              "theorem certified : Certified image program := by", "  intro node hn",
              "  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hn",
              "  rcases hn with " + " | ".join("rfl" for _ in nodes)]
    lines += [f"  · exact node{i}_valid" for i in range(len(nodes))]
    lines += ["", "theorem execution_correct (n : Nat) (s after : SailState)",
              "    (h : Lifted.run program n s = .ok () after) :",
              "    Binary.run image n s = .ok () after := Lifted.run_correct certified n h",
              "#print axioms parsed", "#print axioms certified", "#print axioms execution_correct"]
    if proof_module:
        lines += ["", "-- Import a checked contract and bind it to the actual lifted program:",
                  f"def contract : Contract := {proof_module}.contract",
                  "theorem program_matches : program = contract.program := by rfl",
                  "theorem ir_correct : Hoare program contract.pre contract.post := by",
                  "  rw [program_matches]",
                  "  exact contract.correct",
                  "theorem equivalent : BinaryHoare image contract.pre contract.post :=",
                  "  Lifted.transfer certified ir_correct",
                  "#print axioms equivalent"]
    lines += ["end LiftedBinary", ""]
    return "\n".join(lines)


def audit(output: str) -> None:
    audits = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    if not audits:
        raise RuntimeError(f"Missing axiom audit:\n{output}")
    for audit_text in audits:
        axioms = {name.strip() for name in audit_text.split(",") if name.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected proof axioms: {axioms - ALLOWED_AXIOMS}")


def pointer_flags(tool: str) -> list[str]:
    """LLVM 14 needs an explicit switch for the opaque-pointer IR we emit."""
    version = run([tool, "--version"])
    match = re.search(r"version\s+(\d+)", version)
    if match is None or int(match.group(1)) < 14:
        raise ValueError(f"LLVM 14 or newer is required: {tool}")
    if int(match.group(1)) == 14:
        return ["-mllvm", "-opaque-pointers"] if "clang" in Path(tool).name else ["-opaque-pointers"]
    return []


def build_example(name: str, directory: Path, optimize: bool = True) -> Path:
    source, optimized, obj, elf = [directory / f"{name}{suffix}" for suffix in (".ll", ".opt.ll", ".o", ".elf")]
    source.write_text(run(["lake", "exe", "riscvc", "--llvm", name]))
    run(["opt", *pointer_flags("opt"), "-S", f"-passes=default<{'O2' if optimize else 'O0'}>", "-verify-each", str(source), "-o", str(optimized)])
    run(["llc", *pointer_flags("llc"), "-mtriple=riscv64-unknown-elf", "-target-abi=lp64", "-O=2" if optimize else "-O=0",
         "-filetype=obj", str(optimized), "-o", str(obj)])
    run(["ld.lld", "-m", "elf64lriscv", "--no-relax", f"--entry={name}", "-Ttext=0x80000000", str(obj), "-o", str(elf)])
    (directory / f"{name}.disasm").write_text(run(["llvm-objdump", "-d", str(elf)]))
    return elf


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--elf", type=Path)
    source.add_argument("--example", help="build one of the existing DSL examples with LLVM")
    parser.add_argument("--symbol", help="lift only this function symbol; default: all executable segments")
    parser.add_argument("--output", type=Path, default=ROOT / "build/lifted")
    parser.add_argument("--proof-module", type=lean_module,
                        help="Lean module exporting contract : Riscvc.Binary.Lifted.Contract")
    parser.add_argument("--import", dest="imports", type=lean_module, action="append", default=[],
                        help="additional Lean specification module to build/import (repeatable)")
    parser.add_argument("--no-opt", action="store_true", help="disable LLVM optimization when building an example")
    args = parser.parse_args()
    directory = args.output.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    print("Building the reusable Sail lifting proof...", flush=True)
    modules = [*args.imports, *([args.proof_module] if args.proof_module else [])]
    run(["lake", "build", "riscvc", "Riscvc.Binary.Lifted", *modules])
    elf = args.elf.resolve() if args.elf else build_example(args.example, directory, not args.no_opt)
    data = elf.read_bytes()
    if len(data) > 1024 * 1024:
        raise ValueError("Certificate input size limit: 1 MiB")
    entry, nodes = read_elf(data, args.symbol)
    start = nodes[0].address if args.symbol else entry
    manifest = {"format": "riscvc-lifted-v1", "elf": str(elf), "sha256": hashlib.sha256(data).hexdigest(),
                "entry": entry, "start": start, "symbol": args.symbol, "nodes": [asdict(n) for n in nodes]}
    (directory / "program.json").write_text(json.dumps(manifest, indent=2) + "\n")
    certificate = directory / "Lifted.lean"
    certificate.write_text(certificate_source(data, entry, nodes, args.proof_module, start, args.imports))
    print(f"Checking {len(nodes)} decoded instructions against ELF bytes and Sail...", flush=True)
    result = run(["lake", "env", "lean", "--tstack=131072", str(certificate)])
    audit(result)
    if elf.read_bytes() != data:
        raise RuntimeError("ELF changed during certificate checking")
    (directory / "Lifted.axioms.txt").write_text(result)
    print(f"Certified lifting: {certificate}\nInput SHA-256: {manifest['sha256']}")
    if args.proof_module:
        print("Checked source-contract theorem: LiftedBinary.equivalent")
    else:
        print("Lifting is certified; no source-equivalence theorem was requested.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, RuntimeError, OSError, struct.error, subprocess.TimeoutExpired) as error:
        print(f"Lifting failed: {error}", file=sys.stderr)
        sys.exit(1)
