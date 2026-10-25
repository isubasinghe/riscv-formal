import Riscvc

namespace Riscvc.Examples

def sum : Expr 2 := [riscv| fun x y => x + y]

/-- A natural-number specification needs an explicit no-overflow premise. -/
theorem sum_noOverflow (x y : Word) (h : x.toNat + y.toNat < 2^64) :
    (sum.eval (Env.two x y)).toNat = x.toNat + y.toNat := by
  change (x + y).toNat = _
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

def roundTrip : Expr 2 := [riscv| fun x y =>
  let sum := x + y;
  sum - y
]

/-- This holds even when the addition overflows. -/
theorem roundTrip_correct (x y : Word) : roundTrip.eval (Env.two x y) = x := by
  change x + y - y = x
  exact BitVec.add_sub_cancel x y

theorem roundTrip_compiled (x y : Word) : execute roundTrip (Env.two x y) = x := by
  rw [execute_correct]
  exact roundTrip_correct x y

def maxUnsigned : Expr 2 := [riscv| fun x y =>
  if x < y then y else x
]

theorem maxUnsigned_correct (x y : Word) :
    (maxUnsigned.eval (Env.two x y)).toNat = max x.toNat y.toNat := by
  change (if (if x.ult y then (1 : Word) else 0) = 0 then x else y).toNat = _
  by_cases h : x.toNat < y.toNat
  · simp [BitVec.ult, h, Nat.max_eq_right (by omega : x.toNat ≤ y.toNat)]
  · simp [BitVec.ult, h, Nat.max_eq_left (by omega : y.toNat ≤ x.toNat)]

def choose : Expr 3 := [riscv| fun flag x y => if flag then x else y]

theorem choose_zero (x y : Word) : choose.eval (Env.three 0 x y) = y := rfl

def lowByte : Expr 1 := [riscv| fun x => x & 255]

theorem lowByte_idempotent (x : Word) :
    lowByte.eval (Env.one (lowByte.eval (Env.one x))) = lowByte.eval (Env.one x) := by
  change (x &&& 255#64) &&& 255#64 = x &&& 255#64
  rw [BitVec.and_assoc, BitVec.and_self]

def rotateLeft : Expr 2 := [riscv| fun x amount =>
  (x << amount) | (x >> (64 - amount))
]

def xorCancel : Expr 2 := [riscv| fun x key =>
  let encrypted := x ^ key;
  encrypted ^ key
]

theorem xorCancel_correct (x key : Word) : xorCancel.eval (Env.two x key) = x := by
  change (x ^^^ key) ^^^ key = x
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

def shadow : Expr 2 := [riscv| fun x y =>
  let x := x + y;
  let y := x ^ y;
  x - y
]

def allOnes : Expr 0 := [riscv| fun => 0xffffffffffffffff]

def nested : Expr 3 := [riscv| fun x y z =>
  let m := if x < y then y else x;
  if m < z then z else m
]

def registerEdge : Expr 8 := [riscv| fun a b c d e f g h =>
  h + (g + (f + (e + (d + (c + b)))))
]

/-- A packaged example retains its arity for both the emitter and evaluator. -/
structure Example where
  name : String
  arity : Nat
  program : Expr arity

def examples : List Example := [
  ⟨"sum", 2, sum⟩,
  ⟨"round_trip", 2, roundTrip⟩,
  ⟨"max_unsigned", 2, maxUnsigned⟩,
  ⟨"choose", 3, choose⟩,
  ⟨"low_byte", 1, lowByte⟩,
  ⟨"rotate_left", 2, rotateLeft⟩,
  ⟨"xor_cancel", 2, xorCancel⟩,
  ⟨"shadow", 2, shadow⟩,
  ⟨"all_ones", 0, allOnes⟩,
  ⟨"nested", 3, nested⟩,
  ⟨"register_edge", 8, registerEdge⟩
]

end Riscvc.Examples
