/* Storage and terminal I/O for examples/Scheduler.lean.
 * All process creation, removal, scheduling and slot recycling run in DSL code. */
#include <errno.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef struct Process {
    uint64_t pid, remaining;
    struct Process *next;
} Process;

typedef struct {
    Process *head, *tail, *free;
    uint64_t count, ticks, last_pid;
} Scheduler;

_Static_assert(sizeof(Process) == 24 && offsetof(Process, next) == 16,
               "The DSL requires 64-bit pointers and eight-byte fields");
_Static_assert(sizeof(Scheduler) == 48 && offsetof(Scheduler, count) == 24,
               "Scheduler layout must match Scheduler.lean");

extern uint64_t scheduler_init(Scheduler *, Process *);
extern uint64_t scheduler_step(Scheduler *, uint64_t, uint64_t, uint64_t);

static int word(const char *text, uint64_t *value) {
    if (!text || !*text || strspn(text, "0123456789") != strlen(text)) return 0;
    errno = 0;
    char *end;
    uintmax_t n = strtoumax(text, &end, 10);
    if (errno || *end || n > UINT64_MAX) return 0;
    *value = (uint64_t)n;
    return 1;
}

static void show(const Scheduler *state) {
    printf("ready:");
    for (const Process *p = state->head; p; p = p->next)
        printf(" %" PRIu64 "(%" PRIu64 ")%s", p->pid, p->remaining,
               p->next ? " ->" : "");
    if (!state->head) printf(" empty");
    printf(" | processes=%" PRIu64 " ticks=%" PRIu64 "\n", state->count, state->ticks);
}

static void help(void) {
    puts("add PID TICKS  add a process (both numbers must be positive)\n"
         "remove PID     cancel a queued process\n"
         "tick [N]       run N time slices (default 1)\n"
         "list           show PID(remaining ticks) in queue order\n"
         "help | quit");
}

static uint64_t execute(Scheduler *state, uint64_t op, uint64_t pid, uint64_t work) {
    static const char *errors[] = {
        "", "invalid command or arguments", "PID already exists", "process pool is full",
        "PID not found", "scheduler is idle"
    };
    uint64_t status = scheduler_step(state, op, pid, work);
    if (status) {
        printf("error: %s\n", status < 6 ? errors[status] : "unknown scheduler status");
    } else if (op == 1) {
        printf("added %" PRIu64 "\n", pid);
    } else if (op == 2) {
        printf("removed %" PRIu64 "\n", pid);
    } else {
        printf("ran %" PRIu64 "\n", state->last_pid);
    }
    return status;
}

static int command(Scheduler *state, char *line) {
    char *args[4];
    size_t count = 0;
    for (char *s = strtok(line, " \t\r\n"); s; s = strtok(NULL, " \t\r\n")) {
        if (count == 4) break;
        args[count++] = s;
    }
    if (!count) return 1;
    uint64_t pid, work;
    if (count == 1 && !strcmp(args[0], "quit")) return 0;
    if (count == 1 && !strcmp(args[0], "help")) { help(); return 1; }
    if (count == 1 && !strcmp(args[0], "list")) { show(state); return 1; }
    if (count == 3 && !strcmp(args[0], "add") && word(args[1], &pid) && word(args[2], &work)) {
        execute(state, 1, pid, work);
    } else if (count == 2 && !strcmp(args[0], "remove") && word(args[1], &pid)) {
        execute(state, 2, pid, 0);
    } else if (!strcmp(args[0], "tick") &&
               (count == 1 || (count == 2 && word(args[1], &work) && work))) {
        if (count == 1) work = 1;
        for (uint64_t i = 0; i < work; ++i)
            if (execute(state, 3, 0, 0)) break;
    } else {
        puts("error: expected add PID TICKS, remove PID, tick [N], list, help, or quit");
        return 1;
    }
    show(state);
    return 1;
}

int main(int argc, char **argv) {
    uint64_t capacity = 8;
    int demo = 0;
    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--demo")) demo = 1;
        else if (!strcmp(argv[i], "--capacity") && i + 1 < argc &&
                 word(argv[++i], &capacity) && capacity && capacity <= 65536) {}
        else {
            fprintf(stderr, "usage: %s [--demo] [--capacity 1..65536]\n", argv[0]);
            return 2;
        }
    }
    Process *pool = calloc((size_t)capacity, sizeof(*pool));
    if (!pool) { perror("allocate process pool"); return 1; }
    for (uint64_t i = 0; i + 1 < capacity; ++i) pool[i].next = &pool[i + 1];
    Scheduler state;
    scheduler_init(&state, pool);
    printf("Round-robin scheduler (%" PRIu64 " process slots)\n", capacity);
    if (demo) {
        const char *commands[] = {
            "add 10 3", "add 20 2", "add 30 1", "tick", "remove 20",
            "add 40 2", "tick 4", "add 50 1", "tick 2", "list"
        };
        for (size_t i = 0; i < sizeof(commands) / sizeof(commands[0]); ++i) {
            char line[64];
            snprintf(line, sizeof(line), "%s", commands[i]);
            printf("> %s\n", line);
            command(&state, line);
        }
    } else {
        int interactive = isatty(STDIN_FILENO);
        if (interactive) help();
        char line[256];
        for (;;) {
            if (interactive) { printf("scheduler> "); fflush(stdout); }
            if (!fgets(line, sizeof(line), stdin)) break;
            if (!strchr(line, '\n') && !feof(stdin)) {
                int c;
                while ((c = getchar()) != '\n' && c != EOF) {}
                puts("error: command is too long");
                continue;
            }
            if (!command(&state, line)) break;
        }
    }
    free(pool);
    return 0;
}
