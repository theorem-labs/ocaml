/* extract_shim.h — cpp shim for extract_handlers.sh.
   Redefines interp.c's dispatch macros so each Instruct/Next pair becomes a
   standalone C function that clightgen can process. Preprocess the input
   with `sed 's/Instruct(\([A-Z0-9_]*\)):/Instruct(\1)/g'` first so that
   the trailing colon of `Instruct(X):` is stripped (otherwise it survives
   cpp and lands inside the function body as a syntax error).

   The caller is expected to prepend `int __head(struct interp_state *s) {`
   and append `return STATUS_STEP; }` so that the first Instruct macro has
   a function to close and the last handler closes cleanly. */

/* Close the current function and open `int instr_X(...) {` for the next one.
   `Instruct(X)` without a trailing colon is safe: after expansion nothing
   follows at that source position until the handler body begins. */
#define Instruct(X) \
    return STATUS_STEP; \
    } \
    int instr_##X(struct interp_state *s) {

/* Empty: each `Instruct(X)` already injects `return STATUS_STEP; }` to
   close the previous function. Making `Next` empty avoids a double-return
   and keeps the handler body byte-identical to the old sed extractor's. */
#define Next

/* GC / C-call / debugger boundaries: erase. The Rocq model treats these
   as no-ops (allocation goes through heap_alloc, signals are abstract). */
#define Setup_for_gc
#define Restore_after_gc
#define Setup_for_c_call
#define Restore_after_c_call
#define Setup_for_event
#define Restore_after_event
#define Setup_for_debugger
#define Restore_after_debugger
#define Check_trap_barrier
#define Restart_curr_instr return STATUS_STEP

/* Allocation: route through the model's heap_alloc. */
#define Alloc_small(x, n, t) (x) = heap_alloc(s, (n), (t))
#define Alloc_small_origin

/* Write-barrier and major-heap allocation: our model uses direct stores
   and routes all allocation through heap_alloc (no minor/major split). */
#define caml_modify(fp, val) (*(fp) = (val))
#define caml_initialize(fp, val) (*(fp) = (val))
#define caml_alloc_shr(n, t) heap_alloc(s, (n), (t))

/* Runtime assertion macros: erase. Our model doesn't carry their checks. */
#define CAMLassert(x)

/* Signal/event handling: erase. Our model abstracts signals. */
#define caml_something_to_do 0
#define caml_process_pending_actions()

/* Backtrace machinery: erase. Our model skips backtraces. */
#define Caml_state_backtrace_active 0
#define caml_stash_backtrace(a, b, c)

/* Caml_state access. The input is pre-rewritten so Caml_state->trapsp
   becomes Caml_state_trapsp (a bare identifier cpp can expand). */
#define Caml_state_trapsp (s->trap_sp)
#define caml_global_data (s->global_data)

/* Register-variable aliases so handler bodies referencing the interp.c
   register locals project into the struct. interp.c never writes `s->sp`
   etc., so cpp's no-recursion rule isn't needed here. */
#define accu (s->accu)
#define sp (s->sp)
#define pc (s->pc)
#define env (s->env)
#define extra_args (s->extra_args)

/* Integer comparison family: expand to a full Instruct handler.
   Source: `Integer_comparison(typ, opname, tst)` on a line by itself. */
#define Integer_comparison(typ, opname, tst) \
    Instruct(opname) \
    accu = Val_int((typ) accu tst (typ) *sp++); \
    Next;

#define Integer_branch_comparison(typ, opname, tst, debug) \
    Instruct(opname) \
    if ((typ) *pc++ tst (typ) Long_val(accu)) { \
        pc += *pc; \
    } else { \
        pc++; \
    } \
    Next;
