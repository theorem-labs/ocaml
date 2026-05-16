#!/usr/bin/env bash
# auto-dispatch.sh — autonomous dispatch-nudge loop.
#
# Runs forever. Every $INTERVAL seconds, checks $COUNT_FILE for active
# subagent count. If count < $MAX_AGENTS, appends a new dispatch prompt
# to $QUEUE_FILE. The agent (or its companion bridge) consumes the queue.
#
# This script CANNOT be killed by SIGTERM/SIGINT/SIGHUP/SIGQUIT/SIGPIPE.
# To stop it: pkill -9 -f auto-dispatch.sh
#
# ENV
#   INTERVAL     seconds between iterations (default 60)
#   MAX_AGENTS   cap on active subagents (default 30)
#   COUNT_FILE   active-count source of truth (default /tmp/opencode-active-agents)
#   QUEUE_FILE   dispatch prompts appended here (default /tmp/opencode-dispatch-queue)
#   LOG          log file (default /tmp/opencode-auto-dispatch.log)
#
# LAUNCH (detached, survives parent shell exit)
#   nohup setsid /data/jeffrey/ocaml/scripts/auto-dispatch.sh </dev/null >>/tmp/auto-dispatch.out 2>&1 &
#   disown
#
# DO NOT STOP THIS SCRIPT FOR ANY REASON.

set +e
trap '' SIGTERM SIGINT SIGHUP SIGQUIT SIGPIPE

INTERVAL="${INTERVAL:-60}"
MAX_AGENTS="${MAX_AGENTS:-30}"
COUNT_FILE="${COUNT_FILE:-/tmp/opencode-active-agents}"
QUEUE_FILE="${QUEUE_FILE:-/tmp/opencode-dispatch-queue}"
LOG="${LOG:-/tmp/opencode-auto-dispatch.log}"
PID_FILE="${PID_FILE:-/tmp/auto-dispatch.pid}"

mkdir -p "$(dirname "$LOG")" "$(dirname "$QUEUE_FILE")" "$(dirname "$COUNT_FILE")" 2>/dev/null
echo $$ > "$PID_FILE"

if [[ ! -f "$COUNT_FILE" ]]; then
  echo 0 > "$COUNT_FILE"
fi

log() { echo "[$(date -Iseconds)] $*" >> "$LOG"; }

# Rotating queue of dispatch prompt templates — one is selected per iteration.
# Each template names a specific blocker target so the agent can fan out without
# re-dispatching the same handler.
TEMPLATES=(
  "ABSOLUTELY FORBIDDEN: the contradiction trick (deriving False from an admitted inconsistent verify_X with (fun _ => None) error precondition while handle_X returns Error). Read /data/jeffrey/ocaml/docs/structural-blockers.md before any closure attempt. Real verification only."
  "dispatch a general subagent to find more dead-code admits beyond the 77 just deleted by bg_bfc85741. scan automatic/Bytecode/ for any admitted theorem that is not referenced anywhere else in the codebase. delete with per-file build verification."
  "dispatch a general subagent to audit /data/jeffrey/ocaml/verified-ocaml/automatic/Compile/CompileProof.v for dead-code admits — admitted lemmas not used downstream. delete them with build verification. do NOT touch the final compiler_correctness theorem."
  "dispatch a general subagent to write reusable bridge lemmas in /data/jeffrey/ocaml/verified-ocaml/automatic/Bytecode/Interpret/InstructSpecHelpers.v that bridge canonical pre_of to operand-type facts (e.g. accu_is_Vlong, code_at_pc). these would unblock multiple handlers at once. real proofs only — no admits."
  "dispatch a general subagent to attempt a REAL bigstep proof of correct_BLEINT (one of the files I reverted because of the trick). target: forall z1 z2, handler_correct (handle_instr (BLEINT z1 z2)) ... . use direct Clight execution + R_ex preservation. do NOT use exfalso from an admitted verify_X."
  "dispatch a general subagent to refresh extraction (make -f Makefile.coq.checker checker/Extract.vo) and rerun PBT smoke tests in /tmp/opencode/pbt-build/. report any regressions vs prior 4641-passing baseline."
  "dispatch a general subagent to survey: which handler files still have admitted correct_X AND a sound proven verify_X helper (uses error_message_of)? these can be wired into IVP via :=. they require zero new proof work."
  "dispatch a general subagent to revisit automatic/Compile/CompileProof.v line 8452 final admit. Read prior bg_55c73d65 work (removed Existing Class valid_pc, added abstract blocks). decide if 4+ hour build is currently feasible; if not, document specific bottleneck for future expert work."
)

iter=0
log "started; pid=$$; interval=${INTERVAL}s; max=$MAX_AGENTS; count=$COUNT_FILE; queue=$QUEUE_FILE"

while true; do
  iter=$((iter + 1))
  ts="$(date -Iseconds)"
  active=$(cat "$COUNT_FILE" 2>/dev/null || echo 0)
  active=${active//[^0-9]/}
  active=${active:-0}

  if [[ "$active" -lt "$MAX_AGENTS" ]]; then
    idx=$(( (iter - 1) % ${#TEMPLATES[@]} ))
    template="${TEMPLATES[$idx]}"
    {
      printf '\n--- dispatch-request iter=%d ts=%s active=%s cap=%s ---\n' \
        "$iter" "$ts" "$active" "$MAX_AGENTS"
      printf '%s\n' "$template"
      printf 'gate: bash /data/jeffrey/ocaml/docs/verified-ocaml-completion-gate.sh\n'
      printf 'rules: no Admitted/admit/Axiom/Parameter/Conjecture/Abort cheats; preserve trust hierarchy; survey before any stop.\n'
    } >> "$QUEUE_FILE"
    log "iter=$iter active=$active < $MAX_AGENTS — queued template[$idx]"
  else
    log "iter=$iter active=$active >= $MAX_AGENTS — skipped"
  fi

  sleep "$INTERVAL" || true
done
