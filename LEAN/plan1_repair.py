"""Plan 1: diagnose and repair a drifting translation chain.

The initial S1 -> S2 -> S3 translation is generated without an earlier equivalence-
driven repair pass. If x and the S2 readback drift, one LLM call receives exactly x,
S1, S2 and the fixed vocabulary and chooses the faulty stage. That stage is repaired,
all following stages are regenerated, and drift is measured again. Each row has at
most six repair iterations. Invalid diagnoses and empty repairs are retried and do
not consume an iteration.

    python plan1_repair.py [--only CPR-006 ...] [--repair-temp 0.7]
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import replace

from intervention_common import (
    Log, fields, finish, nli, rule_body, snapshot, stages, vocabulary_for, workspace)
from pipeline import (
    LLM, Diagnosis, PipelineError, Settings, State,
    check_equivalence, lean_available, repair, run)

PLAN = "plan1"
MAX_REPAIR_ITERATIONS = 6

DIAGNOSE_SYSTEM = """A semantic drift detector found that x and the S2 readback do
not say the same thing. Self-check the two-stage translation and identify whether S1
or S2 introduced the mismatch.

S1 translates x into a Lean rule. S2 translates that Lean rule back into ordinary
language. Treat x as fixed. Check for anything added, omitted, weakened, reversed or
otherwise changed. The vocabulary is closed, so a repair may use only its fields.

Choose exactly one stage whose output must be repaired. Reply with exactly:
STAGE: S1|S2
ROOT_CAUSE: ...
SCOPED_FIX_HINT: ..."""


def stage_diagnose(client: LLM, settings: Settings, x: str,
                   state: State) -> tuple[Diagnosis | None, str]:
    """Give one LLM the four requested inputs and let it diagnose S1 versus S2."""
    prompt = f"""x:
{x.strip()}

S1:
```lean
{state.original_rule.strip()}
```

S2:
{state.reconstructed.strip()}

vocabulary:
```lean
{state.vocabulary.source.strip()}
```"""
    reply = client.complete(
        DIAGNOSE_SYSTEM,
        prompt,
        temperature=settings.judge_temperature,
        max_tokens=settings.max_tokens,
        model=settings.judge_model or settings.model,
    )
    parsed = {}
    for line in reply.splitlines():
        key, separator, value = line.partition(":")
        if separator:
            parsed[key.strip().upper()] = value.strip()
    stage = parsed.get("STAGE", "").upper()
    if stage not in {"S1", "S2"}:
        return None, reply
    return Diagnosis(
        stage,
        parsed.get("ROOT_CAUSE", ""),
        parsed.get("SCOPED_FIX_HINT", ""),
        1.0,
    ), reply


def initial_state(x: str, vocabulary, work, settings: Settings,
                  client: LLM) -> State:
    """Generate a complete baseline without the pipeline's equivalence repair loop."""
    baseline_settings = replace(settings, max_rounds=0)
    artifacts = ("YOriginal.lean", "x_prime.txt", "YPrime.lean")
    # The workspace starts as a copy of a previous run. Remove its derived files so
    # a failed fresh pass can never be mistaken for a complete baseline.
    for name in artifacts:
        (work / name).unlink(missing_ok=True)
    run(x, vocabulary, work, baseline_settings, client)
    missing = [name for name in artifacts if not (work / name).exists()]
    if missing:
        raise PipelineError(f"initial translation did not produce: {', '.join(missing)}")
    return State(
        original_rule=(work / "YOriginal.lean").read_text(encoding="utf-8"),
        reconstructed=(work / "x_prime.txt").read_text(encoding="utf-8").strip(),
        prime_rule=(work / "YPrime.lean").read_text(encoding="utf-8"),
        vocabulary=vocabulary,
    )


def one_row(ident: str, settings: Settings, repair_settings: Settings,
            client: LLM, log: Log) -> None:
    work = workspace(PLAN, ident)
    vocabulary = vocabulary_for(ident)
    x = (work / "x.txt").read_text(encoding="utf-8").strip()
    print(f"\n{ident}: {x}")

    state = initial_state(x, vocabulary, work, settings, client)

    trace = []
    stop = ""
    for step in range(MAX_REPAIR_ITERATIONS + 1):
        measure = nli(x, state.reconstructed, settings)
        equivalent, _ = check_equivalence(work, settings.lean_timeout)
        rule = rule_body(state.original_rule)
        log.iteration(ident, step, rule, state.reconstructed, measure, equivalent)
        trace.append({**measure, "n_fields": fields(rule), "equivalent": equivalent})
        snapshot(work, step)

        if measure["drift"] is False:
            stop = "no drift"
            break
        if step == MAX_REPAIR_ITERATIONS:
            stop = f"drift after {MAX_REPAIR_ITERATIONS} repair iterations"
            break

        while True:
            diagnosis, reply = stage_diagnose(client, settings, x, state)
            log.write({"kind": "diagnosis", "id": ident, "step": step,
                       "reply": reply,
                       "chosen": diagnosis.stage if diagnosis else None})
            if diagnosis is not None:
                break
            print("     diagnosis did not choose S1 or S2; rerunning")

        print(f"       diagnose: {diagnosis.stage}  {diagnosis.reason[:110]}")
        updated = None
        while updated is None:
            updated = repair(
                client, repair_settings, x, state, diagnosis, work
            )
            if updated is None:
                print(f"     {diagnosis.stage} repair returned empty; rerunning")
        state = updated

    finish(work, stop, trace)
    log.row(ident, trace, stopped_because=stop)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", nargs="+", default=[])
    parser.add_argument("--repair-temp", type=float, default=0.7,
                        help="temperature for the repair call; the pipeline keeps its own")
    arguments = parser.parse_args()

    if not lean_available():
        print("Lean is not available", file=sys.stderr)
        return 2
    settings = Settings()
    repair_settings = replace(settings, temperature=arguments.repair_temp)
    try:
        client = LLM(settings.model)
    except PipelineError as error:
        print(str(error), file=sys.stderr)
        return 2

    log = Log(PLAN)
    for ident in (arguments.only or stages()):
        try:
            one_row(ident, settings, repair_settings, client, log)
        except PipelineError as error:
            print(f"  [{ident}] FAILED: {error}")
    print(f"\nlog: {log.path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
