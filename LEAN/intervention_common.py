"""Shared plumbing for the two intervention experiments.

Neither experiment touches stages_real_scenario/: each row is copied into
runs/<plan>/<id>/ and every artifact is written there.
"""

from __future__ import annotations

import json
import re
import shutil
from pathlib import Path

from nli.compare import compare as compare_nli
from pipeline import PipelineError, ROOT, Settings, load_vocabulary

VOCAB = {"CH": "choking", "CPR": "cpr", "DR": "drowning"}
SOURCE = ROOT / "stages_real_scenario"


def stages() -> list[str]:
    return sorted(d.name for d in SOURCE.iterdir() if d.is_dir())


def workspace(plan: str, ident: str) -> Path:
    work = ROOT / "runs" / plan / ident
    if work.exists():
        shutil.rmtree(work)
    work.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(SOURCE / ident, work)
    return work


SNAPSHOT = ("x.txt", "x0.txt", "YOriginal.lean", "x_prime.txt", "YPrime.lean",
            "Equivalence.lean")


def snapshot(work: Path, step: int) -> Path:
    """Freeze this iteration's artifacts: the next pass overwrites them in place."""
    into = work / f"step-{step:02d}"
    into.mkdir(exist_ok=True)
    for name in SNAPSHOT:
        source = work / name
        if source.exists():
            shutil.copy2(source, into / name)
    return into


def finish(work: Path, stop: str, trace: list[dict]) -> None:
    """One human-readable outcome file per row, beside the step folders."""
    lines = [f"stopped_because : {stop}",
             f"iterations      : {len(trace) - 1}",
             f"converged       : {str(not trace[-1]['drift']).lower()}",
             f"fields          : {trace[0]['n_fields']} -> {trace[-1]['n_fields']}",
             ""]
    for step, t in enumerate(trace):
        lines.append(f"step {step:>2}  fields={t['n_fields']:<3} {t['category']:<14} "
                     f"drift={str(t['drift']).lower():<5} equivalent={str(t['equivalent']).lower()}")
    (work / "outcome.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")


def vocabulary_for(ident: str):
    return load_vocabulary(ROOT / "vocab_real_scenario" / f"{VOCAB[ident.rpartition('-')[0]]}.lean")


def nli(x: str, x_prime: str, settings: Settings) -> dict:
    """Category, drift, and the three scores the decision tree turns on."""
    result = compare_nli(x.strip(), x_prime.strip(), settings.nli_model)
    if result.get("drift") is None:
        raise PipelineError(f"NLI did not return a drift verdict: {result.get('note', 'unknown error')}")
    forward, backward = result.get("forward", {}), result.get("backward", {})
    return {
        "category": result.get("category"),
        "drift": result["drift"],
        "e_fwd": float(forward.get("entailment", 0.0)),
        "e_bwd": float(backward.get("entailment", 0.0)),
        "c_max": max(float(forward.get("contradiction", 0.0)),
                     float(backward.get("contradiction", 0.0))),
    }


def rule_body(source: str) -> str:
    """The `def rule` lines of a module, without the import/namespace wrapper."""
    keep = [line for line in source.splitlines()
            if line.strip() and not line.startswith(("import", "namespace", "end", "example"))]
    return "\n".join(keep).strip()


def fields(rule: str) -> int:
    """Distinct Ctx fields the rule constrains, not `c.` occurrences: a rule that
    repeats a conjunct is not a rule that says more."""
    return len(set(re.findall(r"c\.(\w+)", rule)))


class Log:
    """One JSONL line per iteration, one per row. Nothing derivable is stored:
    every summary a report needs can be computed from the iteration lines."""

    def __init__(self, plan: str) -> None:
        self.path = ROOT / "runs" / f"{plan}.jsonl"
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text("", encoding="utf-8")

    def write(self, record: dict) -> None:
        with self.path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")

    def iteration(self, ident: str, step: int, rule: str, x_prime: str,
                  measure: dict, equivalent: bool, **extra) -> None:
        self.write({"kind": "iteration", "id": ident, "step": step, "rule": rule,
                    "x_prime": x_prime, "equivalent": equivalent,
                    "n_fields": fields(rule), **measure, **extra})
        print(f"  [{ident} step {step}] fields={fields(rule):<2} "
              f"{measure['category']:<14} drift={str(measure['drift']).lower():<5} "
              f"e_fwd={measure['e_fwd']:.2f} e_bwd={measure['e_bwd']:.2f} eq={equivalent}")

    def row(self, ident: str, trace: list[dict], **extra) -> None:
        self.write({"kind": "row", "id": ident, "iterations": len(trace) - 1, **extra})
        first, last = trace[0], trace[-1]
        print(f"  -> {ident}: {'converged' if not last['drift'] else 'NOT converged'} "
              f"in {len(trace) - 1} iterations, fields {first['n_fields']}->{last['n_fields']}")
