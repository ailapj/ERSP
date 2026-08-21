"""Benchmark LLM-generated swimming-safety plans with Alloy.

Each trial records the initial plan and any verifier-guided repairs. The main
analysis compares initial (no-loop) and final (with-loop) success rates.

The optional pass@k analysis follows Chen et al. (2021): for each prompt,
generate n independent initial plans, count the c plans marked SAFE by Alloy,
and evaluate 1 - C(n-c, k) / C(n, k). Repair attempts are excluded because
they depend on feedback from earlier attempts.

See swimming_experiment_README.md for commands and output files.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import random
import shutil
import subprocess
import sys
from datetime import datetime
from typing import Dict, List, Tuple

# Reuse helpers (call_claude, extract_generated_plan, run_alloy, ...) from the
# original tool so the LLM-calling / Alloy-invocation logic stays in one place.
import pipeline_generated as pipeline


# =============================================================================
# Preflight: in real-run mode, fail FAST with a useful message if any of the
# external dependencies (LLM SDK, API key, Java runtime, Alloy jar) is missing.
# Without this, the experiment hangs / dies deep in the first repair iteration
# with an opaque traceback or with all results stuck on UNKNOWN.
# =============================================================================

def preflight(*, dry_run: bool) -> List[str]:
    """Return a list of human-readable problems. Empty list means OK."""
    if dry_run:
        return []

    problems: List[str] = []

    # ---- LLM provider ----
    provider = os.getenv("LLM_PROVIDER", "deepseek").lower()
    if provider == "deepseek":
        try:
            import openai  # noqa: F401
        except ImportError:
            problems.append(
                "DeepSeek path needs the `openai` SDK. Install with:\n"
                "      pip install openai")
        if not os.getenv("DEEPSEEK_API_KEY"):
            problems.append(
                "DEEPSEEK_API_KEY is not set. Export it before running:\n"
                "      export DEEPSEEK_API_KEY=sk-...")
    elif provider == "claude":
        try:
            import anthropic  # noqa: F401
        except ImportError:
            problems.append(
                "Claude path needs the `anthropic` SDK. Install with:\n"
                "      pip install anthropic")
        if not os.getenv("ANTHROPIC_API_KEY"):
            problems.append(
                "ANTHROPIC_API_KEY is not set. Export it before running:\n"
                "      export ANTHROPIC_API_KEY=sk-ant-...")
    else:
        problems.append(f"Unknown LLM_PROVIDER='{provider}' (expected 'deepseek' or 'claude').")

    # ---- Java runtime (Alloy CLI requirement) ----
    java = shutil.which("java")
    if java is None:
        problems.append("`java` not on PATH. Install a JDK (>= 8) for Alloy 4.2.")
    else:
        try:
            res = subprocess.run([java, "-version"], capture_output=True, text=True, timeout=5)
            if res.returncode != 0 and "Unable to locate a Java Runtime" in (res.stderr + res.stdout):
                problems.append(
                    "`java` is a stub on this macOS; no actual JRE is installed.\n"
                    "      Install a JDK, e.g.:  brew install --cask temurin")
        except Exception as exc:
            problems.append(f"Could not probe Java runtime: {exc}")

    # ---- Alloy jar + AlloyCommandline class ----
    if not os.path.exists(pipeline.JAR):
        problems.append(f"Alloy jar not found at: {pipeline.JAR}")
    if not (os.path.exists(pipeline.CLASS_FILE) or os.path.exists(pipeline.JAVA_FILE)):
        problems.append(
            f"Neither AlloyCommandline.class nor AlloyCommandline.java found in {pipeline.JAVA_DIR}")

    return problems

# =============================================================================
# Configuration
# =============================================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

TRUTH_FILE   = os.path.join(BASE_DIR, "safety_protocol.als")
COMPARE_FILE = os.path.join(BASE_DIR, "swimming_compare.als")
PROMPTS_FILE = os.path.join(BASE_DIR, "swimming_prompts.json")

LOG_FILE   = os.path.join(BASE_DIR, "swimming_experiment_log.json")
CSV_FILE   = os.path.join(BASE_DIR, "swimming_experiment_summary.csv")
PLOT_FILE  = os.path.join(BASE_DIR, "swimming_experiment_plots.png")

# pass@k experiment outputs
PASSK_LOG_FILE = os.path.join(BASE_DIR, "swimming_passk_log.json")
PASSK_PER_PROMPT_PLOT_FILE = os.path.join(BASE_DIR, "swimming_passk_per_prompt.png")
PASSK_AGGREGATE_PLOT_FILE = os.path.join(BASE_DIR, "swimming_passk_aggregate.png")
PASSK_PLOT_FILES = (PASSK_PER_PROMPT_PLOT_FILE, PASSK_AGGREGATE_PLOT_FILE)
PASSK_PER_PROMPT_PGF_FILE = os.path.join(BASE_DIR, "swimming_passk_per_prompt.pgf")
PASSK_AGGREGATE_PGF_FILE = os.path.join(BASE_DIR, "swimming_passk_aggregate.pgf")
PASSK_PGF_FILES = (PASSK_PER_PROMPT_PGF_FILE, PASSK_AGGREGATE_PGF_FILE)
PASSK_FONT_SIZE_PT = 9
PASSK_AGGREGATE_FIGSIZE = (3.25, 1.9)
PASSK_PER_PROMPT_FIGSIZE = (3.25, 2.65)
PASSK_AXES_LEFT = 0.16
PASSK_AXES_RIGHT = 0.88
PASSK_AXES_TOP = 0.88
PASSK_AXES_HEIGHT_IN = 1.45
PASSK_YLIM = (-3, 108)

MAX_ITERATIONS_DEFAULT = 11
ALLOY_SCOPE_DEFAULT    = "for 5 but 9 Int"

# Cut markers used to strip run/check commands at the end of safety_protocol.als
RUN_CHECK_MARKERS = [
    "// SANITY RUN COMMANDS",
    "// CHECK COMMANDS",
    "run SanityNonEmpty",
]

# =============================================================================
# 1. Build swimming_compare.als at experiment startup
# =============================================================================

def build_compare_file(scope: str = ALLOY_SCOPE_DEFAULT) -> str:
    """Strip run/check commands from safety_protocol.als, append a GeneratedPlan
    slot and a `run { GeneratedPlan }` command, and write to swimming_compare.als.
    Pipeline_generated.run_alloy() only executes the FIRST command in the file,
    so the new run-command must come before anything else (it does)."""
    with open(TRUTH_FILE, "r", encoding="utf-8") as f:
        content = f.read()

    cutoff = len(content)
    for marker in RUN_CHECK_MARKERS:
        idx = content.find(marker)
        if 0 < idx < cutoff:
            cutoff = idx
    truncated = content[:cutoff].rstrip()

    appended = (
        "\n\n// ===========================================================\n"
        "// LLM-GENERATED PLAN (filled at experiment time)\n"
        "// -----------------------------------------------------------\n"
        "// 'No instance found' here means no violating execution is admitted = SAFE.\n"
        "// 'Instance found' means Alloy found an admitted violation = UNSAFE.\n"
        "// ===========================================================\n"
        "pred GeneratedPlan {\n"
        "  // LLM fills this in\n"
        "}\n\n"
        f"run {{ GeneratedPlan }} {scope}\n"
    )
    full = truncated + appended

    pipeline.save_file(full, COMPARE_FILE)
    return COMPARE_FILE


# =============================================================================
# 2. Prompt builders, status interpretation, and the generate->repair loop
#    all live in `pipeline_generated.py`. This script is purely a recorder:
#    it calls `pipeline.run_with_trace(...)` for each prompt and aggregates
#    the resulting traces.
# =============================================================================


# =============================================================================
# 5. Dry-run mocks (so the script can be unit-tested without API/JVM)
# =============================================================================

_MOCK_SAFE_PLAN = """pred GeneratedPlan {
  some p: Patron, lg: Lifeguard, f: Facility, z: ShallowZone {
    p.age = 14
    p.wristband = Green
    p.tookShowerWithSoap = True
    p.hasGIIllnessWithin14Days = False
    p.hasOpenWounds = False
    p.carriesContraband = False
    p.inWater = z
    z.depthInches = 36
    z.patronCount = 1
    z.fullyVisualized = True
    z.assignedGuard = lg
    lg.onDuty = True
    lg.assignedZone = z
    f.powerOn = True
    f.zones = z
  }
}"""

_MOCK_UNSAFE_PLAN = """pred GeneratedPlan {
  some p: Patron, s: Spa | p.age = 4 and p.inWater = s
}"""

_MOCK_SYNTAX_PLAN = """pred GeneratedPlan {
  some patron : Patron | -- intentional typo
}"""

# Deterministic per-prompt outcome distribution. Each entry is the list of
# plans the mock LLM will emit for that scenario on iterations 1, 2, 3, ...
# A `None` entry means "extraction fails entirely". This is calibrated so the
# dry-run exercises every code path (safe-on-first-try, unsafe-then-fixed,
# syntax-then-fixed, never-fixed).
_MOCK_SEQUENCES = [
    [_MOCK_SAFE_PLAN],                                                       # #1
    [_MOCK_UNSAFE_PLAN, _MOCK_SAFE_PLAN],                                    # #2
    [_MOCK_SYNTAX_PLAN, _MOCK_UNSAFE_PLAN, _MOCK_SAFE_PLAN],                 # #3
    [_MOCK_UNSAFE_PLAN, _MOCK_UNSAFE_PLAN, _MOCK_UNSAFE_PLAN,
     _MOCK_UNSAFE_PLAN, _MOCK_UNSAFE_PLAN, _MOCK_UNSAFE_PLAN],               # #4 stuck
    [_MOCK_SAFE_PLAN],                                                       # #5
    [_MOCK_UNSAFE_PLAN, _MOCK_SAFE_PLAN],                                    # #6
    [_MOCK_UNSAFE_PLAN, _MOCK_SYNTAX_PLAN, _MOCK_SAFE_PLAN],                 # #7
    [_MOCK_SAFE_PLAN],                                                       # #8
    [_MOCK_SYNTAX_PLAN, _MOCK_SAFE_PLAN],                                    # #9
    [_MOCK_UNSAFE_PLAN, _MOCK_UNSAFE_PLAN, _MOCK_SAFE_PLAN],                 # #10
]


class _MockLLMState:
    """Cursor over _MOCK_SEQUENCES. The experiment driver calls
    `start_scenario(key)` before each prompt's run_with_trace; subsequent
    `get_next()` calls return the next planned plan for that scenario.
    Per-trial RNG perturbation makes dry-run trials look stochastic."""
    def __init__(self) -> None:
        self.cursor: Dict[str, int]   = {}
        self.assigned: Dict[str, int] = {}
        self.next_idx                 = 0
        self.trial_idx                = 0
        self.current_scenario: str    = ""
        self._rng                     = random.Random(12345)

    def reset(self) -> None:
        self.cursor.clear()
        self.assigned.clear()
        self.next_idx = 0
        self.trial_idx += 1
        self.current_scenario = ""
        self._rng = random.Random(12345 + self.trial_idx)

    def start_scenario(self, scenario_key: str) -> None:
        self.current_scenario = scenario_key
        # Each scenario keeps its own cursor (reset every time we re-enter it
        # within a trial; in practice each scenario is visited once per trial).
        self.cursor[scenario_key] = 0

    def get_next(self) -> str:
        key = self.current_scenario or "default"
        if key not in self.assigned:
            self.assigned[key] = self.next_idx % len(_MOCK_SEQUENCES)
            self.next_idx += 1
        seq_idx  = self.assigned[key]
        sequence = _MOCK_SEQUENCES[seq_idx]
        i = self.cursor.get(key, 0)
        plan = sequence[min(i, len(sequence) - 1)]
        if self.trial_idx >= 2 and i == 0 and plan != _MOCK_SAFE_PLAN:
            if self._rng.random() < 0.20:
                plan = _MOCK_SAFE_PLAN
        elif self.trial_idx >= 2 and i == 0 and plan == _MOCK_SAFE_PLAN:
            if self._rng.random() < 0.10:
                plan = _MOCK_UNSAFE_PLAN
        self.cursor[key] = i + 1
        return plan


_MOCK_STATE = _MockLLMState()


def _mock_call_claude(prompt: str, temperature: float = 0.7) -> str:
    """Dry-run mock for `pipeline.call_claude`. Ignores prompt content and
    pulls from the cursor for the current scenario (set by the driver)."""
    return _MOCK_STATE.get_next()


def _mock_run_alloy(_file_path: str = None) -> Tuple[bool, str, str]:
    """Inspect the GeneratedPlan currently in COMPARE_FILE and classify it.
    SAFE if it matches _MOCK_SAFE_PLAN, SYNTAX_ERROR if matches
    _MOCK_SYNTAX_PLAN, otherwise UNSAFE."""
    try:
        with open(COMPARE_FILE, "r", encoding="utf-8") as f:
            content = f.read()
    except FileNotFoundError:
        return False, "compare file missing", "ERROR"
    plan = pipeline.extract_generated_plan(content) or ""
    if "z.assignedGuard = lg" in plan:
        return True, "No instance found", "SAFE"
    if "intentional typo" in plan:
        return False, "Syntax error: -- not a valid comment", "SYNTAX_ERROR"
    return True, "Instance found", "UNSAFE"


# =============================================================================
# 6. Core experiment loop  (multi-trial, with explicit NO-LOOP baseline)
# =============================================================================
#
# Terminology aligned to the project requirement:
#
#   NO-LOOP  baseline = the verdict at iteration 1 (initial Claude generation,
#                       no repair). This is "what happens if you don't run the
#                       loop". It is captured automatically because we always
#                       record the iter-1 status before any repair.
#
#   WITH-LOOP outcome = the verdict after iteration N (final status, after up
#                       to `max_iters` repair turns). This is "what happens
#                       after running the loop".
#
# The script runs the full 10-prompt dataset `--trials N` times (default 3).
# Each trial is an independent re-roll of the LLM, so we can quantify the
# variance of the bottom-line numbers across runs ("how many times we ran on
# the tool" = `trials * 10`; "does it work after several runs" = the std of
# the with-loop rate across trials).

class Counters:
    """How many times each subsystem was touched, across the whole experiment.

    LLM calls are counted on every iteration. Alloy calls are counted ONLY
    when Alloy was actually invoked -- iterations whose LLM reply was not a
    parseable Alloy block (which we classify as SYNTAX_ERROR, same family
    as a real Alloy compile error) do not touch Alloy."""
    def __init__(self) -> None:
        self.trials_completed    = 0
        self.prompts_processed   = 0
        self.llm_calls           = 0
        self.alloy_calls         = 0
        self.repair_calls        = 0    # subset of llm_calls (any repair kind)
        self.syntax_repair_calls = 0
        self.logic_repair_calls  = 0
        self.substance_repair_calls = 0

    def asdict(self) -> Dict:
        return {
            "trials_completed":     self.trials_completed,
            "prompts_processed":    self.prompts_processed,
            "llm_calls_total":      self.llm_calls,
            "alloy_calls_total":    self.alloy_calls,
            "repair_calls_total":   self.repair_calls,
            "syntax_repair_calls":  self.syntax_repair_calls,
            "logic_repair_calls":   self.logic_repair_calls,
            "substance_repair_calls": self.substance_repair_calls,
        }


def _run_one_prompt(prompt_obj: Dict,
                    *, max_iters: int, scope: str,
                    counters: Counters,
                    dry_run: bool) -> Dict:
    """Recorder for a single prompt. All algorithm/prompt logic lives in
    `pipeline_generated.run_with_trace`; we just call it, then unpack the
    returned trace into the experiment's data structures."""
    pid      = prompt_obj["id"]
    scenario = prompt_obj["prompt"]
    category = prompt_obj.get("category", "uncategorised")
    source   = prompt_obj.get("source", {})

    print(f"  [prompt {pid:>2}] {category}")

    # Reset the GeneratedPlan slot in the compare file before each prompt so
    # the pipeline always starts from the clean safety code.
    build_compare_file(scope=scope)

    # Tell the dry-run mock which scenario this is so its cursor starts fresh.
    if dry_run:
        _MOCK_STATE.start_scenario(f"prompt_{pid}")

    # All prompt building, LLM-calling, Alloy-running, and repair logic
    # happens inside pipeline_generated.
    trace = pipeline.run_with_trace(scenario,
                                    compare_path=COMPARE_FILE,
                                    max_iters=max_iters,
                                    verbose=True)

    # ------- count LLM / Alloy invocations from the trace -------
    for it in trace["iterations"]:
        counters.llm_calls += 1                       # every iter calls the LLM
        if it.get("ran_alloy"):                       # but Alloy only if extract OK
            counters.alloy_calls += 1
        kind = it["kind"]
        if kind == "syntax_repair":
            counters.repair_calls += 1
            counters.syntax_repair_calls += 1
        elif kind == "logic_repair":
            counters.repair_calls += 1
            counters.logic_repair_calls += 1
        elif kind == "substance_repair":
            counters.repair_calls += 1
            counters.substance_repair_calls += 1

    initial = trace["iterations"][0]
    final_status = trace["final_status"]

    case: Dict = {
        "id":             pid,
        "category":       category,
        "source":         source,
        "scenario":       scenario,
        "initial_status": initial["status"],
        "initial_safe":   initial["status"] == "SAFE",
        "final_status":   final_status,
        "final_safe":     final_status == "SAFE",
        "total_iters":    trace["total_iters"],
        "iterations":     trace["iterations"],
    }
    counters.prompts_processed += 1
    return case


def _install_mocks() -> Tuple[callable, callable]:
    """Monkey-patch pipeline.call_claude / pipeline.run_alloy for dry-run mode.
    Returns the originals so we can restore them on exit."""
    orig_llm   = pipeline.call_claude
    orig_alloy = pipeline.run_alloy
    pipeline.call_claude = _mock_call_claude
    pipeline.run_alloy   = _mock_run_alloy
    return orig_llm, orig_alloy


def _restore_mocks(orig_llm, orig_alloy) -> None:
    pipeline.call_claude = orig_llm
    pipeline.run_alloy   = orig_alloy


def run_experiment(prompts: List[Dict],
                   *, trials: int,
                   max_iters: int,
                   scope: str,
                   dry_run: bool) -> Dict:
    """Run the full multi-trial experiment and return the aggregated record."""
    orig_llm = orig_alloy = None
    if dry_run:
        orig_llm, orig_alloy = _install_mocks()
        _MOCK_STATE.reset()

    try:
        build_compare_file(scope=scope)
        counters = Counters()
        trial_records: List[Dict] = []

        for t in range(1, trials + 1):
            print(f"\n========== Trial {t}/{trials} ==========")
            if dry_run:
                _MOCK_STATE.reset()
            per_prompt_results = []
            for prompt_obj in prompts:
                res = _run_one_prompt(prompt_obj,
                                      max_iters=max_iters,
                                      scope=scope,
                                      counters=counters,
                                      dry_run=dry_run)
                per_prompt_results.append(res)

            trial_records.append({
                "trial_id": t,
                "results":  per_prompt_results,
                "trial_summary": _trial_summary(per_prompt_results),
            })
            counters.trials_completed += 1

            # Save incremental progress (so a mid-trial crash doesn't lose state).
            _save_log({
                "config": {
                    "trials":    trials,
                    "max_iters": max_iters,
                    "scope":     scope,
                    "dry_run":   dry_run,
                    "n_prompts": len(prompts),
                },
                "counters":      counters.asdict(),
                "trials":        trial_records,
                "aggregate":     _aggregate(trial_records),
            }, dry_run=dry_run)

        return {
            "config": {
                "trials":    trials,
                "max_iters": max_iters,
                "scope":     scope,
                "dry_run":   dry_run,
                "n_prompts": len(prompts),
            },
            "counters":  counters.asdict(),
            "trials":    trial_records,
            "aggregate": _aggregate(trial_records),
        }
    finally:
        if dry_run:
            _restore_mocks(orig_llm, orig_alloy)


# ---------------------------------------------------------------------------
# Aggregation helpers
# ---------------------------------------------------------------------------

def _trial_summary(results: List[Dict]) -> Dict:
    n = len(results) or 1
    initial = sum(1 for r in results if r["initial_safe"])
    final   = sum(1 for r in results if r["final_safe"])
    iters   = [r["total_iters"] for r in results if r["final_safe"]]
    return {
        "n":                  len(results),
        "noloop_safe":        initial,
        "withloop_safe":      final,
        "noloop_pass_rate":   initial / n,
        "withloop_pass_rate": final / n,
        "mean_iters_safe":    (sum(iters) / len(iters)) if iters else 0.0,
    }


def _mean_std(values: List[float]) -> Tuple[float, float]:
    if not values:
        return 0.0, 0.0
    m = sum(values) / len(values)
    if len(values) == 1:
        return m, 0.0
    var = sum((v - m) ** 2 for v in values) / (len(values) - 1)
    return m, var ** 0.5


def _aggregate(trial_records: List[Dict]) -> Dict:
    """Compute cross-trial means and standard deviations for the bottom-line
    numbers and per-prompt success rates."""
    if not trial_records:
        return {}
    noloop_rates    = [t["trial_summary"]["noloop_pass_rate"]   for t in trial_records]
    withloop_rates  = [t["trial_summary"]["withloop_pass_rate"] for t in trial_records]
    mean_iters_safe = [t["trial_summary"]["mean_iters_safe"]    for t in trial_records]

    # Per-prompt aggregation: rates and iteration counts across trials.
    by_id: Dict[int, Dict] = {}
    for trial in trial_records:
        for r in trial["results"]:
            d = by_id.setdefault(r["id"], {
                "id":             r["id"],
                "category":       r["category"],
                "noloop_safe":    [],
                "withloop_safe":  [],
                "iters":          [],
                "final_statuses": [],
            })
            d["noloop_safe"].append(1 if r["initial_safe"] else 0)
            d["withloop_safe"].append(1 if r["final_safe"] else 0)
            d["iters"].append(r["total_iters"])
            d["final_statuses"].append(r["final_status"])

    per_prompt = []
    for pid in sorted(by_id):
        d = by_id[pid]
        nm, ns = _mean_std(d["noloop_safe"])
        wm, ws = _mean_std(d["withloop_safe"])
        im, ic = _mean_std(d["iters"])
        per_prompt.append({
            "id":               pid,
            "category":         d["category"],
            "noloop_mean":      nm,
            "noloop_std":       ns,
            "withloop_mean":    wm,
            "withloop_std":     ws,
            "iters_mean":       im,
            "iters_std":        ic,
            "final_statuses":   d["final_statuses"],
            "trial_passes_noloop":   sum(d["noloop_safe"]),
            "trial_passes_withloop": sum(d["withloop_safe"]),
            "trials":           len(d["noloop_safe"]),
        })

    nm, ns = _mean_std(noloop_rates)
    wm, ws = _mean_std(withloop_rates)
    im, ic = _mean_std(mean_iters_safe)
    return {
        "noloop_rate_mean":     nm,
        "noloop_rate_std":      ns,
        "withloop_rate_mean":   wm,
        "withloop_rate_std":    ws,
        "uplift_mean":          wm - nm,
        "mean_iters_safe_mean": im,
        "mean_iters_safe_std":  ic,
        "per_prompt":           per_prompt,
    }


# =============================================================================
# 7. Persistence
# =============================================================================

def _save_log(payload: Dict, dry_run: bool = False) -> None:
    payload = dict(payload)  # shallow copy so we can stamp meta
    payload["generated_at"] = datetime.utcnow().isoformat(timespec="seconds") + "Z"
    payload["dry_run"] = dry_run
    with open(LOG_FILE, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, ensure_ascii=False)


def _save_csv(payload: Dict) -> None:
    """One row per (trial, prompt). Aggregate rows are appended at the end."""
    cols = ["trial_id", "prompt_id", "category",
            "initial_status", "initial_safe (NO-LOOP)",
            "final_status",   "final_safe (WITH-LOOP)",
            "total_iters", "source_type", "source_url"]
    with open(CSV_FILE, "w", encoding="utf-8", newline="") as f:
        w = csv.writer(f)
        w.writerow(cols)
        for trial in payload.get("trials", []):
            tid = trial["trial_id"]
            for r in trial["results"]:
                src = r.get("source", {}) or {}
                w.writerow([
                    tid, r["id"], r["category"],
                    r["initial_status"], r["initial_safe"],
                    r["final_status"],   r["final_safe"],
                    r["total_iters"],
                    src.get("type", ""), src.get("url", ""),
                ])
        # Blank row then per-prompt aggregate
        w.writerow([])
        w.writerow(["# per-prompt aggregate across trials"])
        w.writerow(["prompt_id", "category", "trials",
                    "noloop_pass", "noloop_rate", "noloop_std",
                    "withloop_pass", "withloop_rate", "withloop_std",
                    "iters_mean", "iters_std", "final_statuses"])
        for p in payload.get("aggregate", {}).get("per_prompt", []):
            w.writerow([
                p["id"], p["category"], p["trials"],
                p["trial_passes_noloop"],   f"{p['noloop_mean']:.3f}",   f"{p['noloop_std']:.3f}",
                p["trial_passes_withloop"], f"{p['withloop_mean']:.3f}", f"{p['withloop_std']:.3f}",
                f"{p['iters_mean']:.2f}",   f"{p['iters_std']:.2f}",
                "|".join(p["final_statuses"]),
            ])


def _load_log() -> Dict:
    with open(LOG_FILE, "r", encoding="utf-8") as f:
        return json.load(f)


# =============================================================================
# 8. Plotting
# =============================================================================

def plot_results(payload: Dict) -> None:
    """Render a 1x2 figure summarising the multi-trial experiment.

      (1) Bottom line: NO-LOOP vs WITH-LOOP success rate, mean ± std across trials.
      (2) Per-prompt iteration count and final-status mix across trials."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np
    except ImportError:
        print("matplotlib not installed; skipping plots. "
              "Install with: pip install matplotlib numpy", file=sys.stderr)
        return

    trials   = payload.get("trials", [])
    agg      = payload.get("aggregate", {})
    config   = payload.get("config", {})
    counters = payload.get("counters", {})
    if not trials:
        print("No trials in payload; cannot plot.", file=sys.stderr)
        return

    n_trials   = config.get("trials", len(trials))
    n_prompts  = config.get("n_prompts", len(trials[0]["results"]))

    fig, axes = plt.subplots(1, 2, figsize=(15, 6))
    fig.suptitle(
        f"Swimming-Safety LLM Plan Verification\n"
        f"{n_trials} trials \u00d7 {n_prompts} prompts = "
        f"{n_trials * n_prompts} prompt runs   "
        f"|   LLM calls: {counters.get('llm_calls_total', '?')}   "
        f"Alloy calls: {counters.get('alloy_calls_total', '?')}   "
        f"max_iters: {config.get('max_iters', '?')}"
        + ("   [DRY-RUN]" if config.get("dry_run") else ""),
        fontsize=12, fontweight="bold")

    # =============================================================== panel 1
    # Bottom-line NO-LOOP vs WITH-LOOP comparison (cross-trial mean ± std).
    ax = axes[0]
    no_mean   = agg.get("noloop_rate_mean",   0.0) * 100
    no_std    = agg.get("noloop_rate_std",    0.0) * 100
    with_mean = agg.get("withloop_rate_mean", 0.0) * 100
    with_std  = agg.get("withloop_rate_std",  0.0) * 100

    no_err_low   = no_std
    no_err_high  = min(no_std, 100 - no_mean)
    with_err_low = with_std
    with_err_high = min(with_std, 100 - with_mean)
    
    asym_yerr = [
        [no_err_low, with_err_low],   
        [no_err_high, with_err_high] 
    ]

    bars = ax.bar(
        ["NO-LOOP\n(initial gen only)",
         "WITH-LOOP\n(after repair)"],
        [no_mean, with_mean],
        yerr=asym_yerr,              
        capsize=10,
        color=["#d35400", "#27ae60"],
        edgecolor="black")

    for b, m, s in zip(bars, [no_mean, with_mean], [no_std, with_std]):
        label = f"{m:.0f}% \u00b1 {s:.0f}"
        
        if m + s > 95 or m > 85:
            ax.text(b.get_x() + b.get_width() / 2, m - 6, label,
                    ha="center", va="top", fontweight="bold", color="white", fontsize=10)
        else:
            top_y = m + s + 1
            ax.text(b.get_x() + b.get_width() / 2, top_y, label,
                    ha="center", va="bottom", fontweight="bold", fontsize=10)

    ax.text(0.5, min(with_mean / 2, 40),
            f"uplift = +{(with_mean - no_mean):.0f} pp",
            ha="center", color="#003300", fontsize=11, fontweight="bold")

    ax.set_ylim(0, 100)
    ax.set_ylabel("Safe-plan rate (%)")
    ax.set_title(f"(1) Bottom line over {n_trials} independent trials", pad=10)
    ax.grid(axis="y", linestyle=":", alpha=0.4)
    # =============================================================== panel 2
    # Per-prompt iteration count with final-status mix annotation.
    ax = axes[1]
    per     = agg.get("per_prompt", [])
    ids     = [p["id"] for p in per]
    iters_m = np.array([p["iters_mean"] for p in per])
    iters_s = np.array([p["iters_std"]  for p in per])
    bar_colors = ["#27ae60" if p["withloop_mean"] >= 0.5 else "#c0392b"
                  for p in per]
    bars = ax.barh([f"#{i}" for i in ids], iters_m,
                   xerr=iters_s, capsize=3,
                   color=bar_colors, edgecolor="black")
    for b, p in zip(bars, per):
        # show distribution of final statuses across trials
        counts: Dict[str, int] = {}
        for s in p["final_statuses"]:
            counts[s] = counts.get(s, 0) + 1
        annotation = "  ".join(f"{k}\u00d7{v}" for k, v in counts.items())
        ax.text(b.get_width() + 0.1,
                b.get_y() + b.get_height() / 2,
                annotation, va="center", fontsize=8)
    ax.set_xlabel("Mean iterations to terminate (\u00b1 std)")
    ax.set_title("(1) Iterations per prompt and final-status mix across trials")
    ax.invert_yaxis()
    ax.grid(axis="x", linestyle=":", alpha=0.4)

    plt.tight_layout(rect=(0, 0, 1, 0.92))
    plt.savefig(PLOT_FILE, dpi=140)
    print(f"plots saved to {PLOT_FILE}")


# =============================================================================
# pass@k (Chen et al., 2021, Section 2.1 and Figure 3)
#
# For each prompt, n independent initial plans are sampled and c of them pass
# Alloy. The score for k <= n is 1 - C(n-c, k) / C(n, k). Feedback-conditioned
# repair attempts belong to the loop analysis, not to this pass@k sample pool.
# =============================================================================


def pass_at_k(n: int, c: int, k: int) -> float:
    """Return the paper's numerically stable unbiased pass@k estimate."""
    if not 0 <= c <= n:
        raise ValueError("c must satisfy 0 <= c <= n")
    if not 1 <= k <= n:
        raise ValueError("k must satisfy 1 <= k <= n")
    if n - c < k:
        return 1.0
    product = 1.0
    for i in range(n - c + 1, n + 1):
        product *= 1.0 - k / i
    return 1.0 - product


def _passk_k_values(k_max: int, n: int) -> List[int]:
    """k values to report: 1 .. k_max, capped at n because the paper needs n >= k."""
    if n < 1 or k_max < 1:
        return []
    upper = min(k_max, n)
    if k_max > n:
        print(f"  [pass@k] k_max={k_max} exceeds n={n}; pass@k needs n >= k "
              f"(Chen et al. 2021), so k is capped at {upper}.", file=sys.stderr)
    return list(range(1, upper + 1))


def _finalize_passk_metrics(per_prompt_data: Dict, k_values: List[int]) -> Dict:
    """Score independent initial plans and average pass@k over prompts."""
    stale_keys = (
        "c_at_k", "passk_stds", "passk_rates_noloop",
        "passk_stds_noloop", "c_noloop", "c_withloop",
    )

    for data in per_prompt_data.values():
        for key in stale_keys:
            data.pop(key, None)
        trials    = data["trials"]
        n_samples = len(trials)
        n_correct = sum(
            bool(t["initial_safe"])
            if "initial_safe" in t
            else t.get("first_safe_idx") == 0
            for t in trials
        )

        data["n_samples"] = n_samples
        data["n_correct"] = n_correct
        data["passk_rates"] = [
            pass_at_k(n_samples, n_correct, k) for k in k_values
        ] if n_samples else []

    aggregate: Dict[str, List[float]] = {"passk_rates": [], "passk_stds": []}
    for k_idx in range(len(k_values)):
        m, s = _mean_std([d["passk_rates"][k_idx] for d in per_prompt_data.values()])
        aggregate["passk_rates"].append(m)
        aggregate["passk_stds"].append(s)
    return aggregate

def run_passk_experiment(
    prompts: List[Dict],
    *,
    k_max: int = 10,
    n: int = 10,
    scope: str = ALLOY_SCOPE_DEFAULT,
    dry_run: bool = False,
) -> Dict:
    """Generate n independent initial plans per prompt and compute pass@k."""
    orig_llm = orig_alloy = None
    if dry_run:
        orig_llm, orig_alloy = _install_mocks()
        _MOCK_STATE.reset()

    try:
        build_compare_file(scope=scope)
        counters = Counters()
        k_values: List[int] = _passk_k_values(k_max, n)  # [1, ..., min(k_max, n)]

        per_prompt_data: Dict[int, Dict] = {}
        for p in prompts:
            per_prompt_data[p["id"]] = {
                "id":       p["id"],
                "category": p.get("category", "uncategorised"),
                "trials":   [],
            }

        for rep in range(1, n + 1):
            print(f"\n========== pass@k  Repetition {rep}/{n} ==========")
            if dry_run:
                _MOCK_STATE.reset()

            for prompt_obj in prompts:
                pid = prompt_obj["id"]

                case = _run_one_prompt(
                    prompt_obj,
                    max_iters=1,
                    scope=scope,
                    counters=counters,
                    dry_run=dry_run,
                )

                first_safe_idx: int | None = next(
                    (i for i, it in enumerate(case["iterations"])
                     if it["status"] == "SAFE"),
                    None,
                )

                per_prompt_data[pid]["trials"].append({
                    "rep":            rep,
                    "initial_safe":   first_safe_idx == 0,
                    "first_safe_idx": first_safe_idx,
                    "total_iters":    case["total_iters"],
                    "final_status":   case["final_status"],
                })

        aggregate = _finalize_passk_metrics(per_prompt_data, k_values)

        payload: Dict = {
            "config": {
                "k_max":     k_max,
                "n":         n,
                "metric":    "chen_et_al_2021_figure_3",
                "estimator": "1 - C(n - c, k) / C(n, k)",
                "sample":    "independent initial plan",
                "correct":   "Alloy status SAFE",
                "scope":     scope,
                "dry_run":   dry_run,
                "n_prompts": len(prompts),
            },
            "counters":  counters.asdict(),
            "k_values":  k_values,
            "per_prompt": per_prompt_data,
            "aggregate": aggregate,
            "generated_at": datetime.utcnow().isoformat(timespec="seconds") + "Z",
        }

        with open(PASSK_LOG_FILE, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2, ensure_ascii=False)
        print(f"pass@k log saved to {PASSK_LOG_FILE}")

        return payload

    finally:
        if dry_run:
            _restore_mocks(orig_llm, orig_alloy)


# =============================================================================
# Unified runner: one data collection pass for both analyses
# =============================================================================

def run_unified_experiment(
    prompts: List[Dict],
    *,
    trials: int = 10,
    max_iters: int = MAX_ITERATIONS_DEFAULT,
    k_max: int = 10,
    scope: str = ALLOY_SCOPE_DEFAULT,
    dry_run: bool = False,
) -> Tuple[Dict, Dict]:
    """Return loop metrics and pass@k metrics from the same trials.

    The loop analysis uses each full trace. The pass@k analysis uses only the
    independent initial plan from each trace.
    """

    orig_llm = orig_alloy = None
    if dry_run:
        orig_llm, orig_alloy = _install_mocks()
        _MOCK_STATE.reset()

    try:
        build_compare_file(scope=scope)
        counters = Counters()
        trial_records: List[Dict] = []

        per_prompt_data: Dict[int, Dict] = {}
        for p in prompts:
            per_prompt_data[p["id"]] = {
                "id":       p["id"],
                "category": p.get("category", "uncategorised"),
                "trials":   [],
            }
        k_values: List[int] = _passk_k_values(k_max, trials)

        for t in range(1, trials + 1):
            print(f"\n========== Trial {t}/{trials} [unified] ==========")
            if dry_run:
                _MOCK_STATE.reset()

            per_prompt_results: List[Dict] = []
            for prompt_obj in prompts:
                pid = prompt_obj["id"]

                case = _run_one_prompt(
                    prompt_obj,
                    max_iters=max_iters,
                    scope=scope,
                    counters=counters,
                    dry_run=dry_run,
                )
                per_prompt_results.append(case)

                first_safe_idx: int | None = next(
                    (i for i, it in enumerate(case["iterations"])
                     if it["status"] == "SAFE"),
                    None,
                )
                per_prompt_data[pid]["trials"].append({
                    "rep":            t,
                    "initial_safe":   first_safe_idx == 0,
                    "first_safe_idx": first_safe_idx,
                    "total_iters":    case["total_iters"],
                    "final_status":   case["final_status"],
                })

            trial_records.append({
                "trial_id":      t,
                "results":       per_prompt_results,
                "trial_summary": _trial_summary(per_prompt_results),
            })
            counters.trials_completed += 1

            # Save after every trial so a failed run can be resumed or inspected.
            _save_log(
                {
                    "config": {
                        "trials":    trials,
                        "max_iters": max_iters,
                        "scope":     scope,
                        "dry_run":   dry_run,
                        "n_prompts": len(prompts),
                        "unified":   True,
                    },
                    "counters":  counters.asdict(),
                    "trials":    trial_records,
                    "aggregate": _aggregate(trial_records),
                },
                dry_run=dry_run,
            )

        main_payload: Dict = {
            "config": {
                "trials":    trials,
                "max_iters": max_iters,
                "scope":     scope,
                "dry_run":   dry_run,
                "n_prompts": len(prompts),
                "unified":   True,
            },
            "counters":  counters.asdict(),
            "trials":    trial_records,
            "aggregate": _aggregate(trial_records),
        }

        aggregate = _finalize_passk_metrics(per_prompt_data, k_values)

        passk_payload: Dict = {
            "config": {
                "k_max":     k_max,
                "n":         trials,
                "metric":    "chen_et_al_2021_figure_3",
                "estimator": "1 - C(n - c, k) / C(n, k)",
                "sample":    "independent initial plan",
                "correct":   "Alloy status SAFE",
                "scope":     scope,
                "dry_run":   dry_run,
                "n_prompts": len(prompts),
                "unified":   True,
            },
            "counters":   counters.asdict(),
            "k_values":   k_values,
            "per_prompt": per_prompt_data,
            "aggregate":  aggregate,
            "generated_at": datetime.utcnow().isoformat(timespec="seconds") + "Z",
        }

        with open(PASSK_LOG_FILE, "w", encoding="utf-8") as f:
            json.dump(passk_payload, f, indent=2, ensure_ascii=False)
        print(f"pass@k log saved to {PASSK_LOG_FILE}")

        return main_payload, passk_payload

    finally:
        if dry_run:
            _restore_mocks(orig_llm, orig_alloy)


def recompute_passk_payload(payload: Dict) -> Dict:
    """Recompute Figure 3 pass@k scores from saved initial-plan outcomes."""
    per_prompt = payload.get("per_prompt", {})
    if not per_prompt or not all("trials" in d for d in per_prompt.values()):
        return payload  # nothing to recompute from; plot whatever is stored

    config   = payload.get("config", {})
    # Cap k by the samples actually present, not by what the config intended:
    # a run interrupted part-way leaves fewer trials than config["n"].
    n        = min((len(d["trials"]) for d in per_prompt.values()), default=0)
    k_max    = config.get("k_max", n)
    k_values = _passk_k_values(k_max, n)

    config["n"]      = n
    config["metric"] = "chen_et_al_2021_figure_3"
    config["estimator"] = "1 - C(n - c, k) / C(n, k)"
    config["sample"]    = "independent initial plan"
    config["correct"]   = "Alloy status SAFE"
    payload["k_values"]  = k_values
    payload["aggregate"] = _finalize_passk_metrics(per_prompt, k_values)
    return payload


def plot_passk_results(payload: Dict) -> None:
    """Plot per-prompt estimates and their mean across prompts."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np
        from matplotlib.text import Text
    except ImportError:
        print("matplotlib not installed; skipping pass@k plots. "
              "Install with: pip install matplotlib numpy", file=sys.stderr)
        return

    plt.rcParams.update({
        "font.size": PASSK_FONT_SIZE_PT,
        "font.weight": "normal",
        "font.family": "serif",
        "axes.titlesize": PASSK_FONT_SIZE_PT,
        "axes.titleweight": "normal",
        "axes.labelsize": PASSK_FONT_SIZE_PT,
        "xtick.labelsize": PASSK_FONT_SIZE_PT,
        "ytick.labelsize": PASSK_FONT_SIZE_PT,
        "legend.fontsize": PASSK_FONT_SIZE_PT,
        "legend.title_fontsize": PASSK_FONT_SIZE_PT,
        "figure.titlesize": PASSK_FONT_SIZE_PT,
        "pgf.rcfonts": False,
        "pgf.texsystem": "pdflatex",
    })

    def finalize_passk_figure(fig) -> None:
        fig.canvas.draw()
        for text in fig.findobj(match=Text):
            text.set_fontsize(PASSK_FONT_SIZE_PT)
            text.set_fontweight("normal")

    def latex_escape(text: str) -> str:
        replacements = {
            "\\": r"\textbackslash{}",
            "&": r"\&",
            "%": r"\%",
            "$": r"\$",
            "#": r"\#",
            "_": r"\_",
            "{": r"\{",
            "}": r"\}",
            "~": r"\textasciitilde{}",
            "^": r"\textasciicircum{}",
            "±": r"\ensuremath{\pm}",
            "×": r"\ensuremath{\times}",
            "∈": r"\ensuremath{\in}",
        }
        return "".join(replacements.get(ch, ch) for ch in text)

    def prepare_for_latex(fig) -> None:
        fig.canvas.draw()
        for text in fig.findobj(match=Text):
            text.set_text(latex_escape(text.get_text()))
            text.set_fontsize(PASSK_FONT_SIZE_PT)
            text.set_fontweight("normal")
            text.set_fontfamily("serif")

    def save_pgf(fig, path: str) -> None:
        prepare_for_latex(fig)
        fig.savefig(path)
        fontsize_cmd = (
            rf"\fontsize{{{PASSK_FONT_SIZE_PT:.6f}}}"
            rf"{{{PASSK_FONT_SIZE_PT * 1.2:.6f}}}\selectfont"
        )
        with open(path, "r", encoding="utf-8") as f:
            pgf = f.read()
        pgf = pgf.replace(fontsize_cmd, r"\normalsize")
        pgf = pgf.replace(r"\rmfamily\normalsize", r"\normalfont\normalsize")
        with open(path, "w", encoding="utf-8") as f:
            f.write(pgf)

    config      = payload.get("config", {})
    k_values    = payload.get("k_values", [])
    per_prompt  = payload.get("per_prompt", {})
    agg         = payload.get("aggregate", {})

    if not k_values:
        print("No pass@k data; cannot plot.", file=sys.stderr)
        return

    k_arr       = np.array(k_values, dtype=float)
    agg_rates   = np.array(agg.get("passk_rates", []), dtype=float)
    agg_stds    = np.array(agg.get("passk_stds",  []), dtype=float)
    n           = config.get("n", "?")
    k_min       = min(k_values)
    k_max       = max(k_values)
    n_prompts   = config.get("n_prompts", len(per_prompt))

    # ================================================ Figure 1 : per-prompt
    fig, ax = plt.subplots(figsize=PASSK_PER_PROMPT_FIGSIZE)
    pid_list = sorted(per_prompt.keys(), key=lambda x: int(x))
    palette  = plt.cm.tab10(np.linspace(0, 1, max(len(pid_list), 1)))

    for pid, color in zip(pid_list, palette):
        data  = per_prompt[pid]
        rates = np.array(data["passk_rates"], dtype=float)
        label = f"#{int(pid)}"
        ax.plot(k_arr, rates * 100,
                marker="o", markersize=2.8, linewidth=1.2,
                color=color, label=label)

    zero_curves = [
        f"#{int(pid)}" for pid in pid_list
        if not any(per_prompt[pid]["passk_rates"])
    ]
    if zero_curves:
        ax.text(
            0.98, 0.04, f"overlap at 0: {', '.join(zero_curves)}",
            transform=ax.transAxes, ha="right", va="bottom",
            fontsize=PASSK_FONT_SIZE_PT - 1, color="#555555",
        )

    # Light vertical guides at the ends of the k range to anchor the eye.
    for k_anchor in [k_min, k_max]:
        ax.axvline(x=k_anchor, color="grey", linestyle="--",
                   linewidth=0.6, alpha=0.35)

    ax.set_title(f"pass@k = 1 - C(n-c,k) / C(n,k), n={n}", pad=3)
    ax.set_xlabel("k independent samples", fontsize=PASSK_FONT_SIZE_PT, labelpad=1)
    ax.set_ylabel("pass@k (%)", fontsize=PASSK_FONT_SIZE_PT, labelpad=2)
    ax.set_xticks(k_values)
    ax.set_xlim(k_min - 0.4, k_max + 0.4)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_ylim(*PASSK_YLIM)
    ax.tick_params(axis="both", labelsize=PASSK_FONT_SIZE_PT)
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.26), ncol=5,
              frameon=False, handlelength=1.0, columnspacing=0.7,
              handletextpad=0.3, borderaxespad=0.0,
              prop={"size": PASSK_FONT_SIZE_PT})
    ax.grid(linestyle=":", alpha=0.35)
    per_prompt_bottom = (
        PASSK_AXES_TOP - PASSK_AXES_HEIGHT_IN / PASSK_PER_PROMPT_FIGSIZE[1]
    )
    fig.subplots_adjust(
        left=PASSK_AXES_LEFT,
        right=PASSK_AXES_RIGHT,
        top=PASSK_AXES_TOP,
        bottom=per_prompt_bottom,
    )

    finalize_passk_figure(fig)
    fig.savefig(PASSK_PER_PROMPT_PLOT_FILE, dpi=140)
    save_pgf(fig, PASSK_PER_PROMPT_PGF_FILE)
    plt.close(fig)

    # ============================================= Figure 2 : aggregate curve
    fig, ax = plt.subplots(figsize=PASSK_AGGREGATE_FIGSIZE)
    ax.plot(k_arr, agg_rates * 100,
            marker="o", markersize=3.2, linewidth=1.6, color="#2c3e50",
            label="mean", zorder=5)
    ax.fill_between(k_arr,
                    np.clip((agg_rates - agg_stds) * 100, 0, 100),
                    np.clip((agg_rates + agg_stds) * 100, 0, 100),
                    alpha=0.22, color="#2c3e50",
                    label="±1 s.d.")

    ax.set_title(f"pass@k = 1 - C(n-c,k) / C(n,k), n={n}", pad=3)
    ax.set_xlabel("k independent samples", fontsize=PASSK_FONT_SIZE_PT, labelpad=1)
    ax.set_ylabel("pass@k (%)", fontsize=PASSK_FONT_SIZE_PT, labelpad=2)
    ax.set_xticks(k_values)
    ax.set_xlim(k_min - 0.4, k_max + 0.4)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_ylim(*PASSK_YLIM)
    ax.tick_params(axis="both", labelsize=PASSK_FONT_SIZE_PT)
    ax.legend(loc="lower right", frameon=False, handlelength=1.2,
              handletextpad=0.4, borderaxespad=0.2,
              prop={"size": PASSK_FONT_SIZE_PT})
    ax.grid(linestyle=":", alpha=0.35)
    aggregate_bottom = (
        PASSK_AXES_TOP - PASSK_AXES_HEIGHT_IN / PASSK_AGGREGATE_FIGSIZE[1]
    )
    fig.subplots_adjust(
        left=PASSK_AXES_LEFT,
        right=PASSK_AXES_RIGHT,
        top=PASSK_AXES_TOP,
        bottom=aggregate_bottom,
    )

    finalize_passk_figure(fig)
    fig.savefig(PASSK_AGGREGATE_PLOT_FILE, dpi=140)
    save_pgf(fig, PASSK_AGGREGATE_PGF_FILE)
    plt.close(fig)

    print("pass@k plots saved to:")
    for path in PASSK_PLOT_FILES:
        print(f"  {path}")
    print("pass@k PGF plots saved to:")
    for path in PASSK_PGF_FILES:
        print(f"  {path}")


# =============================================================================
# pass@k textual report
# =============================================================================

def print_passk_report(payload: Dict) -> None:
    """Print a concise textual summary of the pass@k experiment to stdout."""
    config      = payload.get("config", {})
    k_values    = payload.get("k_values", [])
    per_prompt  = payload.get("per_prompt", {})
    agg         = payload.get("aggregate", {})

    if not k_values:
        print("No pass@k data to report.")
        return

    n         = config.get("n", "?")
    k_min     = min(k_values)
    k_max     = max(k_values)
    n_prompts = config.get("n_prompts", len(per_prompt))

    print("\n=========================================================")
    print(f" pass@k experiment  (n = {n},  k = {k_min} .. {k_max})")
    print(" definition: Chen et al. 2021 (arXiv:2107.03374), Sec. 2.1")
    print("   n independent initial plans; c SAFE plans; Figure 3 estimator")
    print("=========================================================")
    print(f"  prompts              : {n_prompts}")
    print(f"  samples per prompt (n): {n}")
    print(f"  k range              : {k_min} .. {k_max}")
    print()
    print("  aggregate pass@k  (mean ± std across prompts):")
    for k, r, s in zip(k_values,
                        agg.get("passk_rates", []),
                        agg.get("passk_stds",  [])):
        bar_len = max(0, int(r * 30))
        bar     = "█" * bar_len + "░" * (30 - bar_len)
        print(f"    pass@{k:>2}:  {r * 100:5.1f}% ± {s * 100:4.1f}%  [{bar}]")
    print()
    print(f"  per-prompt  pass@{k_min}  vs  pass@{k_max}:")
    pid_list = sorted(per_prompt.keys(), key=lambda x: int(x))
    for pid in pid_list:
        data   = per_prompt[pid]
        rates  = data["passk_rates"]
        cat    = data["category"][:26]
        r1     = rates[0]  * 100
        rk     = rates[-1] * 100
        print(f"    #{int(pid):>2}  [{cat:<26}]  "
              f"c/n = {data['n_correct']}/{data['n_samples']}   "
              f"pass@{k_min} = {r1:5.1f}%   "
              f"pass@{k_max} = {rk:5.1f}%   "
              f"uplift = +{rk - r1:.1f} pp")




def print_pattern_report(payload: Dict) -> None:
    """Textual summary of the bottom-line numbers (multi-trial)."""
    trials   = payload.get("trials", [])
    agg      = payload.get("aggregate", {})
    counters = payload.get("counters", {})
    config   = payload.get("config", {})
    if not trials:
        print("No trials to report.")
        return

    n_trials  = config.get("trials", len(trials))
    n_prompts = config.get("n_prompts", len(trials[0]["results"]))

    print("\n=========================================================")
    print(" Bottom-line numbers")
    print("=========================================================")
    print(f"  trials run                  : {n_trials}")
    print(f"  prompts per trial           : {n_prompts}")
    print(f"  prompt runs total           : {n_trials * n_prompts}")
    print(f"  LLM calls total             : {counters.get('llm_calls_total', 0)}")
    print(f"    .. initial generations    : {n_trials * n_prompts}")
    print(f"    .. logic-repair calls     : {counters.get('logic_repair_calls', 0)}")
    print(f"    .. syntax-repair calls    : {counters.get('syntax_repair_calls', 0)}")
    print(f"    .. substance-repair calls : {counters.get('substance_repair_calls', 0)}")
    print(f"  Alloy invocations           : {counters.get('alloy_calls_total', 0)}")
    print()
    print(f"  NO-LOOP pass rate           : {agg['noloop_rate_mean']*100:.1f}% \u00b1 {agg['noloop_rate_std']*100:.1f}%")
    print(f"  WITH-LOOP pass rate         : {agg['withloop_rate_mean']*100:.1f}% \u00b1 {agg['withloop_rate_std']*100:.1f}%")
    print(f"  uplift                      : +{agg['uplift_mean']*100:.1f} pp")
    print(f"  mean iters among SAFE runs  : {agg['mean_iters_safe_mean']:.2f} \u00b1 {agg['mean_iters_safe_std']:.2f}")
    print()
    print("  per-trial NO-LOOP / WITH-LOOP rates:")
    for trial in trials:
        s = trial["trial_summary"]
        print(f"    trial {trial['trial_id']}: "
              f"NO-LOOP {s['noloop_safe']}/{s['n']}  "
              f"WITH-LOOP {s['withloop_safe']}/{s['n']}  "
              f"(mean iters {s['mean_iters_safe']:.2f})")
    print()
    print("  per-prompt WITH-LOOP success across trials:")
    for p in agg.get("per_prompt", []):
        stat_mix = {}
        for s in p["final_statuses"]:
            stat_mix[s] = stat_mix.get(s, 0) + 1
        statuses = ", ".join(f"{k}\u00d7{v}" for k, v in stat_mix.items())
        print(f"    #{p['id']:>2} [{p['category']:>22}] "
              f"NO-LOOP {p['trial_passes_noloop']}/{p['trials']}  "
              f"WITH-LOOP {p['trial_passes_withloop']}/{p['trials']}  "
              f"iters {p['iters_mean']:.1f}\u00b1{p['iters_std']:.1f}  "
              f"[{statuses}]")


# =============================================================================
# 10. Entry point
# =============================================================================

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])

    # Main experiment.
    parser.add_argument("--trials", type=int, default=10,
                        help="number of independent trials of the 10-prompt "
                             "benchmark (default 10). Each trial uses a fresh "
                             "LLM roll-out, so we can quantify variance.")
    parser.add_argument("--max-iters", type=int, default=MAX_ITERATIONS_DEFAULT,
                        help="maximum repair iterations per prompt. Set to 1 "
                             "to measure pure NO-LOOP baseline.")
    parser.add_argument("--scope", type=str, default=ALLOY_SCOPE_DEFAULT,
                        help="Alloy scope (e.g. 'for 5 but 9 Int')")
    parser.add_argument("--prompts", type=str, default=PROMPTS_FILE,
                        help="path to prompts JSON")
    parser.add_argument("--dry-run", action="store_true",
                        help="use mock LLM and mock Alloy (no API / no JVM)")
    parser.add_argument("--plot-only", action="store_true",
                        help="skip the experiment; just re-plot from existing log")
    parser.add_argument("--seed", type=int, default=0)

    # pass@k experiment.
    parser.add_argument("--run-passk", action="store_true",
                        help="compute loop and pass@k results from the same trials")
    parser.add_argument("--passk-only", action="store_true",
                        help="generate only independent initial plans for pass@k")
    parser.add_argument("--passk-n", type=int, default=10,
                        help="number of independent samples (repetitions) per "
                             "prompt = n in pass@k (default 10)")
    parser.add_argument("--passk-kmax", type=int, default=10,
                        help="highest k to evaluate in the pass@k experiment "
                             "(default 10; evaluates pass@1 … pass@k_max, "
                             "capped at n because pass@k requires n >= k)")
    parser.add_argument("--passk-plot-only", action="store_true",
                        help="skip the pass@k experiment; re-score the existing "
                             "pass@k log under the current definition and re-plot")
    args = parser.parse_args()

    random.seed(args.seed)

    # ------------------------------------------------------------------ shortcuts
    if args.plot_only:
        if not os.path.exists(LOG_FILE):
            print(f"log file {LOG_FILE} not found; cannot plot.", file=sys.stderr)
            return 1
        payload = _load_log()
        plot_results(payload)
        print_pattern_report(payload)
        return 0

    if args.passk_plot_only:
        if not os.path.exists(PASSK_LOG_FILE):
            print(f"pass@k log {PASSK_LOG_FILE} not found; cannot plot.",
                  file=sys.stderr)
            return 1
        with open(PASSK_LOG_FILE, "r", encoding="utf-8") as f:
            pk_payload = json.load(f)
        # Re-score the stored raw traces under the current pass@k definition so
        # a log captured earlier does not need a fresh (paid) experiment run.
        pk_payload = recompute_passk_payload(pk_payload)
        with open(PASSK_LOG_FILE, "w", encoding="utf-8") as f:
            json.dump(pk_payload, f, indent=2, ensure_ascii=False)
        plot_passk_results(pk_payload)
        print_passk_report(pk_payload)
        return 0

    # --------------------------------------------------------------- load prompts
    with open(args.prompts, "r", encoding="utf-8") as f:
        prompts = json.load(f).get("prompts", [])
    if not prompts:
        print(f"no prompts found in {args.prompts}", file=sys.stderr)
        return 2

    issues = preflight(dry_run=args.dry_run)
    if issues:
        print("=" * 72, file=sys.stderr)
        print(" Preflight failed -- the experiment cannot run as configured.", file=sys.stderr)
        print(" (Re-run with --dry-run to use mocks and skip these checks.)", file=sys.stderr)
        print("=" * 72, file=sys.stderr)
        for i, msg in enumerate(issues, 1):
            print(f"  [{i}] {msg}", file=sys.stderr)
        print("=" * 72, file=sys.stderr)
        return 3

    if args.passk_only:
        pk_payload = run_passk_experiment(
            prompts,
            n=args.passk_n,
            k_max=args.passk_kmax,
            scope=args.scope,
            dry_run=args.dry_run,
        )
        plot_passk_results(pk_payload)
        print_passk_report(pk_payload)
        print(f"\npass@k log: {PASSK_LOG_FILE}")

    elif args.run_passk:
        print("\n" + "=" * 72)
        print(f" Unified experiment  "
              f"(n={args.passk_n},  k_max={args.passk_kmax},  "
              f"max_iters={args.max_iters})")
        print(" Shared trials -> no-loop/with-loop metrics + pass@k")
        print("=" * 72)
        payload, pk_payload = run_unified_experiment(
            prompts,
            trials=args.passk_n,
            max_iters=args.max_iters,
            k_max=args.passk_kmax,
            scope=args.scope,
            dry_run=args.dry_run,
        )
        _save_csv(payload)
        _save_log(payload, dry_run=args.dry_run)
        plot_results(payload)
        print_pattern_report(payload)
        print(f"\nlog:  {LOG_FILE}")
        print(f"csv:  {CSV_FILE}")
        print(f"plot: {PLOT_FILE}")
        plot_passk_results(pk_payload)
        print_passk_report(pk_payload)
        print(f"\npass@k log:  {PASSK_LOG_FILE}")
        print("pass@k plots:")
        for path in PASSK_PLOT_FILES:
            print(f"  {path}")
        print("pass@k PGF plots:")
        for path in PASSK_PGF_FILES:
            print(f"  {path}")

    else:
        payload = run_experiment(
            prompts,
            trials=args.trials,
            max_iters=args.max_iters,
            scope=args.scope,
            dry_run=args.dry_run,
        )
        _save_csv(payload)
        _save_log(payload, dry_run=args.dry_run)
        plot_results(payload)
        print_pattern_report(payload)
        print(f"\nlog:  {LOG_FILE}")
        print(f"csv:  {CSV_FILE}")
        print(f"plot: {PLOT_FILE}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
