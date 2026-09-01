"""Run the real-scenario inquiries through the pipeline, recording the run.

Same shape as run_all.py, pointed at the real-scenario experiment: the rewritten
vocabularies in vocab_real_scenario/ and the stages in stages_real_scenario/. Neither
the original vocab/ nor the original stages/ is touched.

    python run_all_real_scenario.py                 # every stage, in order
    python run_all_real_scenario.py --only CH-001   # one stage
    python run_all_real_scenario.py --skip-done     # only stages with no result yet
"""

from __future__ import annotations

import argparse
import contextlib
import sys
from datetime import datetime
from pathlib import Path

from inquiry import inquire
from pipeline import LLM, PipelineError, ROOT, Settings, lean_available, load_vocabulary


VOCABULARIES = {"CH": "choking", "CPR": "cpr", "DR": "drowning"}
VOCAB_DIR = ROOT / "vocab_real_scenario"
STAGE_DIR = ROOT / "stages_real_scenario"
RECORD = ROOT / "record_real_scenario.txt"


class Tee:
    """Write to the terminal and to the record at once."""

    def __init__(self, stream, record) -> None:
        self.stream = stream
        self.record = record

    def write(self, text: str) -> int:
        self.record.write(text)
        return self.stream.write(text)

    def flush(self) -> None:
        self.stream.flush()
        self.record.flush()


def selected(arguments) -> list[Path]:
    stages = sorted(d for d in STAGE_DIR.iterdir() if d.is_dir())
    if arguments.only:
        wanted = set(arguments.only)
        stages = [d for d in stages if d.name in wanted]
        missing = wanted - {d.name for d in stages}
        if missing:
            raise PipelineError(f"no such stage: {', '.join(sorted(missing))}")
    if arguments.skip_done:
        stages = [d for d in stages if not (d / "x_prime.txt").exists()]
    return stages


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", nargs="+", default=[], help="stage ids, e.g. CH-001")
    parser.add_argument("--skip-done", action="store_true", help="skip stages already run")
    arguments = parser.parse_args(argv)

    if not lean_available():
        print("Lean is not available", file=sys.stderr)
        return 2

    settings = Settings()
    try:
        vocabularies = {
            prefix: load_vocabulary(VOCAB_DIR / f"{name}.lean")
            for prefix, name in VOCABULARIES.items()
        }
        stages = selected(arguments)
        client = LLM(settings.model)
    except PipelineError as error:
        print(str(error), file=sys.stderr)
        return 2

    with RECORD.open("a", encoding="utf-8") as record, contextlib.redirect_stdout(
        Tee(sys.stdout, record)
    ):
        print(f"\n\n########## run {datetime.now():%Y-%m-%d %H:%M:%S} ##########", flush=True)
        print(f"vocab: {VOCAB_DIR.name}  stages: {STAGE_DIR.name}  n: {len(stages)}", flush=True)

        for stage_dir in stages:
            prefix = stage_dir.name.partition("-")[0]
            if prefix not in vocabularies:
                continue

            print(f"\n{'=' * 70}", flush=True)
            print(stage_dir.name, flush=True)
            print("=" * 70, flush=True)
            try:
                inquiry, formal, drift = inquire(
                    (stage_dir / "x.txt").read_text(encoding="utf-8"),
                    vocabularies[prefix],
                    stage_dir,
                    settings,
                    client,
                )
            except PipelineError as error:
                print(f"\n[FAILED]\n{error}", flush=True)
                continue

            print("\n[INQUIRY]", flush=True)
            print(inquiry, flush=True)
            print("\n[FORMAL]", flush=True)
            print(formal or "none", flush=True)
            print("\n[DRIFT]", flush=True)
            print("unavailable" if drift is None else str(drift).lower(), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
