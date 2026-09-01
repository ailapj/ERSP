"""One user inquiry in; the inquiry unchanged, the Lean the pipeline formalized
it to, and whether a readback of that Lean still says what the inquiry said."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from nli.compare import compare as compare_nli
from pipeline import (
    DEFAULT_MODEL,
    LLM,
    PipelineError,
    ROOT,
    Settings,
    Vocabulary,
    lean_available,
    load_vocabulary,
    run,
)


def inquire(
    text: str,
    vocabulary: Vocabulary,
    stage_dir: Path,
    settings: Settings,
    client: LLM,
) -> tuple[str, str, bool | None]:
    run(text, vocabulary, stage_dir, settings, client)
    formal = stage_dir / "YOriginal.lean"
    reconstructed = stage_dir / "x_prime.txt"
    # Both sides are stripped: whether a side carries a trailing newline depends on
    # whether it came from a prompt or from a file, and the entailment scores sit
    # close enough to the category thresholds for that alone to flip the verdict.
    semantic = (
        compare_nli(
            text.strip(),
            reconstructed.read_text(encoding="utf-8").strip(),
            settings.nli_model,
        )
        if reconstructed.exists()
        else {}
    )
    return (
        text.strip(),
        formal.read_text(encoding="utf-8").strip() if formal.exists() else "",
        semantic.get("drift"),
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run one user inquiry through the pipeline")
    parser.add_argument("inquiry", help="the user inquiry, or a path to a file holding it")
    parser.add_argument("-v", "--vocab", required=True, help="hand-written Lean vocabulary")
    parser.add_argument("--stage-dir", default="", help="directory for all stage artifacts")
    parser.add_argument("--model", default=DEFAULT_MODEL)
    arguments = parser.parse_args(argv)

    vocabulary_path = Path(arguments.vocab)
    if not vocabulary_path.exists():
        parser.error("vocabulary file must exist")
    if not lean_available():
        print("Lean is not available", file=sys.stderr)
        return 2

    inquiry_path = Path(arguments.inquiry)
    text = (
        inquiry_path.read_text(encoding="utf-8")
        if inquiry_path.exists()
        else arguments.inquiry
    )
    stage_dir = Path(arguments.stage_dir) if arguments.stage_dir else (
        ROOT / "stages" / (inquiry_path.stem if inquiry_path.exists() else "inquiry")
    )

    try:
        settings = Settings(model=arguments.model)
        inquiry, formal, drift = inquire(
            text,
            load_vocabulary(vocabulary_path),
            stage_dir,
            settings,
            LLM(settings.model),
        )
    except PipelineError as error:
        print(str(error), file=sys.stderr)
        return 2

    print("\n[INQUIRY]", flush=True)
    print(inquiry, flush=True)
    print("\n[FORMAL]", flush=True)
    print(formal or "none", flush=True)
    print("\n[DRIFT]", flush=True)
    print("unavailable" if drift is None else str(drift).lower(), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
