"""x_original           human/semi-automatic workflow -> define vocab/declaration that all lean file should use.
    |
 (by calling llm and check return code is valid (ignored over-simplified answer and lean typecheck/compile))
    |
    y_original.lean
    |
 (deformalized in to natual language)
    |
    x'
 (by calling llm and check return code is valid(ignored over-simplified answer and lean typecheck/compile))
    |
    y_prime.lean

check if y_original <-> y_prime.lean by equivalence.py
    |                                   |
    if yes, proceed NLI check.          if no do stage diagnose, call llm locate file, update the file, and update following stages
"""

from __future__ import annotations

import argparse
import os
import random
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

import equivalence
from fragment import check_def_shape
from nli.compare import compare as compare_nli


ROOT = Path(__file__).resolve().parent
DEFAULT_MODEL = "deepseek-chat"
DEFAULT_BASE_URL = "https://api.deepseek.com"


@dataclass
class Settings:
    model: str = DEFAULT_MODEL
    judge_model: str = ""
    temperature: float = 0.1
    judge_temperature: float = 0.0
    max_tokens: int = 2000
    max_rounds: int = 3
    max_compile_attempts: int = 5
    max_diagnosis_attempts: int = 3
    lean_timeout: int = 120
    run_nli: bool = True
    nli_model: str = "facebook/bart-large-mnli"


class PipelineError(RuntimeError):
    pass


@dataclass(frozen=True)
class Vocabulary:
    source: str
    struct: str


@dataclass
class State:
    original_rule: str
    reconstructed: str
    prime_rule: str
    vocabulary: Vocabulary


@dataclass
class Diagnosis:
    stage: str
    reason: str = ""
    hint: str = ""
    confidence: float = 0.0


# main
def run(
    original: str,
    vocabulary: Vocabulary,
    stage_dir: Path,
    settings: Settings,
    client: LLM,
) -> bool:
    stage_dir.mkdir(parents=True, exist_ok=True)
    (stage_dir / "lakefile.toml").write_text(
        """name = "tptl_stage"
version = "0.1.0"
defaultTargets = ["Stage"]

[[lean_lib]]
name = "Stage"
roots = ["Vocab", "YOriginal", "YPrime", "Equivalence"]
""",
        encoding="utf-8",
    )
    toolchain_path = ROOT.parent / "lean-toolchain"
    if toolchain_path.exists():
        (stage_dir / "lean-toolchain").write_text(
            toolchain_path.read_text(encoding="utf-8"), encoding="utf-8"
        )
    original = original.strip() + "\n"
    (stage_dir / "x.txt").write_text(original, encoding="utf-8")
    print("[X ORIGINAL]", flush=True)
    print(original.strip(), flush=True)

    vocab_ok, vocab_error = typecheck(
        vocabulary.source, stage_dir / "Vocab.lean", settings.lean_timeout
    )
    print("\n[VOCAB RETURN]", flush=True)
    print(f"typecheck: {str(vocab_ok).lower()}", flush=True)
    if not vocab_ok:
        print(vocab_error, flush=True)
        print("\n[PIPELINE RETURN]\nfalse", flush=True)
        return False

    original_rule = formalize(
        client, settings, vocabulary, original, stage_dir,
        stage="S1", module_name="YOriginal",
    )
    if original_rule is None:
        print("\n[PIPELINE RETURN]\nfalse", flush=True)
        return False

    reconstructed = deformalize(
        client, settings, vocabulary, original_rule, stage_dir
    )
    if reconstructed is None:
        print("\n[PIPELINE RETURN]\nfalse", flush=True)
        return False

    prime_rule = formalize(
        client, settings, vocabulary, reconstructed, stage_dir,
        stage="S3", module_name="YPrime",
    )
    if prime_rule is None:
        print("\n[PIPELINE RETURN]\nfalse", flush=True)
        return False

    state = State(original_rule, reconstructed, prime_rule, vocabulary)
    equivalent, evidence = check_equivalence(stage_dir, settings.lean_timeout)

    for round_number in range(1, settings.max_rounds + 1):
        if equivalent:
            break
        diagnosis = diagnose(client, settings, original, state, evidence)
        print(f"\n[DIAGNOSIS RETURN round {round_number}]", flush=True)
        print(f"stage: {diagnosis.stage}", flush=True)
        print(f"reason: {diagnosis.reason}", flush=True)
        print(f"hint: {diagnosis.hint}", flush=True)
        print(f"confidence: {diagnosis.confidence}", flush=True)

        print(f"\n[REPAIR round {round_number}: {diagnosis.stage}]", flush=True)
        updated = repair(client, settings, original, state, diagnosis, stage_dir)
        print(f"[REPAIR RETURN]\n{str(updated is not None).lower()}", flush=True)
        if updated is None:
            break
        state = updated
        equivalent, evidence = check_equivalence(stage_dir, settings.lean_timeout)

    print("\n[NLI RETURN]", flush=True)
    if not settings.run_nli:
        print("disabled", flush=True)
    else:
        semantic = compare_nli(original, state.reconstructed, settings.nli_model)
        if semantic.get("available"):
            print(f"category: {semantic.get('category')}", flush=True)
            print(f"drift: {str(semantic.get('drift')).lower()}", flush=True)
        else:
            print(f"unavailable: {semantic.get('note')}", flush=True)

    print("\n[PIPELINE RETURN]", flush=True)
    print(str(equivalent).lower(), flush=True)
    return equivalent


def formalize(
    client: LLM,
    settings: Settings,
    vocabulary: Vocabulary,
    specification: str,
    stage_dir: Path,
    *,
    stage: str,
    module_name: str,
    repair_prompt: str = "",
) -> str | None:
    system = f"""Translate the supplied text into one Lean 4 proposition over the
supplied fixed vocabulary. Return exactly:
```lean
def rule (c : {vocabulary.struct}) : Prop :=
  ...
```
Translate only what the text says: state every fact it states and nothing else, and
leave any field the text does not mention unconstrained. Preserve every condition,
exception, threshold, and implication direction. Do not repeat or define vocabulary
declarations. Reply with one Lean block only."""
    prompt = repair_prompt or f"""Formalize this text:

{specification.strip()}

Fixed vocabulary:
```lean
{vocabulary.source.strip()}
```"""

    for attempt in range(1, settings.max_compile_attempts + 1):
        reply = client.complete(
            system,
            prompt,
            temperature=settings.temperature,
            max_tokens=settings.max_tokens,
        )
        model_code = reply.strip()
        if "```" in model_code:
            chunks = model_code.split("```")
            model_code = chunks[1].partition("\n")[2].strip() or chunks[1].strip()

        shape_ok, error = check_def_shape(model_code)
        print(f"\n[{stage} DEF SHAPE attempt {attempt}]", flush=True)
        print(f"shape: {str(shape_ok).lower()}", flush=True)
        if not shape_ok:
            print(f"rejected: {error}", flush=True)
        else:
            rule = model_code.strip()
            source = f"""import Vocab

namespace {module_name}
{rule}

example : {vocabulary.struct} → Prop := rule
end {module_name}
"""
            typecheck_ok, error = typecheck(
                source, stage_dir / f"{module_name}.lean", settings.lean_timeout
            )
            print(f"typecheck: {str(typecheck_ok).lower()}", flush=True)
            if typecheck_ok:
                print(f"\n[{stage} RETURN]", flush=True)
                print(rule, flush=True)
                return rule
            print(f"rejected: {error}", flush=True)

        prompt = f"""Correct this rejected Lean rule without changing its intended meaning.

Text:
{specification.strip()}

Fixed vocabulary:
```lean
{vocabulary.source.strip()}
```

Rejected code:
```lean
{model_code}
```

Error:
{error}

Return the complete corrected `def rule` only."""

    print(f"\n[{stage} RETURN]\nfalse", flush=True)
    return None


DEFORMALIZE_SYSTEM = """Read the supplied formal statement and say the same thing
in ordinary language. Mirror its logical structure exactly: a conjunction is "and",
a disjunction is "or", an implication is "if ... then", a negation is "not". Never
turn one into another; in particular, never restate a conjunction as a conditional.
Preserve every condition, threshold, exception, and implication direction. Do not
mention Lean, code, types, fields, or identifiers. Add nothing the statement does
not say. Reply with plain prose."""


def deformalize(
    client: LLM,
    settings: Settings,
    vocabulary: Vocabulary,
    rule: str,
    stage_dir: Path,
    repair_prompt: str = "",
) -> str | None:
    reply = client.complete(
        DEFORMALIZE_SYSTEM,
        repair_prompt or f"""State the requirement expressed by this rule.

Fixed vocabulary:
```lean
{vocabulary.source.strip()}
```

Rule:
```lean
{rule.strip()}
```""",
        temperature=settings.temperature,
        max_tokens=settings.max_tokens,
    ).strip()
    if reply.startswith("```"):
        lines = reply.splitlines()[1:]
        if lines and lines[-1].strip().startswith("```"):
            lines.pop()
        reply = "\n".join(lines).strip()
    if not reply:
        print("\n[S2 RETURN]\nfalse", flush=True)
        return None
    (stage_dir / "x_prime.txt").write_text(reply + "\n", encoding="utf-8")
    print("\n[S2 RETURN]", flush=True)
    print(reply, flush=True)
    return reply


def check_equivalence(
    stage_dir: Path,
    timeout: int,
) -> tuple[bool, str]:
    source = equivalence.theorem_source()
    equivalent, error = typecheck(source, stage_dir / "Equivalence.lean", timeout)
    evidence = (
        "Lean proved `∀ c, YOriginal.rule c ↔ YPrime.rule c`."
        if equivalent
        else "Lean did not accept the equivalence theorem.\n" + error
    ).strip()
    print("\n[EQUIVALENCE RETURN]", flush=True)
    print(f"typecheck: {str(equivalent).lower()}", flush=True)
    print(f"equivalent: {str(equivalent).lower()}", flush=True)
    print(evidence.splitlines()[0], flush=True)
    return equivalent, evidence


DIAGNOSE_SYSTEM = """Audit this translation pipeline:
S1: original natural language -> original Lean rule
S2: original Lean rule -> reconstructed natural language
S3: reconstructed natural language -> roundtrip Lean rule

Weigh all three stages together, then report the one that lost the meaning. Do not
walk through them in order and do not settle on the first stage that looks
imperfect: a stage is the culprit only if repairing that stage alone would remove
the disagreement. The fix hint may mention only adjacent artifacts: S1 uses
x/y_original, S2 uses y_original/x_prime, and S3 uses x_prime/y_prime. Return
exactly four plain-text lines:
STAGE: S1|S2|S3
ROOT_CAUSE: ...
SCOPED_FIX_HINT: ...
CONFIDENCE: 0.0"""


def diagnose(
    client: LLM,
    settings: Settings,
    original: str,
    state: State,
    evidence: str,
) -> Diagnosis:
    prompt = f"""x:
{original.strip()}

y_original:
```lean
{state.original_rule}
```

x_prime:
{state.reconstructed}

y_prime:
```lean
{state.prime_rule}
```

Fixed vocabulary:
```lean
{state.vocabulary.source.strip()}
```

Formal evidence:
{evidence}"""
    for _ in range(settings.max_diagnosis_attempts):
        reply = client.complete(
            DIAGNOSE_SYSTEM,
            prompt,
            temperature=settings.judge_temperature,
            max_tokens=settings.max_tokens,
            model=settings.judge_model or settings.model,
        )
        fields: dict[str, str] = {}
        for line in reply.splitlines():
            key, separator, value = line.partition(":")
            if separator:
                fields[key.strip().upper()] = value.strip()
        stage = fields.get("STAGE", "").upper()
        if stage not in {"S1", "S2", "S3"}:
            continue
        try:
            confidence = max(0.0, min(1.0, float(fields.get("CONFIDENCE", "0"))))
        except ValueError:
            confidence = 0.0
        return Diagnosis(
            stage,
            fields.get("ROOT_CAUSE", ""),
            fields.get("SCOPED_FIX_HINT", ""),
            confidence,
        )
    return Diagnosis("UNKNOWN")


def repair(
    client: LLM,
    settings: Settings,
    original: str,
    state: State,
    diagnosis: Diagnosis,
    stage_dir: Path,
) -> State | None:
    vocabulary = state.vocabulary
    feedback = " ".join(part for part in (diagnosis.reason, diagnosis.hint) if part)

    if diagnosis.stage not in {"S1", "S2", "S3"}:
        diagnosis = Diagnosis("S1", "diagnosis unavailable", "regenerate carefully", 0.0)
        feedback = "diagnosis unavailable; regenerate carefully"

    original_rule = state.original_rule
    reconstructed = state.reconstructed

    if diagnosis.stage == "S1":
        s1_prompt = f"""Repair S1 only.
x:
{original.strip()}
y_original:
{state.original_rule}
diagnosis:
{feedback}
vocabulary:
{vocabulary.source.strip()}
Return only the corrected `def rule`."""
        original_rule = formalize(
            client, settings, vocabulary, original, stage_dir,
            stage="S1", module_name="YOriginal", repair_prompt=s1_prompt,
        )
        if original_rule is None:
            return None

    s2_prompt = ""
    if diagnosis.stage == "S2":
        s2_prompt = f"""Repair S2 only.
y_original:
{state.original_rule}
x_prime:
{state.reconstructed}
diagnosis:
{feedback}
vocabulary:
{vocabulary.source.strip()}
Return only the corrected plain-language requirement."""

    if diagnosis.stage in {"S1", "S2"}:
        reconstructed = deformalize(
            client,
            settings,
            vocabulary,
            original_rule,
            stage_dir,
            repair_prompt=s2_prompt,
        )
        if reconstructed is None:
            return None

    s3_prompt = ""
    if diagnosis.stage == "S3":
        s3_prompt = f"""Repair S3 only.
x_prime:
{state.reconstructed}
y_prime:
{state.prime_rule}
diagnosis:
{feedback}
vocabulary:
{vocabulary.source.strip()}
Return only the corrected `def rule`."""

    prime_rule = formalize(
        client, settings, vocabulary, reconstructed, stage_dir,
        stage="S3", module_name="YPrime", repair_prompt=s3_prompt,
    )
    return State(original_rule, reconstructed, prime_rule, vocabulary) if prime_rule else None


def lean_available() -> bool:
    return shutil.which("lean") is not None


def typecheck(source: str, path: Path, timeout: int = 120) -> tuple[bool, str]:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    if not lean_available():
        return False, "Lean executable is not available"
    olean = path.with_suffix(".olean")
    olean.unlink(missing_ok=True)
    lean_environment = os.environ.copy()
    local_path = str(path.parent.resolve())
    existing_path = lean_environment.get("LEAN_PATH", "")
    lean_environment["LEAN_PATH"] = (
        local_path + os.pathsep + existing_path if existing_path else local_path
    )
    try:
        process = subprocess.run(
            ["lean", "-o", olean.name, path.name],
            cwd=str(path.parent),
            capture_output=True,
            text=True,
            timeout=timeout,
            env=lean_environment,
        )
    except subprocess.TimeoutExpired:
        return False, f"Lean timed out after {timeout}s"
    output = "\n".join(
        part.strip() for part in (process.stdout, process.stderr) if part.strip()
    )
    return process.returncode == 0, output


def load_vocabulary(path: str | Path) -> Vocabulary:
    source_path = Path(path)
    source = source_path.read_text(encoding="utf-8")
    structures = re.findall(
        r"(?m)^structure\s+([A-Za-z_][A-Za-z0-9_']*)"
        r"(?:\s+extends\s+.*?)?\s+where\s*$",
        source,
    )
    if len(structures) != 1:
        raise PipelineError("vocabulary must contain exactly one context structure")
    return Vocabulary(source.strip() + "\n", structures[0])


@dataclass
class LLM:
    model: str
    api_key: str = ""
    base_url: str = ""

    def __post_init__(self) -> None:
        from openai import OpenAI

        self.api_key = (
            self.api_key
            or os.environ.get("ROUNDTRIP_API_KEY", "")
            or os.environ.get("DEEPSEEK_API_KEY", "")
            or os.environ.get("OPENAI_API_KEY", "")
        ).strip()
        if not self.api_key:
            raise PipelineError(
                "set ROUNDTRIP_API_KEY, DEEPSEEK_API_KEY, or OPENAI_API_KEY"
            )
        self.base_url = (
            self.base_url
            or os.environ.get("ROUNDTRIP_BASE_URL", "")
            or os.environ.get("DEEPSEEK_BASE_URL", "")
            or os.environ.get("OPENAI_BASE_URL", "")
            or DEFAULT_BASE_URL
        ).strip()
        self.client = OpenAI(api_key=self.api_key, base_url=self.base_url, timeout=180)

    def complete(
        self,
        system: str,
        user: str,
        *,
        temperature: float,
        max_tokens: int,
        model: str | None = None,
    ) -> str:
        import openai

        selected_model = model or self.model
        parameters: dict = {
            "model": selected_model,
            "messages": [
                {"role": "system", "content": system},
                {"role": "user", "content": user},
            ],
            "max_tokens": max_tokens,
        }
        if "reasoner" not in selected_model:
            parameters["temperature"] = temperature

        transient = (
            openai.RateLimitError,
            openai.APIConnectionError,
            openai.APITimeoutError,
            openai.InternalServerError,
        )
        response = None
        last_error: Exception | None = None
        for attempt in range(5):
            try:
                response = self.client.chat.completions.create(**parameters)
                break
            except transient as error:
                last_error = error
                time.sleep(min(2**attempt, 30) + random.random())
            except openai.APIStatusError as error:
                raise PipelineError(
                    f"{selected_model} rejected the request: HTTP {error.status_code}"
                ) from error
        if response is None:
            raise PipelineError(f"{selected_model} failed after retries: {last_error}")
        text = (response.choices[0].message.content or "").strip()
        if not text:
            raise PipelineError(f"{selected_model} returned an empty response")
        return text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Lean roundtrip verification and scoped repair")
    parser.add_argument("input", help="path to the original x text")
    parser.add_argument("-v", "--vocab", required=True, help="hand-written Lean vocabulary")
    parser.add_argument("--stage-dir", default="", help="directory for all stage artifacts")
    parser.add_argument("--model", default=DEFAULT_MODEL)
    parser.add_argument("--judge-model", default="")
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--no-nli", action="store_true")
    arguments = parser.parse_args(argv)

    input_path = Path(arguments.input)
    vocabulary_path = Path(arguments.vocab)
    if not input_path.exists() or not vocabulary_path.exists():
        parser.error("input and vocabulary files must exist")
    if not lean_available():
        print("Lean is not available", file=sys.stderr)
        return 2
    try:
        vocabulary = load_vocabulary(vocabulary_path)
        settings = Settings(
            model=arguments.model,
            judge_model=arguments.judge_model,
            max_rounds=arguments.rounds,
            run_nli=not arguments.no_nli,
        )
        client = LLM(settings.model)
    except PipelineError as error:
        print(str(error), file=sys.stderr)
        return 2

    stage_dir = Path(arguments.stage_dir) if arguments.stage_dir else (
        input_path.parent if input_path.name == "x.txt" else ROOT / "stages" / input_path.stem
    )
    try:
        equivalent = run(
            input_path.read_text(encoding="utf-8"),
            vocabulary,
            stage_dir,
            settings,
            client,
        )
    except PipelineError as error:
        print(str(error), file=sys.stderr)
        return 2
    return 0 if equivalent else 1


if __name__ == "__main__":
    raise SystemExit(main())
