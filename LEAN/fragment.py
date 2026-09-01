"""Check the outer shape and obvious placeholders in one generated Lean definition."""

from __future__ import annotations

import re


# there should be only one def and that name must be rule, and oversimplified answers are rejected like sorry
def check_def_shape(source: str) -> tuple[bool, str]:
    command = re.compile(
        r"(?:import|open|namespace|section|end|variable|include|omit|universe|"
        r"set_option|attribute|local|scoped|syntax|macro|elab|command_elab|"
        r"inductive|structure|class|def|abbrev|opaque|axiom|theorem|lemma|"
        r"example|instance|mutual|#\S+)\b"
    )
    source_without_blocks = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    code_lines: list[str] = []
    first_code = ""
    top_level_commands: list[str] = []

    for raw in source_without_blocks.splitlines():
        code = raw.split("--", 1)[0].rstrip()
        if not code.strip():
            continue
        code_lines.append(code)
        if not first_code:
            first_code = code.strip()
        if code == code.lstrip() and command.match(code):
            top_level_commands.append(code)

    if not re.match(r"^def\s+rule\b", first_code):
        return False, "expected the generated code to start with `def rule`"
    if len(top_level_commands) != 1 or not re.match(
        r"^def\s+rule\b", top_level_commands[0]
    ):
        return False, "expected exactly one top-level declaration: `def rule`"

    normalized = "\n".join(code_lines)
    if re.search(r"\b(?:sorry|admit)\b|\?_[A-Za-z0-9_']*", normalized):
        return False, "`def rule` may not contain `sorry`, `admit`, or metavariable holes"

    _, assignment, body = normalized.partition(":=")
    if assignment:
        compact_body = " ".join(body.split()).strip()
        while compact_body.startswith("(") and compact_body.endswith(")"):
            compact_body = compact_body[1:-1].strip()
        constant = re.fullmatch(
            r"(?:by\s+exact\s+)?\(?\s*(True|False)\s*\)?",
            compact_body,
        )
        if constant:
            return False, f"`def rule` may not be the constant proposition `{constant.group(1)}`"
    return True, ""
