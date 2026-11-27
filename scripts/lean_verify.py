"""Verify the axiom policy and the source-level proof policy."""

import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
IMPORTS = (
    "Erdos504Formal",
    "Erdos504Formal.Erdos504SendovN3",
    "Erdos504Formal.Erdos504SendovSe95Bridge",
)
THEOREMS = (
    "Erdos504.erdos_504",
    "Erdos504.erdos_504_endpoint_of_card_le",
    "Erdos504.sendov_counting_bound_n3",
    "Erdos504.SendovStage1.Se95Bridge.four_perfect_counterexample",
    "Erdos504.SendovStage1.Se95Bridge.five_perfect_counterexample",
    "Erdos504.SendovStage1.Se95Bridge.six_perfect_counterexample",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_REPORT = re.compile(
    r"^'(?P<theorem>[^'\r\n]+)' "
    r"(?:depends on axioms:\s*\[(?P<axioms>[^]]*)\]|does not depend on any axioms)"
    r"[ \t]*$",
    re.MULTILINE,
)

FORBIDDEN = re.compile(
    r"(?<![\w'])(?:sorry|admit|sorryAx|native_decide|ofReduceBool|trustCompiler)(?![\w'])"
)
CHALLENGE_HOLE = re.compile(
    r"^theorem (erdos_504(?:_endpoint)?)(?=[ \t\n])(?:(?!^[^ \t\n]).)*?"
    r":=[ \t]*by[ \t]*\n[ \t]+(?P<hole>sorry)[ \t]*$",
    re.MULTILINE | re.DOTALL,
)
LEXEME = re.compile(
    r"""--|/-|(?P<raw>(?<![\w'])r(?P<hashes>#*)")|"(?:[^"\\]|\\[\s\S])*"|«[^»]*»"""
)
BLOCK_MARK = re.compile(r"/-|-/")


def without_comments(source):
    """Mask comments, retaining line numbers and leaving literals visible."""
    buffer = list(source)
    position = 0
    while match := LEXEME.search(source, position):
        position = match.end()
        if match.group("raw") is not None:
            closing = '"' + match.group("hashes")
            end = source.find(closing, position)
            position = len(source) if end == -1 else end + len(closing)
            continue
        if match.group() == "--":
            end = source.find("\n", position)
            position = len(source) if end == -1 else end
        elif match.group() == "/-":
            depth = 1
            while depth:
                delimiter = BLOCK_MARK.search(source, position)
                if delimiter is None:
                    raise ValueError("unterminated block comment")
                depth += 1 if delimiter.group() == "/-" else -1
                position = delimiter.end()
        else:
            continue
        for index in range(match.start(), position):
            if buffer[index] != "\n":
                buffer[index] = " "
    return "".join(buffer)


def source_violations(source, source_name):
    source = without_comments(source)
    allowed_holes = set()
    if source_name == "Challenge.lean":
        used_names = set()
        for match in CHALLENGE_HOLE.finditer(source):
            if match[1] not in used_names:
                allowed_holes.add(match.start("hole"))
                used_names.add(match[1])

    return [
        (source.count("\n", 0, match.start()) + 1, match.group())
        for match in FORBIDDEN.finditer(source)
        if match.start() not in allowed_holes
    ]


def guard():
    sources = sorted((ROOT / "Erdos504Formal").rglob("*.lean"))
    sources += [ROOT / name for name in ("Erdos504Formal.lean", "Challenge.lean", "Solution.lean")]
    failed = False
    for path in sources:
        name = path.relative_to(ROOT).as_posix()
        try:
            violations = source_violations(path.read_text(encoding="utf-8"), name)
        except (OSError, ValueError) as error:
            print(f"{name}: {error}", file=sys.stderr)
            failed = True
            continue
        for line, token in violations:
            print(f"{name}:{line}: forbidden Lean token {token!r}", file=sys.stderr)
            failed = True
    if not failed:
        print(f"Source guard passed ({len(sources)} Lean files).")
    return int(failed)


def audit_violations(output):
    errors = []
    for axiom in ("sorryAx", "Lean.ofReduceBool"):
        if axiom in output:
            errors.append(f"Lean output contains {axiom}.")
    seen = set()
    for report in AUDIT_REPORT.finditer(output):
        theorem = report["theorem"]
        if theorem in seen or theorem not in THEOREMS:
            errors.append(f"Unexpected audit report for {theorem}.")
        seen.add(theorem)
        actual = {x.strip() for x in (report["axioms"] or "").split(",") if x.strip()}
        if unexpected := actual - ALLOWED_AXIOMS:
            errors.append(f"{theorem}: forbidden axioms {', '.join(sorted(unexpected))}.")
    for theorem in THEOREMS:
        if theorem not in seen:
            errors.append(f"Missing audit report for {theorem}.")
    return errors


def audit():
    commands = [
        *(f"import {module}" for module in IMPORTS),
        "",
        *(f"#print axioms {theorem}" for theorem in THEOREMS),
    ]
    with tempfile.TemporaryDirectory(prefix="lean-verify-") as tmp:
        source = Path(tmp) / "Audit.lean"
        source.write_text("\n".join(commands) + "\n", encoding="utf-8")
        print("Running lake env lean on the six axiom audit targets.", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", str(source)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            encoding="utf-8", check=False,
        )
    print(result.stdout, end="")
    if result.returncode:
        return result.returncode
    if errors := audit_violations(result.stdout):
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Axiom audit passed ({len(THEOREMS)} theorems).")
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("check", choices=("audit", "guard"))
    check = parser.parse_args().check
    raise SystemExit(audit() if check == "audit" else guard())
