#!/usr/bin/env python3
"""Check the complete OpenLogic source inventory and reviewer union.

This is intentionally a source-accounting check.  It verifies the pinned
checkout, include closure, one row per source file, and the reconciliation of
the two reviewer inventories.  It does not decide semantic equivalence.
"""

from __future__ import annotations

import collections
import csv
import re
import subprocess
from pathlib import Path


if not __debug__:
    raise SystemExit("check-book-coverage.py must run without python -O")


REPO = Path(__file__).resolve().parents[1]
SRC = REPO / "OpenLogic" / "content"
INVENTORY = REPO / "docs" / "book-coverage" / "inventory.tsv"
REVIEWERS = [
    REPO / "docs" / "book-coverage" / "foundations.tsv",
    REPO / "docs" / "book-coverage" / "logic.tsv",
]
PINNED = "1e960beff9ed7835bf3e3f1335e21af3439cd107"

INVENTORY_FIELDS = {
    "source_file",
    "source_root",
    "file_kind",
    "selection",
    "selected_roots",
    "direct_importers",
    "active_imports",
    "active_subfiles",
    "commented_subfiles",
    "direct_subfile_importers",
    "commented_imports",
    "substantive",
    "prose_words",
    "headings",
    "construct_counts",
    "labels",
    "named_items",
    "coverage_status",
    "coverage_basis",
    "formalolp_evidence",
    "formal_declarations",
    "audit_note",
}
REVIEWER_FIELDS = {
    "source_file",
    "source_root",
    "file_kind",
    "source_unit",
    "selection",
    "selected_roots",
    "direct_importers",
    "active_imports",
    "commented_imports",
    "substantive",
    "prose_words",
    "headings",
    "construct_counts",
    "labels",
    "named_items",
    "unit_start_line",
    "unit_end_line",
    "file_lines",
    "file_words",
    "coverage_status",
    "coverage_basis",
    "formalolp_evidence",
    "formal_declarations",
    "audit_note",
}
STATUS_MAP = {
    "proved_equivalent": "proved-equivalent",
    "proved-equivalent": "proved-equivalent",
    "proved_weaker": "partial/weaker",
    "partial-weaker": "partial/weaker",
    "defined_only": "definition/statement-only",
    "definition-only": "definition/statement-only",
    "dependency_only": "dependency-only",
    "dependency-only": "dependency-only",
    "structural_container": "structural-container",
    "structural-container": "structural-container",
    "non_formal_exposition": "non-formal-exposition",
    "non-formal-exposition": "non-formal-exposition",
    "missing": "missing",
}
FOUNDATION_UNIT_ENVS = (
    "defn", "defish", "prop", "thm", "lem", "cor", "axiom", "ex",
    "prob", "derivation", "conv",
)
LOGIC_UNIT_ENVS = ("defn", "prop", "prob", "ex", "thm", "lem", "cor")
DECLARATION_COUNTS = {
    "applied-modal-logic/epistemic-logic/properties-accessibility.tex": 1,
    "applied-modal-logic/epistemic-logic/truth-at-w.tex": 1,
    "counterfactuals/minimal-change-semantics/sphere-models.tex": 1,
    "counterfactuals/minimal-change-semantics/true-false.tex": 1,
    "first-order-logic/syntax-and-semantics/semantic-notions.tex": 4,
    "intuitionistic-logic/semantics/relational-models.tex": 1,
    "intuitionistic-logic/soundness-completeness/soundness-nd.tex": 1,
    "model-theory/basics/isomorphism.tex": 3,
    "many-valued-logic/three-valued-logics/kleene.tex": 1,
    "normal-modal-logic/frame-definability/properties-accessibility.tex": 1,
    "propositional-logic/syntax-and-semantics/semantic-notions.tex": 1,
    "propositional-logic/syntax-and-semantics/soundness.tex": 1,
    "propositional-logic/syntax-and-semantics/valuations-sat.tex": 1,
    "second-order-logic/syntax-and-semantics/satisfaction.tex": 1,
    "second-order-logic/syntax-and-semantics/semantic-notions.tex": 1,
}


def strip_comments(text: str) -> str:
    lines = []
    for line in text.splitlines():
        cut = next(
            (i for i, char in enumerate(line)
             if char == "%" and (i == 0 or line[i - 1] != "\\")),
            None,
        )
        lines.append(line if cut is None else line[:cut])
    return "\n".join(lines)


def relative(path: Path) -> str:
    return path.relative_to(SRC).as_posix()


def imports(path: Path, text: str) -> list[Path]:
    return [
        (path.parent / (directory or "") / (name + ".tex")).resolve()
        for directory, name in re.findall(
            r"\\olimport(?:\[([^]]+)\])?\{([^}]+)\}", text
        )
    ]


def subfiles(path: Path, text: str) -> list[Path]:
    return [
        (path.parent / (name + ".tex")).resolve()
        for name in re.findall(r"\\subfile\{([^}]+)\}", text)
    ]


def read_tsv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        rows = list(reader)
        assert reader.fieldnames is not None, path
        return reader.fieldnames, rows


def clean_evidence(value: str) -> str:
    if value == "-":
        return value
    return ";".join(piece.split(":", 1)[0] for piece in value.split(";"))


def expected_source_units(path: str, environment_names: tuple[str, ...],
                          global_numbering: bool) -> list[str]:
    """Reproduce the frozen reviewer unit identity rule from current TeX.

    Foundations uses one ordinal over its recognized unit environments and
    replaces that ordinal with the first ``ollabel`` when present. Logic uses
    an ordinal per environment and retains a label as a suffix. Both ledgers
    intentionally scan raw TeX, so commented unit environments remain in the
    source denominator.
    """
    text = (SRC / path).read_text(errors="replace")
    begin = re.compile(r"\\begin\s*\{\s*([^}]+?)\s*\}")
    starts = [
        (match.start(), match.end(), match.group(1))
        for match in begin.finditer(text)
        if match.group(1) in environment_names
    ]
    result = []
    per_environment: collections.Counter[str] = collections.Counter()
    for ordinal, (_, body_start, environment) in enumerate(starts, 1):
        end_environment = re.compile(
            r"\\(?:begin|end)\s*\{\s*" + re.escape(environment) + r"\s*\}"
        )
        depth = 0
        body_end = len(text)
        for match in end_environment.finditer(text, body_start):
            if match.group(0).lstrip().startswith(r"\begin"):
                depth += 1
            elif depth == 0:
                body_end = match.start()
                break
            else:
                depth -= 1
        label_match = re.search(
            r"\\ollabel\s*\{([^}]+)\}", text[body_start:body_end]
        )
        label = label_match.group(1).strip() if label_match else None
        per_environment[environment] += 1
        if global_numbering:
            identity = (
                f"{environment}#{label}"
                if label else f"{environment}#{ordinal}"
            )
        else:
            identity = f"{environment}#{per_environment[environment]}"
            if label:
                identity += f"; label={label}"
        result.append(identity)
    return result


def check_source_graph() -> tuple[list[dict[str, str]], set[Path], dict[Path, set[str]]]:
    files = sorted(SRC.rglob("*.tex"))
    file_set = {path.resolve() for path in files}
    children: dict[Path, list[Path]] = collections.defaultdict(list)
    parents: dict[Path, list[Path]] = collections.defaultdict(list)
    subfile_parents: dict[Path, list[Path]] = collections.defaultdict(list)
    commented_counts: dict[Path, int] = {}
    subfile_counts: dict[Path, tuple[int, int]] = {}

    for path in files:
        raw = path.read_text(errors="replace")
        active_imports = imports(path, strip_comments(raw))
        all_imports = imports(path, raw)
        active_subfiles = subfiles(path, strip_comments(raw))
        all_subfiles = subfiles(path, raw)
        assert all(child in file_set for child in active_imports), relative(path)
        assert all(child in file_set for child in active_subfiles), relative(path)
        active_import_counter = collections.Counter(active_imports)
        all_import_counter = collections.Counter(all_imports)
        commented_counts[path] = sum(
            max(0, all_import_counter[child] - active_import_counter[child])
            for child in all_import_counter
        )
        active_subfile_counter = collections.Counter(active_subfiles)
        all_subfile_counter = collections.Counter(all_subfiles)
        subfile_counts[path] = (
            len(active_subfiles),
            sum(
                max(0, all_subfile_counter[child] - active_subfile_counter[child])
                for child in all_subfile_counter
            ),
        )
        for child in active_imports:
            children[path].append(child)
            parents[child].append(path)
        for child in active_subfiles:
            children[path].append(child)
            subfile_parents[child].append(path)

    actual_pin = subprocess.check_output(
        ["git", "-C", str(REPO / "OpenLogic"), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    assert actual_pin == PINNED, (actual_pin, PINNED)

    rows = list(csv.DictReader(INVENTORY.open(), delimiter="\t"))
    assert set(rows[0]) == INVENTORY_FIELDS if rows else False
    expected_paths = sorted(relative(path) for path in files)
    actual_paths = [row["source_file"] for row in rows]
    assert len(files) == 722, len(files)
    assert len(rows) == len(files), (len(rows), len(files))
    assert len(set(actual_paths)) == len(actual_paths), "duplicate source rows"
    assert actual_paths == expected_paths, "inventory paths are not the sorted source tree"

    driver = (SRC / "content.tex").resolve()
    selected = {driver}
    roots: dict[Path, set[str]] = collections.defaultdict(set)
    roots[driver].add("content")
    for first in children[driver]:
        todo = [first]
        seen: set[Path] = set()
        while todo:
            path = todo.pop()
            if path in seen:
                continue
            seen.add(path)
            selected.add(path)
            roots[path].add(first.stem)
            todo.extend(children[path])

    allowed = set(STATUS_MAP.values())
    for row in rows:
        path = (SRC / row["source_file"]).resolve()
        assert path in file_set, row["source_file"]
        assert row["selection"] == (
            "selected" if path in selected else "orphan_or_unselected"
        ), row
        expected_importers = sorted(relative(parent) for parent in parents[path])
        actual_importers = (
            [] if row["direct_importers"] == "-"
            else sorted(row["direct_importers"].split(";"))
        )
        assert actual_importers == expected_importers, row["source_file"]
        expected_subfile_importers = sorted(
            relative(parent) for parent in subfile_parents[path]
        )
        actual_subfile_importers = (
            [] if row["direct_subfile_importers"] == "-"
            else sorted(row["direct_subfile_importers"].split(";"))
        )
        assert actual_subfile_importers == expected_subfile_importers, row["source_file"]
        assert int(row["active_imports"]) == len(
            imports(path, strip_comments(path.read_text(errors="replace")))
        ), row["source_file"]
        assert int(row["commented_imports"]) == commented_counts[path], row["source_file"]
        assert int(row["active_subfiles"]) == subfile_counts[path][0], row["source_file"]
        assert int(row["commented_subfiles"]) == subfile_counts[path][1], row["source_file"]
        expected_roots = sorted(roots.get(path, set()))
        actual_roots = (
            [] if row["selected_roots"] == "-"
            else sorted(row["selected_roots"].split(";"))
        )
        assert actual_roots == expected_roots, row["source_file"]
        assert row["substantive"] in {"yes", "no"}
        status = row["coverage_status"]
        assert status in allowed, (row["source_file"], status)
        evidence = row["formalolp_evidence"]
        if status in {"proved-equivalent", "partial/weaker", "definition/statement-only"}:
            assert evidence != "-" and all(
                (REPO / piece).exists() for piece in evidence.split(";")
            ), row
            assert row["formal_declarations"] != "-", row
        elif status == "non-formal-exposition":
            assert evidence in {"-", "docs/topic-map.md"}, row
        elif status == "dependency-only":
            assert evidence != "-" and all(
                (REPO / piece).exists() for piece in evidence.split(";")
            ), row
            assert row["formal_declarations"] != "-", row
        else:
            assert evidence == "-", row
            assert row["formal_declarations"] == "-", row

    assert sum(row["selection"] == "selected" for row in rows) == len(selected) == 641
    assert sum(row["selection"] == "orphan_or_unselected" for row in rows) == 81
    return rows, selected, roots


def check_reviewer_union(rows: list[dict[str, str]]) -> None:
    central = {row["source_file"]: row for row in rows}
    reviewer_maps = []
    for path in REVIEWERS:
        fields, reviewer_rows = read_tsv(path)
        assert set(fields) == REVIEWER_FIELDS, (path, fields)
        keys = [(row["source_file"], row["source_unit"]) for row in reviewer_rows]
        assert len(keys) == len(set(keys)), (path, "duplicate source-unit row")
        sections = [row for row in reviewer_rows if row["source_unit"] == "section"]
        assert len({row["source_file"] for row in sections}) == len(sections), path
        is_foundations = path.name == "foundations.tsv"
        environment_names = (
            FOUNDATION_UNIT_ENVS if is_foundations else LOGIC_UNIT_ENVS
        )
        global_numbering = is_foundations
        expected_declaration_counts = {} if is_foundations else DECLARATION_COUNTS
        actual_declaration_counts: collections.Counter[str] = collections.Counter()
        for row in reviewer_rows:
            source_unit = row["source_unit"]
            if source_unit.startswith("declaration#"):
                actual_declaration_counts[row["source_file"]] += 1
                assert re.fullmatch(r"declaration#\d+", source_unit), row
                continue
            if source_unit == "section":
                continue
            assert source_unit in expected_source_units(
                row["source_file"], environment_names, global_numbering
            ), (path, row["source_file"], source_unit)
        for source_file in {row["source_file"] for row in sections}:
            expected_units = expected_source_units(
                source_file, environment_names, global_numbering
            )
            actual_units = [
                row["source_unit"]
                for row in reviewer_rows
                if row["source_file"] == source_file
                and row["source_unit"] != "section"
                and not row["source_unit"].startswith("declaration#")
            ]
            assert actual_units == expected_units, (
                path, source_file, expected_units, actual_units
            )
        if is_foundations:
            assert not actual_declaration_counts, (path, actual_declaration_counts)
        else:
            assert dict(actual_declaration_counts) == expected_declaration_counts, (
                path, expected_declaration_counts, dict(actual_declaration_counts)
            )
        reviewer_maps.append({row["source_file"]: row for row in sections})

    foundations, logic = reviewer_maps
    assert len(foundations) == 332, len(foundations)
    assert len(logic) == 388, len(logic)
    assert not set(foundations) & set(logic), "reviewer path overlap"
    union = set(foundations) | set(logic)
    assert union <= set(central), "reviewer path missing from central inventory"
    assert set(central) - union == {"content.tex", "open-logic-about.tex"}

    for path in union:
        reviewer = foundations.get(path) or logic.get(path)
        row = central[path]
        expected_status = STATUS_MAP[reviewer["coverage_status"]]
        assert row["coverage_status"] == expected_status, path
        assert row["coverage_basis"] == reviewer["coverage_basis"], path
        assert row["formalolp_evidence"] == clean_evidence(
            reviewer["formalolp_evidence"]
        ), path
        assert row["formal_declarations"] == reviewer["formal_declarations"], path
        assert row["audit_note"] == reviewer["audit_note"], path

    for reviewer_path in REVIEWERS:
        _, reviewer_rows = read_tsv(reviewer_path)
        for reviewer in reviewer_rows:
            status = STATUS_MAP[reviewer["coverage_status"]]
            evidence = clean_evidence(reviewer["formalolp_evidence"])
            declarations = reviewer["formal_declarations"]
            if status in {
                "proved-equivalent", "partial/weaker", "definition/statement-only",
            }:
                assert evidence != "-" and all(
                    (REPO / piece).exists() for piece in evidence.split(";")
                ), reviewer
                assert declarations != "-" and declarations.strip(), reviewer
                for declaration in declarations.split(";"):
                    if declaration.startswith("FormalOLP/"):
                        assert (REPO / declaration.split(":", 1)[0]).exists(), reviewer
            elif status == "dependency-only":
                assert evidence != "-" and all(
                    (REPO / piece).exists() for piece in evidence.split(";")
                ), reviewer
                assert declarations != "-" and declarations.strip(), reviewer
            else:
                assert evidence == "-" and declarations == "-", reviewer

    counts = collections.Counter(
        STATUS_MAP[reviewer["coverage_status"]]
        for reviewer_map in reviewer_maps
        for reviewer in reviewer_map.values()
    )
    central_counts = collections.Counter(row["coverage_status"] for row in rows)
    assert all(central_counts[status] >= count for status, count in counts.items())
    print(
        "OK: reviewer union 720 section rows (foundations 332 + logic 388); "
        "central-only content.tex, open-logic-about.tex"
    )
    print("section statuses:", " ".join(f"{key}={counts[key]}" for key in sorted(counts)))
    print("central statuses:", " ".join(f"{key}={central_counts[key]}" for key in sorted(central_counts)))


def main() -> None:
    rows, selected, _ = check_source_graph()
    actual_pin = subprocess.check_output(
        ["git", "-C", str(REPO / "OpenLogic"), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    print(
        f"OK: {len(rows)} unique content files; {len(selected)} selected, "
        f"{len(rows) - len(selected)} orphan/unselected; pinned {actual_pin}"
    )
    check_reviewer_union(rows)


if __name__ == "__main__":
    main()
