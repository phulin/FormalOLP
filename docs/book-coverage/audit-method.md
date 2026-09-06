# Open Logic source coverage audit

This file records the method for [`inventory.tsv`](inventory.tsv), the
file-level inventory for the complete Open Logic source checkout. The pinned
book revision is the `OpenLogic` submodule commit
`1e960beff9ed7835bf3e3f1335e21af3439cd107` (`v1.0-a-931-g1e960be`). The
FormalOLP branch was clean at `16ff1f8` before this audit; `upstream/main`
was fetched and is an ancestor of that commit, so no rebase was needed.

The denominator is every one of the 722 files matching
`OpenLogic/content/**/*.tex` at that revision. This includes part and chapter
aggregators, section files, the complete driver `content.tex`, and
`open-logic-about.tex`. The inventory deliberately retains all files with no
recognized theorem-like environment, because their prose, figures, examples,
or include role can still matter to a book coverage claim. The parser's
`substantive` column is a signal, not an exclusion rule: 665 files have a
positive prose/claim signal and 57 zero-signal structural files remain in the
722-row denominator.

The denominator excludes files outside `OpenLogic/content`, including the
Open Logic style files, include templates, course drivers, documentation,
bibliography, generated output, and non-TeX assets. It also excludes no
content because it is draft, commented out, or absent from the complete
driver. Such material is represented by `selection=orphan_or_unselected` or
by a positive `commented_imports` count. Shared source wrappers and templates
that do live under `content` remain ordinary inventory rows, while external
style/include templates are recorded only through the graph boundary and are
outside this content denominator. The complete driver's active
`\olimport` closure contains 641 files. The other 81 rows include the entire
orphaned `proof-theory/` source tree, source files only reachable through
commented imports, superseded sections, and `open-logic-about.tex`.

The include graph is parsed after removing TeX comments (an unescaped `%`
starts a comment). Each active `\olimport[dir]{name}` and `\subfile{name}` is
resolved relative to the importing file's directory and must resolve to
another content `.tex` file. The inventory records active and commented
`\olimport` counts, active/commented `\subfile` counts, direct importers, and
direct subfile importers, together with the set of complete-driver roots
reaching each file. A file reachable from multiple roots therefore appears
once, with all roots and importers recorded; it is never duplicated or
credited separately for each topic. The current complete driver has eight
active subfile edges, all in the orphaned proof-theory source tree.

Each row also records the section kind, headings, all parsed environment
counts, all `\label`/`\ollabel` values, and named theorem-like units. Named
units are extracted from `defn`, `thm`, `prop`, `lem`, `cor`, `axiom`, `ex`,
`prob`, and `probtag` environments, retaining an optional environment title,
label, or both. `proof`, `explain`, `editorial`, `figure`, `table`, `quote`,
`derivation`, `prooftree`, `oltableau`, and the other recognized exposition
environments are retained in `construct_counts`. Nested TeX macros can make a
heading or optional title appear truncated in this mechanical field; labels,
paths, and environment counts are the authoritative omission checks. This
parser is a source index, not a semantic theorem prover.

Coverage statuses use the same vocabulary as the area-level reviews:

- `proved-equivalent`: the indicated native declaration chain was manually
  checked against the mapped source statement at the stated representation
  and hypothesis boundary. This status applies to the mapped chain, not to
  every item or piece of exposition in the source file.
- `partial/weaker`: a genuine native fragment or restricted representation
  is present, while other source results, examples, hypotheses, or source
  representations remain outside it.
- `definition/statement-only`: a native object or interface corresponds to a
  source definition or listed statement, with no source-equivalent proof
  chain claimed.
- `dependency-only`: the row is a support dependency and is not itself
  mathematical source coverage. The current use is the one section whose
  result is exposed only through a native support dependency; import-only
  part/chapter and driver rows use `structural-container`.
- `structural-container`: an include wrapper whose child rows carry the
  source content audit.
- `non-formal-exposition`: biography, historical narrative, notation
  reference, or repository/editorial material retained for attribution and
  context, without a Lean theorem target. These rows may have no Lean or
  documentation evidence path because their classification is a scope result.
- `missing`: no active FormalOLP declaration was found for the source file's
  substantive material. A topic import, matching filename, or nearby generic
  theorem never changes this status.

The mapped formal rows were manually checked against the indicated FormalOLP
file and declaration names, while structural and non-formal rows were checked
for their source role. That review is deliberately narrower than a claim that
all 722 files or all source units have been semantically re-proved. Files with
one matched theorem and additional source claims remain `partial/weaker` or
`missing` unless the mapped chain and its boundary cover the relevant source
material. The companion area inventories split source files into individual
theorem, definition, proposition, corollary, example, and exercise rows; this
file remains the machine-checkable union denominator for all content files.
Together, the two area inventories cover the 720 topical files under the
foundations and logic roots; this central inventory adds the two root-level
files (`content.tex` and `open-logic-about.tex`) so the full 722-file source
tree is checked in one place.

The standalone checker independently validates the reviewer unit ledgers. It
scans raw TeX (including commented unit environments, matching the frozen
ledger rule), always expects one `section` row, and derives the remaining unit
identities from these explicit rules: foundations recognizes `defn`,
`defish`, `prop`, `thm`, `lem`, `cor`, `axiom`, `ex`, `prob`, `derivation`,
and `conv` with one source-order ordinal; logic recognizes `defn`, `prop`,
`prob`, `ex`, `thm`, `lem`, and `cor` with an ordinal per environment. A first
`\ollabel` changes the identity according to the area schema. The 20 logic
declaration-map rows are checked against their frozen per-file counts and are
also required to carry existing evidence and declaration references.

Run this check from the repository root. It independently rebuilds the active
include closure, verifies that every content file has exactly one inventory
row, checks direct-import and evidence references, and rejects unrecognized
statuses or missing mapped files. The pinned revision assertion makes a
source update fail closed until the inventory is regenerated.

```sh
python3 - <<'PY'
from pathlib import Path
import csv, re, collections, subprocess

repo = Path('.').resolve()
src = repo / 'OpenLogic' / 'content'
inv = repo / 'docs' / 'book-coverage' / 'inventory.tsv'
pinned = '1e960beff9ed7835bf3e3f1335e21af3439cd107'
actual_pin = subprocess.check_output(
    ['git', '-C', str(repo / 'OpenLogic'), 'rev-parse', 'HEAD'], text=True
).strip()
assert actual_pin == pinned, (actual_pin, pinned)

def strip_comments(text):
    out = []
    for line in text.splitlines():
        cut = next((i for i, c in enumerate(line)
                    if c == '%' and (i == 0 or line[i - 1] != '\\')), None)
        out.append(line if cut is None else line[:cut])
    return '\n'.join(out)

files = sorted(src.rglob('*.tex'))
paths = {p.resolve() for p in files}
def rel(p):
    return p.relative_to(src).as_posix()
def imports(path, text):
    return [(path.parent / (d or '') / (name + '.tex')).resolve()
            for d, name in re.findall(
                r'\\olimport(?:\[([^]]+)\])?\{([^}]+)\}', text)]
def subfiles(path, text):
    return [(path.parent / (name + '.tex')).resolve()
            for name in re.findall(r'\\subfile\{([^}]+)\}', text)]

children = collections.defaultdict(list)
parents = collections.defaultdict(list)
subfile_parents = collections.defaultdict(list)
commented_counts = {}
subfile_counts = {}
for path in files:
    raw = path.read_text(errors='replace')
    active = imports(path, strip_comments(raw))
    all_imports = imports(path, raw)
    active_subfiles = subfiles(path, strip_comments(raw))
    all_subfiles = subfiles(path, raw)
    assert all(q in paths for q in active), (rel(path), active)
    assert all(q in paths for q in active_subfiles), (rel(path), active_subfiles)
    active_counts = collections.Counter(active)
    all_counts = collections.Counter(all_imports)
    commented_counts[path] = sum(
        max(0, all_counts[q] - active_counts[q]) for q in all_counts)
    active_subfile_counts = collections.Counter(active_subfiles)
    all_subfile_counts = collections.Counter(all_subfiles)
    subfile_counts[path] = (
        len(active_subfiles),
        sum(max(0, all_subfile_counts[q] - active_subfile_counts[q])
            for q in all_subfile_counts))
    for target in active:
        children[path].append(target)
        parents[target].append(path)
    for target in active_subfiles:
        children[path].append(target)
        subfile_parents[target].append(path)

rows = list(csv.DictReader(inv.open(), delimiter='\t'))
header = set(rows[0]) if rows else set()
expected_header = {
    'source_file','source_root','file_kind','selection','selected_roots',
    'direct_importers','active_imports','active_subfiles','commented_subfiles',
    'direct_subfile_importers','commented_imports','substantive','prose_words',
    'headings','construct_counts','labels','named_items','coverage_status',
    'coverage_basis','formalolp_evidence','formal_declarations','audit_note'}
assert header == expected_header, header
expected = sorted(rel(p) for p in files)
actual = [row['source_file'] for row in rows]
assert len(files) == 722, len(files)
assert len(rows) == len(files), (len(rows), len(files))
assert len(set(actual)) == len(actual), 'duplicate source rows'
assert actual == expected, 'inventory paths are not the sorted content tree'

driver = (src / 'content.tex').resolve()
selected = {driver}
roots = collections.defaultdict(set)
roots[driver].add('content')
for first in children[driver]:
    todo, seen = [first], set()
    while todo:
        path = todo.pop()
        if path in seen:
            continue
        seen.add(path)
        selected.add(path)
        roots[path].add(first.stem)
        todo.extend(children[path])

allowed = {
    'proved-equivalent','partial/weaker','definition/statement-only',
    'dependency-only','structural-container','non-formal-exposition','missing'}
for row in rows:
    path = (src / row['source_file']).resolve()
    assert path in paths, row['source_file']
    assert row['selection'] == ('selected' if path in selected
                                else 'orphan_or_unselected'), row
    expected_importers = sorted(rel(p) for p in parents[path])
    actual_importers = [] if row['direct_importers'] == '-' else sorted(
        row['direct_importers'].split(';'))
    assert actual_importers == expected_importers, row['source_file']
    expected_subfile_importers = sorted(rel(p) for p in subfile_parents[path])
    actual_subfile_importers = [] if row['direct_subfile_importers'] == '-' else sorted(
        row['direct_subfile_importers'].split(';'))
    assert actual_subfile_importers == expected_subfile_importers, row['source_file']
    assert int(row['active_imports']) == len(imports(
        path, strip_comments(path.read_text(errors='replace')))), row
    assert int(row['commented_imports']) == commented_counts[path], row
    assert int(row['active_subfiles']) == subfile_counts[path][0], row
    assert int(row['commented_subfiles']) == subfile_counts[path][1], row
    expected_roots = sorted(roots.get(path, set()))
    actual_roots = [] if row['selected_roots'] == '-' else sorted(
        row['selected_roots'].split(';'))
    assert actual_roots == expected_roots, row['source_file']
    assert row['substantive'] in {'yes','no'}
    status = row['coverage_status']
    assert status in allowed, (row['source_file'], status)
    evidence = row['formalolp_evidence']
    if status in {'proved-equivalent','partial/weaker',
                  'definition/statement-only'}:
        assert evidence != '-' and all(
            (repo / piece).exists() for piece in evidence.split(';')), row
        assert row['formal_declarations'] != '-', row
    elif status == 'non-formal-exposition':
        assert evidence in {'-', 'docs/topic-map.md'}, row
    elif status == 'dependency-only':
        assert evidence != '-' and all(
            (repo / piece).exists() for piece in evidence.split(';')), row
        assert row['formal_declarations'] != '-', row
    else:
        assert evidence == '-', row
        assert row['formal_declarations'] == '-', row

assert sum(row['selection'] == 'selected' for row in rows) == len(selected) == 641
assert sum(row['selection'] == 'orphan_or_unselected' for row in rows) == 81
print(f'OK: {len(rows)} unique content files; {len(selected)} selected, '
      f'{len(rows)-len(selected)} orphan/unselected; pinned {actual_pin}')
PY
```

At the pinned revision this prints `OK: 722 unique content files; 641
selected, 81 orphan/unselected`. The check proves source-file union and graph
accounting; it does not turn parser counts into semantic equivalence claims.
The standalone [`scripts/check-book-coverage.py`](../../scripts/check-book-coverage.py)
also verifies the canonical reviewer schemas and reconciles their 332+388
section union with this 722-row file inventory.
