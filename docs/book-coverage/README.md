# Open Logic book coverage audit

This audit inventories the complete OpenLogic content checkout and compares
its substantive sections with the current FormalOLP declarations. The book
source is pinned to OpenLogic commit
`1e960beff9ed7835bf3e3f1335e21af3439cd107` (`v1.0-a-931-g1e960be`). The
denominator is every `OpenLogic/content/**/*.tex` file at that revision:
**722 files**. The active `content.tex` include closure selects **641** files;
**81** are orphaned or unselected, including the orphaned `proof-theory`
tree and documentation or superseded material. Selection does not remove a
file from the denominator.

The two reviewer inventories cover the 720 topical files with no path overlap:

| inventory | section files | rows | row breakdown |
| --- | ---: | ---: | --- |
| [`foundations.tsv`](foundations.tsv) | 332 | 1,202 | 332 section rows + 870 named source-unit rows |
| [`logic.tsv`](logic.tsv) | 388 | 1,393 | 388 section rows + 985 substantive unit rows + 20 declaration-map rows |

The central [`inventory.tsv`](inventory.tsv) adds exactly two central-only
rows: `content.tex` (the complete-book driver, classified
`structural-container`) and `open-logic-about.tex` (editorial/source
documentation, classified `non-formal-exposition`). The central inventory
therefore has one row for every one of the 722 source files. The executable
check confirms the include graph, importer records, selected/orphan split,
reviewer union, and central classifications:

```text
section statuses: definition/statement-only=8 dependency-only=1 missing=551 non-formal-exposition=18 partial/weaker=43 proved-equivalent=2 structural-container=97
central statuses: definition/statement-only=8 dependency-only=1 missing=551 non-formal-exposition=19 partial/weaker=43 proved-equivalent=2 structural-container=98
```

The result does **not** show full book representation. Of the 720 topical
sections, 551 have `missing`, 43 have only a partial or weaker native result,
and 8 have a definition or statement without a source-equivalent proof chain.
Here `missing` means that the reviewer found no active FormalOLP declaration
for the section's substantive material. It does not prove that a formalization
is impossible, and a nearby topic import, matching filename, or dependency
does not change that status. `structural-container` rows are include wrappers
whose child sections are audited separately. `dependency-only` identifies
support exposed through a native dependency without claiming that the source
section itself is formalized.

`proved-equivalent` is narrow: it applies to the named declaration chain at
the recorded representation and hypothesis boundary. It does not certify all
claims, examples, exercises, or exposition in the source file. The inventories
are an exhaustive file and source-unit index followed by triage and manual
spot-checks of the mapped classifications. They are **not** a complete
semantic review or proof-equivalence certification of all 722 files, all 1,855
substantive source-unit rows, or all 20 declaration-map rows. See
[`audit-method.md`](audit-method.md) for the
parser, denominator, include handling, exclusions, and status definitions;
the area-level review notes are [`foundations-review.md`](foundations-review.md)
and [`logic-review.md`](logic-review.md).

Run the independent checker from the repository root:

```sh
python3 scripts/check-book-coverage.py
```

The checker is [`scripts/check-book-coverage.py`](../../scripts/check-book-coverage.py).

It prints the pinned revision, the 722/641/81 source accounting, the 332+388
reviewer union, and the status reconciliation. The source audit was prepared
with a clean FormalOLP checkout at `16ff1f8`. `upstream/main` was fetched; it
is an ancestor of that commit (`HEAD` is 26 commits ahead and zero behind),
so no rebase was needed before preparing these files.
