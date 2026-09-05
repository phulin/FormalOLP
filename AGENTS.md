This is a formalization project for the Open Logic Project.

- Commit as you go. Use Conventional Commits-ish style with a short one-line description and a paragraph summary below.
- Codex: use timeouts of at least 30 minutes for `wait`, `wait_agent`, and `write_stdin`.

## Lean guidelines

1. **Build explicit chains of lemmas.** Introduce many well-named intermediate lemmas that each capture one mathematical step, including results that may be useful beyond the immediate proof. Prefer a sequence of reusable declarations over a single monolithic proof of the headline theorem. Formalization plans and reviews should identify missing links in these chains and propose or request concrete lemma statements.
2. **Keep declarations small.** Break long proofs into helper lemmas with explicit statements. This gives Lean smaller elaboration problems and avoids repeatedly re-inferring large intermediate terms.
3. **Add type annotations to important intermediate terms.** Prefer `have h : T := ...` over `have h := ...` when `T` is nontrivial. Explicit types reduce metavariable creation and constrain elaboration early.
4. **Do not rely on expensive definitional equality.** If two complicated expressions are mathematically the same but only become identical after unfolding, use an explicit lemma or rewrite to connect them instead of making Lean discover this automatically.
5. **Avoid unfolding large definitions in downstream proofs.** Prove simple API lemmas about a definition once—e.g. application, membership, equality, map, or simp lemmas—and reason through those instead of repeatedly using `simp [BigDefinition]` or `unfold BigDefinition`.
6. **Control `simp` on large expressions.** If a proof is slow, prefer `simp only [lemma1, lemma2, ...]` or perform the key rewrite explicitly before simplifying. Broad `simp` can repeatedly traverse and rewrite very large terms.
7. **Avoid repeated typeclass search.** If Lean repeatedly needs the same complicated instance, construct or select it once with `letI`/`haveI` and reuse it. Failed or ambiguous instance searches can be especially expensive.
8. **Name large repeated expressions.** If the same large sum, map, subtype, structure expression, etc. appears repeatedly, bind it with `let`, `set`, or a helper definition rather than elaborating and comparing the full expression everywhere.
9. **Do not fix slow proofs by increasing `maxHeartbeats`.** A declaration taking seconds usually indicates excessive inference, unfolding, simplification, or automation. Change the proof structure instead of merely allowing more work.
10. **Treat unexpectedly slow declarations as bugs.** Ordinary lemmas should generally elaborate in well under a second; investigate multi-second declarations before building more code on top of them.
11. **Use automation to discover proofs, then specialize it if it is slow.** You can start with a temporary aesop, grind, simp, linarith, etc. If it works, use the corresponding suggestion tactic (aesop?, grind?, simp?, linarith?, exact?, apply?, rw?) and replace broad search with the suggested lemmas/tactics or a smaller ... only [...] invocation.

## Lint hygiene

Write proofs so they pass the default Mathlib linters: bind instances with `let`/`have` (not `letI`/`haveI`) whenever the bound statement is a Prop or the value need not be inlined, and use plain `simp` rather than `simpa` when simplification alone closes the goal; also drop unused simp arguments and prefix unused binder names with `_`.
