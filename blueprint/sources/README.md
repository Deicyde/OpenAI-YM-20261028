# Sources

## Boundary

The formal source is the repository
[yang-mills-group/OpenAI-YM-20261028](https://github.com/yang-mills-group/OpenAI-YM-20261028)
at commit 3456e5e75cf8d4cd558955a5c7638fba2d68f464 ("OpenAI construction of
pure Yang–Mills obtained 10/28/2026"), with Mathlib at commit
81a5d257c8e410db227a6665ed08f64fea08e997. This repository is that commit with
the blueprint added: its Lean files are the original ones, unchanged, and each
article's Lean links open the cited declaration at that commit. The informal
source is [Scott Armstrong's informalization](armstrong.md) of the proof,
whose map of eight parts and thirty-two units orders the book.

This version maps the main theorem with every definition its statement uses
(the files PublicTheory.lean, PublicWilson.lean, ChallengeSpec.lean and
Solution.lean) and Armstrong's unit V.3, reconstruction for every phase (the
modules of YM/EveryPhase). The repository is checked out sparsely: only the
files the book cites are on disk, and Challenge.lean, which restates the main
theorem with the proof `sorry`, is left out so that the theorem's name
resolves to its proof in Solution.lean.

## Status of the sources

The Lean files and the README are project-authored by the upstream authors,
not peer-reviewed sources, and Armstrong's outlines were written by AI agents
from the Lean. The Lean statements are authoritative: the articles state
exactly what they say.

## Treatment

The 81 keyword declarations and 143 structure fields of PublicTheory.lean,
PublicWilson.lean and ChallengeSpec.lean are each reconciled to one of the
articles of the first eight chapters, and their ledgers below list every one
of these names under its article. The two instances without names in
PublicWilson.lean are supporting entries of its ledger. Mathlib is an imported
dependency and is not inventoried; the [Lean-side notes](lean-notes.md) record
the Mathlib definitions the statements use. Of the modules of YM/EveryPhase,
the selected statements of Armstrong's unit V.3 and the definitions their
statements use have articles; the ledger of those modules lists every
declaration they contain.

The statuses the roadmap records come from two checks. On 2026-11-11 the files
of the public statement were built on a devserver with Lean 4.32.0 and
Mathlib 81a5d257 (`lake build` passed), and the main theorem and the results
of YM/EveryPhase were loaded from the published compiled build of the whole
source, as the [Solution.lean ledger](solution.md#verification) records.

## Pages

- [PublicTheory.lean declaration ledger](public-theory.md): the gauge groups,
  spacetime, test functions and Wightman structures, by covering article.
- [PublicWilson.lean declaration ledger](public-wilson.md): the Wilson
  lattice, Wilson families and the ordered continuum limit, with the two
  instances without names as supporting entries.
- [ChallengeSpec.lean declaration ledger](challenge-spec.md): regularity, the
  continuum hierarchy and its reconstruction, expansion and trace-test
  conditions, and the joint existence statement.
- [Solution.lean declaration ledger](solution.md): the main theorem, the
  declarations its proof uses, and how it was checked.
- [Armstrong's informalization](armstrong.md): the informal source, how this
  book uses it, and where its outline and the Lean differ.
- [Upstream description of the public challenge](upstream-readme.md): the
  README's informal description of the challenge, quoted and mapped to the
  articles.
- [Lean-side notes](lean-notes.md): the Mathlib notions the statements use,
  junk-value conventions, naming observations and build options.

<!-- AUTHORING NOTES — these comments are not published.

     One page per reference. Each page maps stable source locators to the
     roadmap articles that depend on them, so every statement can be traced
     back to the passage it came from.
-->
