# Yang–Mills construction: a map of the Lean proof

This blueprint maps, in ordinary mathematical language, OpenAI's Lean proof of
the construction of four-dimensional Yang–Mills theory: the repository
yang-mills-group/OpenAI-YM-20261028 at commit 3456e5e7, whose authors
published it under the Apache-2.0 license. Every article states what one
declaration of that original source states, and its Lean links open that
declaration at that commit. The order and grouping follow Scott Armstrong's
informalization of the proof, which divides it into eight parts and
thirty-two units; the [Sources](sources/README.md) page records both sources.

This version is a pilot: the main theorem, with every definition its statement
uses, and Armstrong's unit V.3, reconstruction for every phase.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what is mapped, and what comes later.

<!-- Reference material goes in sources/. Its Markdown notes are pages of the
     site, which a statement's "## Sources" list links to; a site rendered at a
     verified commit links scans and data in the repository instead. A
     dot-prefixed name, or a folder inside sources/ whose README says
     published: false, keeps a note off the site. -->
