# The Yang–Mills construction in Lean

This book states, in ordinary mathematical language, what OpenAI's Lean proof
of the construction of four-dimensional Yang–Mills theory proves, following
its original source: the repository yang-mills-group/OpenAI-YM-20261028 at
commit 3456e5e7 ('OpenAI construction of pure Yang–Mills obtained
10/28/2026'). Each article states exactly what one declaration of that source
states, and links to it there. The order and grouping follow Scott Armstrong's
informalization of the proof, which divides it into eight parts and
thirty-two units.

The main theorem asks, for every closed matrix gauge group whose real Lie
algebra is simple and nonabelian, for one regular Wilson lattice family (its
couplings run logarithmically with the inverse lattice spacing, and its
insertions are continuous, gauge invariant and determined by a fixed finite
stencil) such that every strictly increasing sequence of volume indices has a
subsequence along which a single continuum hierarchy reproduces the ordered
continuum limit of the lattice moments, reconstructs a Wightman quantum field
theory, satisfies an all-orders separated operator product expansion and
passes a non-freeness test. The first eight chapters state it, with every
definition its statement uses, down to Mathlib. The original source proves it
from a detailed construction, which this book maps unit by unit; this version
maps one unit, reconstruction for every phase, as the
[Coverage page](../coverage/README.md) records.

## Chapters

- [Compact simple matrix gauge groups](gauge-groups/README.md)
- [Spacetime, Lorentz symmetry and test functions](spacetime/README.md)
- [Wilson lattice and its ordered continuum limit](wilson-lattice/README.md)
- [Wightman quantum field theory](wightman/README.md)
- [Continuum hierarchy and Wightman reconstruction](continuum-hierarchy/README.md)
- [All-orders separated operator product expansion](operator-product-expansion/README.md)
- [Non-freeness test](non-freeness/README.md)
- [The main theorem](challenge/README.md)

<!-- AUTHORING NOTES — these comments are not published.

     Replace the line above with a short statement of the goal, then link each
     chapter below in reading order. This page is the book's preface and table
     of contents; keep it short.

     A chapter is a DIRECTORY holding a README.md. That README.md *is* the
     chapter: it carries the narrative prose, and the formalizable statements
     beside it are placed into that prose where they are first used.

         roadmap/
           README.md              <- this page
           first-chapter/
             README.md            <- the chapter, with its exposition
             some-definition.md   <- a formalizable leaf
             main-result.md

     A chapter directory WITHOUT a README.md is not a chapter. Its pages
     collapse to the top level and the published book has no structure. Write
     the chapter as `<chapter>/README.md`, never as a sibling file beside the
     directory, then run `autoform check`.

     Add a `## Chapters` heading once there is more than one chapter to list.
-->
