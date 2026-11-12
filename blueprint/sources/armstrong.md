# Armstrong's informalization

Scott Armstrong (CNRS and Sorbonne Université; Courant Institute, New York
University) maintains *Yang–Mills informalization*, a map of OpenAI's Lean
proof and a natural-language outline built from it, in collaboration with
Martin Hairer's *humanise-yang-mills* project:
<https://github.com/scottnarmstrong/yang-mills-informalization>, read here at
commit 1a47ac9 (11 November 2026), under the Apache-2.0 license. Its outlines
were written by AI agents from the Lean and are being checked by people; it is
an informal source, not a peer-reviewed one.

This book takes from it the order and grouping of the proof (eight parts and
thirty-two units, `outline/units.md`), the plain-language readings of the
code's names (`glossary.md`), and, for each unit it maps, the unit's outline
and detailed notes. The Lean is the authority: each article states what the
cited declaration of the original source states, and where the outline and
the Lean differ the article follows the Lean, with the difference recorded on
this page.

## The main theorem

Armstrong's `statement.md` compares the public theorem with the Lean
definition by definition. The chapters from the gauge groups to
[the main theorem](../roadmap/challenge/README.md) state the same theorem
from the Lean directly; they were written from the Lean before this source
was consulted.
