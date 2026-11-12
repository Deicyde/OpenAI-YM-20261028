# Solution.lean declaration ledger

Solution.lean proves the main theorem. It imports Construction.lean (line 1)
and declares one theorem, which AutoformBot's Lean source index records at
line 4.

## Declarations

### The main theorem

Covered by [The main theorem](../roadmap/challenge/challenge-theorem.md),
lines 3 to 10.

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YangMills.jointExistence` | theorem | [4](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/Solution.lean#L4) | The core comparator asks only for existence, reconstruction, the OPE and the trace test. |

Line 4 states that `YangMills.JointExistence` holds; that definition is on
the [ChallengeSpec.lean ledger](challenge-spec.md#joint-existence). The proof,
lines 5 to 10, takes the detailed construction with penalty 1, the Wilson
family of its family of lattice theories, and, for each strictly increasing
sequence of volume indices, the hierarchy of its final object and reader. It
uses three declarations that this version of the book does not yet map:

| Lean name | Kind | Location |
| --- | --- | --- |
| `YangMills.constructed` | theorem | [Construction.lean:15](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/Construction.lean#L15) |
| `YangMills.wilsonFamily` | def | [WilsonBridge.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/WilsonBridge.lean#L20) |
| `YangMills.hierarchy` | def | [HierarchyBridge.lean:27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/HierarchyBridge.lean#L27) |

## The challenge file

Challenge.lean, at line 5, states the same theorem under the same name with
the proof `sorry`; it is the reference statement against which the group
compares Solution.lean. This project's sparse checkout leaves Challenge.lean
out, so that the name resolves to the proved theorem; the file is unchanged in
the original source.

## Verification

On 2026-11-11 the main theorem, `YangMills.constructed` and the every-phase
reconstruction `YM.EveryPhase.all_characters` were loaded on a devserver
from the published compiled build of commit 3456e5e (Scott Armstrong's
`lean-build-3456e5e`, unpacked; Lake reported all 18,126 jobs up to date),
and `#print axioms` reported only `propext`, `Classical.choice` and
`Quot.sound` for each. Solution.lean, Construction.lean and the files of
YM/EveryPhase contain no `sorry` or `admit`. The build was not recompiled
from source for this book.
