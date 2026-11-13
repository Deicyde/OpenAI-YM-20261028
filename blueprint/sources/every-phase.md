# YM/EveryPhase declaration ledger

The modules of YM/EveryPhase hold Armstrong's unit V.3, reconstruction for
every phase. This page lists every declaration that AutoformBot's Lean source
index records in the 34 files, file by file in line order, with a link to the
declaration's line in the original source at commit 3456e5e and its
docstring. The article that covers a declaration says so in the notes under
the file's table; a declaration without such a note has no article in this
version of the book.

### Average

`YM/EveryPhase/Average.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.pulse` | def | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L20) |  |
| `YM.EveryPhase.pulse_bounded` | lemma | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L22) |  |
| `YM.EveryPhase.pulse_measurable` | lemma | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L29) |  |
| `YM.EveryPhase.pulse_positive` | lemma | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L35) |  |
| `YM.EveryPhase.pulse_lower` | lemma | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L46) |  |
| `YM.EveryPhase.up` | def | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L63) |  |
| `YM.EveryPhase.up_limit` | theorem | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L65) |  |
| `YM.EveryPhase.up_measurable` | lemma | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L69) |  |
| `YM.EveryPhase.weighted` | def | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L72) |  |
| `YM.EveryPhase.oddTest` | def | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L86) |  |
| `YM.EveryPhase.averaged` | def | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L88) |  |
| `YM.EveryPhase.intervalChar` | lemma | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L91) |  |
| `YM.EveryPhase.plane_odd` | lemma | [104](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L104) |  |
| `YM.EveryPhase.one_average` | lemma | [113](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L113) |  |
| `YM.EveryPhase.two_average` | lemma | [149](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Average.lean#L149) |  |

### Barycenter

`YM/EveryPhase/Barycenter.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.eager` | lemma | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Barycenter.lean#L18) |  |
| `YM.EveryPhase.word_axes` | lemma | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Barycenter.lean#L44) |  |
| `YM.EveryPhase.word_continuity` | lemma | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Barycenter.lean#L48) |  |
| `YM.EveryPhase.barycenter` | theorem | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Barycenter.lean#L75) |  |

### Charge

`YM/EveryPhase/Charge.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.Season` | structure | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L14) |  |
| `YM.EveryPhase.Stress.Season.real` | field | [15](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L15) |  |
| `YM.EveryPhase.Stress.Season.smoothTime` | field | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L16) |  |
| `YM.EveryPhase.Stress.Season.unit` | field | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L17) |  |
| `YM.EveryPhase.Stress.Season.stands` | lemma | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L19) |  |
| `YM.EveryPhase.Stress.accepts` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L24) |  |
| `YM.EveryPhase.Stress.Reservation` | structure | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L37) |  |
| `YM.EveryPhase.Stress.Reservation.pocket` | field | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L38) |  |
| `YM.EveryPhase.Stress.Reservation.across` | field | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L39) |  |
| `YM.EveryPhase.Stress.reservable` | lemma | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L42) |  |
| `YM.EveryPhase.Stress.Reservation.admits` | lemma | [60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L60) |  |
| `YM.EveryPhase.Stress.Charge` | def | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L80) |  |
| `YM.EveryPhase.Stress.action` | def | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L86) | `v ∂ Φ_B` as distribution is sum `∂_a Φ_B` tested at `v^a m`. No integration-by-parts on general field-word domains here: minus is in the definition. Includes the derivative of the affine factor. |
| `YM.EveryPhase.Stress.adjAction` | def | [90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L90) |  |
| `YM.EveryPhase.Stress.action_labels` | lemma | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L93) |  |
| `YM.EveryPhase.Stress.measure_identity` | lemma | [104](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L104) |  |
| `YM.EveryPhase.Stress.local_action` | theorem | [143](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Charge.lean#L143) | Testing functions are Schwartz with HasCompactSupport (C∞ with compact support). Real f, integral one; any such height profile. Spatial cutoff can also be complex. Test supports not including exterior vectors of the matrix element between which we test. Only a local identity. |

Covered by [Admissible time profile](../roadmap/every-phase/admissible-time-profile.md) (`YM.EveryPhase.Stress.Season`); [Admissible spatial cutoff](../roadmap/every-phase/admissible-spatial-cutoff.md) (`YM.EveryPhase.Stress.Reservation`); [Stress charge and the commutator action](../roadmap/every-phase/stress-charge.md) (`YM.EveryPhase.Stress.Charge`, `YM.EveryPhase.Stress.adjAction`); [Infinitesimal Poincaré transformation of a field](../roadmap/every-phase/infinitesimal-field-transformation.md) (`YM.EveryPhase.Stress.action`); and [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) (`YM.EveryPhase.Stress.local_action`).

Lean-side notes:

- `YM.EveryPhase.Stress.Season` and `YM.EveryPhase.Stress.Reservation` are propositions. `YM.EveryPhase.Stress.accepts` (line 24) proves that an admissible time profile exists, and `YM.EveryPhase.Stress.Season.stands` (line 19, not `YM.EveryPhase.stands`) that its closed support is nonempty.
- Moved out of the admissible-spatial-cutoff article: `YM.EveryPhase.Stress.Reservation` assumes neither that the set of points is compact nor that the profile has compact support. `YM.EveryPhase.Stress.reservable` (line 42) proves that an admissible spatial cutoff exists for every compact set and every compactly supported profile.
- `YM.EveryPhase.Stress.Charge` carries no admissibility hypothesis; it uses `YM.EveryPhase.Stress.pincushion` and `YM.EveryPhase.Stress.touch` (Frost) and `YM.EveryPhase.Stress.fieldM` (Tensor).
- `YM.EveryPhase.Stress.action` uses the rotations only through their generators, by way of `YM.Next.BOUNDARY.Descent.rankAction`; the minus sign of the derivative term sits in `YM.EveryPhase.Stress.partialProbe`. `YM.EveryPhase.Stress.action_labels` (line 93) rewrites the derivative term as a sum of fields of derivative labels weighted by the Wick factors, under `YM.EveryPhase.Stress.Prospect`, `YM.EveryPhase.Stress.Gallery` and `YM.Next.BOUNDARY.FieldCore`; it is a lemma, not the definition.
- Moved out of the infinitesimal-field-transformation article: `YM.Next.BOUNDARY.Descent.tangent_parts` (YM/Next/BOUNDARY/Derived.lean:43) splits the matrix of a Killing field into a skew part commuting with the time reflection (a spatial-rotation generator) and a symmetric part anticommuting with it (a boost generator). `YM.Next.BOUNDARY.Descent.rank_space` (Derived.lean:120) and `YM.Next.BOUNDARY.Descent.rank_boost` (Derived.lean:128) give the label action on each part. `YM.EveryPhase.Stress.action` uses no such decomposition.
- `YM.EveryPhase.Stress.local_action` needs only `YM.Next.BOUNDARY.FieldCore`, which is `YM.Boundary.Wightman.Realizes` without vacuum uniqueness. Its proof replaces the cutoff by its real part, removes the difference by local commutativity (the field `localPairs` of `YM.Next.BOUNDARY.FieldCore`), and applies `YM.EveryPhase.Stress.measure_identity` (line 104), which uses `YM.EveryPhase.Stress.Schwartz_shells` and `YM.EveryPhase.Stress.action_labels`; `YM.EveryPhase.Stress.Reservation.admits` (line 60) supplies `YM.EveryPhase.Stress.Jury` at every point of the set.
- Indirect proof link: stress-charge-commutator links ward-identity-schwartz-spectators through `YM.EveryPhase.Stress.measure_identity`, which has no article. The proof also reaches `YM.EveryPhase.Stress.Jury` (spacelike-cutoff-condition) through `YM.EveryPhase.Stress.Reservation.admits`, which has no article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Probe` | [YM/Distribution/Tests.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L20) | [Admissible time profile](../roadmap/every-phase/admissible-time-profile.md), [Admissible spatial cutoff](../roadmap/every-phase/admissible-spatial-cutoff.md) |
| `YM.Mink.spacelike` | [YM/Mink/Geometry.lean:80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L80) | [Admissible spatial cutoff](../roadmap/every-phase/admissible-spatial-cutoff.md) |
| `YM.position` | [YM/Space/Configurations.lean:29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L29) | [Admissible spatial cutoff](../roadmap/every-phase/admissible-spatial-cutoff.md) |
| `YM.Mink.lateral` | [YM/Mink/Geometry.lean:103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L103) | [Admissible spatial cutoff](../roadmap/every-phase/admissible-spatial-cutoff.md) |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Stress charge and the commutator action](../roadmap/every-phase/stress-charge.md), [Infinitesimal Poincaré transformation of a field](../roadmap/every-phase/infinitesimal-field-transformation.md), [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.Fields` | [YM/Fields/System.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L22) | [Stress charge and the commutator action](../roadmap/every-phase/stress-charge.md) |
| `YM.Table.Stress` | [YM/Euclid/Stress.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L57) | [Stress charge and the commutator action](../roadmap/every-phase/stress-charge.md), [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Next.BOUNDARY.Descent.rankAction` | [YM/Next/BOUNDARY/Derived.lean:114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derived.lean#L114) | [Infinitesimal Poincaré transformation of a field](../roadmap/every-phase/infinitesimal-field-transformation.md) |
| `YM.Table.Rotation` | [YM/Euclid/Stress.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L22) | [Infinitesimal Poincaré transformation of a field](../roadmap/every-phase/infinitesimal-field-transformation.md) |
| `YM.Table.pin` | [YM/Euclid/Union.lean:26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Union.lean#L26) | [Infinitesimal Poincaré transformation of a field](../roadmap/every-phase/infinitesimal-field-transformation.md) |
| `YM.Table.Tag` | [YM/Euclid/Lift.lean:66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Lift.lean#L66) | [Infinitesimal Poincaré transformation of a field](../roadmap/every-phase/infinitesimal-field-transformation.md) |
| `YM.Next.BOUNDARY.FieldCore` | [YM/Next/BOUNDARY/Core.lean:34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Core.lean#L34) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Table.StressLaws` | [YM/Euclid/Stress.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L90) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Table.Window` | [YM/Euclid/Stress.lean:72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L72) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Table.useAt` | [YM/Euclid/Lift.lean:69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Lift.lean#L69) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.Surface` | [YM/Boundary/Contour.lean:54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L54) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.Waves` | [YM/Boundary/Contour.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L57) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.Blanket` | [YM/Shift/Sol.lean:60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L60) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.Surface.Aurora` | [YM/Shift/Sol.lean:109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L109) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.DiffPlan` | [YM/Euclid/Differential.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L20) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Table.RealSpin` | [YM/Euclid/Table.lean:80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Table.lean#L80) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.Spins.Descends` | [YM/Fields/Star.lean:26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L26) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.starRead` | [YM/Fields/Star.lean:42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L42) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |
| `YM.Boundary.Symmetries` | [YM/Fields/System.lean:111](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L111) | [The stress charge generates the transformation](../roadmap/every-phase/stress-charge-commutator.md) |

### Compatibility

`YM/EveryPhase/Compatibility.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Next.BOUNDARY.FieldCore.of_realizes` | theorem | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Compatibility.lean#L17) |  |
| `YM.Next.BOUNDARY.onFinal` | theorem | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Compatibility.lean#L26) | For ANY already produced Final, not just instances from `after_materializes`. |
| `YM.Next.BOUNDARY.extends_unique` | theorem | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Compatibility.lean#L40) |  |
| `YM.Next.BOUNDARY.Attachment.inner_eq` | theorem | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Compatibility.lean#L44) |  |
| `YM.Boundary.solid_fields` | lemma | [60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Compatibility.lean#L60) |  |

### Court

`YM/EveryPhase/Court.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.dress` | lemma | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L13) |  |
| `YM.EveryPhase.Stress.ticket` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L20) |  |
| `YM.EveryPhase.Stress.cost` | lemma | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L30) |  |
| `YM.EveryPhase.Stress.turn_effect` | lemma | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L36) |  |
| `YM.EveryPhase.Stress.inserting` | lemma | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L44) |  |
| `YM.EveryPhase.Stress.introduce` | lemma | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L56) |  |
| `YM.EveryPhase.Stress.two_more` | lemma | [60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L60) |  |
| `YM.EveryPhase.Stress.adds_tensor` | lemma | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L63) |  |
| `YM.EveryPhase.Stress.tensor_read` | lemma | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L67) |  |
| `YM.EveryPhase.Stress.shells` | def | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L70) |  |
| `YM.EveryPhase.Stress.compact_shells` | lemma | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L77) |  |
| `YM.EveryPhase.Stress.shave` | def | [120](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L120) |  |
| `YM.EveryPhase.Stress.widespread` | lemma | [121](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L121) |  |
| `YM.EveryPhase.Stress.Schwartz_shells` | lemma | [147](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Court.lean#L147) |  |

Covered by [Shell identity for word expectations](../roadmap/every-phase/shell-identity.md) (`YM.EveryPhase.Stress.shells`); and [Ward identity with arbitrary spectators](../roadmap/every-phase/ward-identity-schwartz-spectators.md) (`YM.EveryPhase.Stress.Schwartz_shells`).

Lean-side notes:

- `YM.EveryPhase.Stress.shells` is a proposition. Word expectations are `YM.Boundary.Surface.expect`, the boundary distribution evaluated on the product test `YM.Boundary.Joint.materialize` of the word, which is the constant 1 for the empty word.
- `YM.EveryPhase.Stress.compact_shells` (line 77) proves the shell identity when every spectator test function has compact support. `YM.EveryPhase.Stress.Schwartz_shells` removes that assumption by approximation through `YM.EveryPhase.Stress.shave` and `YM.EveryPhase.Stress.widespread` (line 121).
- Proof depends on of ward-identity-schwartz-spectators: `YM.EveryPhase.Stress.Schwartz_shells` uses `YM.EveryPhase.Stress.zeta` directly and goes through `YM.EveryPhase.Stress.compact_shells`, which has no article and uses `YM.EveryPhase.Stress.verdict`, `YM.EveryPhase.Stress.hole`, `YM.EveryPhase.Stress.stamp`, `YM.EveryPhase.Stress.receives` and `YM.EveryPhase.Stress.cloth`; through `YM.EveryPhase.Stress.dress` and `YM.EveryPhase.Stress.turn_effect` it reaches `YM.EveryPhase.Stress.chairs`, `YM.EveryPhase.Stress.seat`, `YM.EveryPhase.Stress.effect` and `YM.EveryPhase.Stress.touch`. These are the article's links to minkowski-jump-identity, slot-insertion, tested-current-jump, tested-jump-value, killing-weighted-tests and minkowski-stress-field.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Surface.expect` | [YM/Fields/Star.lean:95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L95) | [Shell identity for word expectations](../roadmap/every-phase/shell-identity.md) |
| `YM.Boundary.Joint.materialize` | [YM/Distribution/Product.lean:139](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Product.lean#L139) | [Shell identity for word expectations](../roadmap/every-phase/shell-identity.md) |
| `YM.Boundary.Sentence` | [YM/Fields/Star.lean:39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L39) | [Shell identity for word expectations](../roadmap/every-phase/shell-identity.md) |
| `YM.Boundary.Letter` | [YM/Fields/Star.lean:38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L38) | [Shell identity for word expectations](../roadmap/every-phase/shell-identity.md) |
| `YM.Next.BOUNDARY.Descent.rankAction` | [YM/Next/BOUNDARY/Derived.lean:114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derived.lean#L114) | [Shell identity for word expectations](../roadmap/every-phase/shell-identity.md) |
| `YM.DiffPlan` | [YM/Euclid/Differential.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L20) | [Shell identity for word expectations](../roadmap/every-phase/shell-identity.md) |
| `YM.Table.StressLaws` | [YM/Euclid/Stress.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L90) | [Ward identity with arbitrary spectators](../roadmap/every-phase/ward-identity-schwartz-spectators.md) |
| `YM.Table.Window` | [YM/Euclid/Stress.lean:72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L72) | [Ward identity with arbitrary spectators](../roadmap/every-phase/ward-identity-schwartz-spectators.md) |

### Cross

`YM/EveryPhase/Cross.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.vertical` | lemma | [10](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L10) |  |
| `YM.EveryPhase.Stress.horizontal` | lemma | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L46) |  |
| `YM.EveryPhase.Stress.real_path` | lemma | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L67) |  |
| `YM.EveryPhase.Stress.Prospect` | structure | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L76) |  |
| `YM.EveryPhase.Stress.Prospect.hT` | field | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L77) |  |
| `YM.EveryPhase.Stress.Prospect.hu` | field | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L78) |  |
| `YM.EveryPhase.Stress.Prospect.hs` | field | [79](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L79) |  |
| `YM.EveryPhase.Stress.Prospect.hi` | field | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L80) |  |
| `YM.EveryPhase.Stress.Prospect.hd` | field | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L81) |  |
| `YM.EveryPhase.Stress.Prospect.hF` | field | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L82) |  |
| `YM.EveryPhase.Stress.Prospect.hZ` | field | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L83) |  |
| `YM.EveryPhase.Stress.crest` | def | [85](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L85) |  |
| `YM.EveryPhase.Stress.trough` | def | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L88) |  |
| `YM.EveryPhase.Stress.first_ports` | lemma | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L91) |  |
| `YM.EveryPhase.Stress.currentJump` | def | [130](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L130) |  |
| `YM.EveryPhase.Stress.variation` | lemma | [133](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Cross.lean#L133) |  |

Covered by [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) (`YM.EveryPhase.Stress.Prospect`); and [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) (`YM.EveryPhase.Stress.crest`, `YM.EveryPhase.Stress.trough`, `YM.EveryPhase.Stress.currentJump`).

Lean-side notes:

- `YM.EveryPhase.Stress.Prospect` is a proposition. Its parameter, the reflection and reality symmetry of the table, is itself a proposition and enters only through the conjugation used in `YM.Table.Conserved`. The inclusion laws are stated for the table itself and the derivative laws for the second table.
- The field `hu` unfolds to `YM.Table.Hierarchy`: laws, signed-permutation symmetry and reality (`YM.Table.RealSpin`, whose mirror clause quantifies over every `YM.Signed`, a permutation of the axes with sign changes, not only reflections), translations, reflection positivity, its smeared form, smoothness and the polynomial derivative bound.
- `YM.EveryPhase.Stress.crest` inserts the stress after the distinguished entry and `YM.EveryPhase.Stress.trough` before it. The inserted label is the Euclidean class of the time-row stress component, not the Minkowski label of `YM.EveryPhase.Stress.M`; the Wick factor enters through `YM.EveryPhase.Stress.Killing.w`.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Table.Conserved` | [YM/Euclid/Stress.lean:59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L59) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Table.Hierarchy` | [YM/Euclid/Words.lean:141](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Words.lean#L141) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Table.RealSpin` | [YM/Euclid/Table.lean:80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Table.lean#L80) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Table.Symmetric` | [YM/Euclid/Table.lean:71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Table.lean#L71) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.DiffPlan` | [YM/Euclid/Differential.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L20) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.DiffPlan.Inclusions` | [YM/Euclid/Differential.lean:58](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L58) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.DiffPlan.Derivatives` | [YM/Euclid/Differential.lean:61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L61) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.Waves` | [YM/Boundary/Contour.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L57) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.Waves.Region` | [YM/Boundary/Contour.lean:71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L71) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.Surface` | [YM/Boundary/Contour.lean:54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L54) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.Blanket` | [YM/Shift/Sol.lean:60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L60) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.Blanket.partialD` | [YM/Shift/Sol.lean:78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L78) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.Surface.Aurora` | [YM/Shift/Sol.lean:109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L109) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md), [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) |
| `YM.Boundary.Surface.Aurora.emit` | [YM/Shift/Sol.lean:116](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L116) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md), [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) |
| `YM.Boundary.Surface.Aurora.FullBody` | [YM/Shift/Sol.lean:118](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L118) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.fields` | [YM/Shift/Closing.lean:71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Closing.lean#L71) | [Hypotheses for continuing the stress current](../roadmap/every-phase/stress-continuation-hypotheses.md) |
| `YM.Boundary.glow` | [YM/Shift/Sol.lean:34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L34) | [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) |
| `YM.Boundary.place` | [YM/Boundary/Contour.lean:44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L44) | [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) |
| `YM.Boundary.dawn` | [YM/Shift/Ridge.lean:24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Ridge.lean#L24) | [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) |
| `YM.Boundary.Probe` | [YM/Distribution/Tests.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L20) | [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) |
| `YM.Table.Stress` | [YM/Euclid/Stress.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L57) | [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) |

### Decay

`YM/EveryPhase/Decay.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.density_power` | lemma, private | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L14) |  |
| `YM.EveryPhase.decay` | theorem | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L22) | Tail integration of the shell bound. Parameters outside the unit interval can already be included at the same price using total mass. |
| `YM.EveryPhase.char_cont` | theorem | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L82) |  |
| `YM.EveryPhase.test_cont` | lemma | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L93) | For continuity of heat use the scalar spectral measure on spacetime frequencies. Approximate the exponential on the positive cone uniformly by compact bumps times the exponential. Fourier test against the translation functions. |
| `YM.EveryPhase.uniform_heat` | theorem | [113](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L113) |  |
| `YM.EveryPhase.inverse_square` | theorem | [173](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decay.lean#L173) | Subtraction of the FULL zero-energy projection. |

Covered by [Inverse-square heat decay after subtracting zero energy](../roadmap/every-phase/inverse-square-heat-decay.md) (`YM.EveryPhase.inverse_square`).

Lean-side notes:

- The docstring of `YM.EveryPhase.inverse_square` reads 'Subtraction of the FULL zero-energy projection.' The heat time is a nonnegative real at least 1, and both bounds hold in the partial order of the complex numbers, which makes the bounded quantity real.
- The vacuum-subtracted bound, with the vacuum term in place of the zero-energy projection, is `YM.EveryPhase.extends_decay` (Vacuum.lean:51), which has no article.
- Indirect proof links of inverse-square-heat-decay: the proof uses `YM.EveryPhase.light_bound` directly (low-energy-bound). It uses `YM.EveryPhase.word_bound` (Light.lean:197), whose statement is about `YM.EveryPhase.νletter` and which reaches `YM.EveryPhase.strict_evaluation` through `YM.EveryPhase.sum_pair`, `YM.EveryPhase.word_pair`, `YM.EveryPhase.word_continuity` and `YM.EveryPhase.eager`; its auxiliary bound `hI` (line 182) is stated on `YM.EveryPhase.νletter`. None of these intermediate declarations has an article, hence the links to strict-height-continuity-barycenter and word-spectral-measure. It also uses `YM.EveryPhase.residual_pair` (Projection.lean:145) and `YM.EveryPhase.decay` (line 22).

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Spectral.PVM` | [YM/Spectral/Projection.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spectral/Projection.lean#L19) | [Inverse-square heat decay after subtracting zero energy](../roadmap/every-phase/inverse-square-heat-decay.md) |

### Decree

`YM/EveryPhase/Decree.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.cloth_split` | lemma | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L18) |  |
| `YM.EveryPhase.Stress.variations` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L24) |  |
| `YM.EveryPhase.Stress.responses` | lemma | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L35) |  |
| `YM.EveryPhase.Stress.grades` | lemma | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L51) |  |
| `YM.EveryPhase.Stress.twin` | lemma | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L62) |  |
| `YM.EveryPhase.Stress.Jury` | structure | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L73) |  |
| `YM.EveryPhase.Stress.Jury.fits` | field | [74](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L74) |  |
| `YM.EveryPhase.Stress.Jury.during` | field | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L75) |  |
| `YM.EveryPhase.Stress.partial_jump` | theorem | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L77) |  |
| `YM.EveryPhase.Stress.Gallery` | structure | [167](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L167) |  |
| `YM.EveryPhase.Stress.Gallery.book` | field | [168](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L168) |  |
| `YM.EveryPhase.Stress.Gallery.spectra` | field | [169](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L169) |  |
| `YM.EveryPhase.Stress.Gallery.cases` | field | [170](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L170) |  |
| `YM.EveryPhase.Stress.ancestor` | lemma | [173](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L173) |  |
| `YM.EveryPhase.Stress.stamp` | def | [196](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L196) |  |
| `YM.EveryPhase.Stress.receives` | def | [200](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L200) |  |
| `YM.EveryPhase.Stress.dawn_zero` | lemma | [206](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L206) |  |
| `YM.EveryPhase.Stress.verdict` | theorem | [208](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Decree.lean#L208) |  |

Covered by [Spacelike condition on cutoff and profile](../roadmap/every-phase/spacelike-cutoff-condition.md) (`YM.EveryPhase.Stress.Jury`); [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) (`YM.EveryPhase.Stress.Gallery`); [Tested stress insertion next to a field](../roadmap/every-phase/tested-current-jump.md) (`YM.EveryPhase.Stress.stamp`); [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md) (`YM.EveryPhase.Stress.receives`); and [Minkowski jump identity](../roadmap/every-phase/minkowski-jump-identity.md) (`YM.EveryPhase.Stress.verdict`).

Lean-side notes:

- `YM.EveryPhase.Stress.Gallery` has three fields: every cutoff is attenuable (`book`), the Fourier supports lie in the cones (`spectra`), and for every adjacent pair one sequence of heights serves all labels (`cases`: there is a sequence, and for every term and every label, `YM.EveryPhase.Stress.atlases` holds for `YM.EveryPhase.Stress.pair`). The convergence is stated for the configurations of the heights, not for the height vectors. `YM.EveryPhase.Stress.ancestor` (line 173) turns the sequence into strictly increasing heights with one tied pair; `YM.EveryPhase.Stress.verdict` uses it.
- `YM.EveryPhase.Stress.Jury` holds no support, reality or integral condition. A source comment at line 72 says that only the condition local to the slot of the distinguished field is needed.
- `YM.EveryPhase.Stress.stamp` inserts the Euclidean class of the time-row stress component, weighted by the Wick factors; its helpers are `YM.EveryPhase.Stress.cloth` (Frost) and `YM.EveryPhase.Stress.seat`, `YM.EveryPhase.Stress.cushion` and `YM.EveryPhase.Stress.chairs` (Slots).
- Moved out of the tested-jump-value article: `YM.EveryPhase.Stress.receives` has no time-integral factor. The integral of the profile enters only in `YM.EveryPhase.Stress.verdict` (line 213), as a factor of `YM.EveryPhase.Stress.receives`. Do not confuse it with `YM.OS.Spread.Resolution.receives`. In the proof of `YM.EveryPhase.Stress.verdict` it is `YM.EveryPhase.Stress.mandate` (Frost.lean:90) at height 0.
- Proof depends on of minkowski-jump-identity: `YM.EveryPhase.Stress.partial_jump` (line 77, no article) uses `YM.EveryPhase.Stress.through_jump` (joint-current-jump-limit), `YM.EveryPhase.Stress.taskC` (continued-jump-value), `YM.EveryPhase.Stress.crest`, `YM.EveryPhase.Stress.trough` and `YM.EveryPhase.Stress.harbors` (integrated-current-jump) and `YM.EveryPhase.Stress.atlases` (jump-admissibility). `YM.EveryPhase.Stress.ancestor` uses `YM.EveryPhase.Stress.atlases` and `YM.EveryPhase.Stress.pair`; `YM.EveryPhase.Stress.gavel` (Frost.lean:97) uses `YM.EveryPhase.Stress.pincushion` (killing-weighted-tests); `YM.EveryPhase.Stress.cloth_split` and `YM.EveryPhase.Stress.stack` use `YM.EveryPhase.Stress.touch` and `YM.EveryPhase.Stress.zeta` (minkowski-stress-field). The intermediate lemmas `YM.EveryPhase.Stress.variations`, `responses`, `mandate`, `mandate_int`, `harvest`, `twin` and `dawn_zero` have no article.
- `YM.Table.StressLaws` (with `YM.Table.Window`) is a hypothesis of `YM.EveryPhase.Stress.verdict` and of `YM.EveryPhase.Stress.Schwartz_shells` and belongs to an unmapped unit. The minkowski-jump-identity and ward-identity-schwartz-spectators articles describe it in identical words.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Blanket` | [YM/Shift/Sol.lean:60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L60) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.Blanket.Modified` | [YM/Shift/Sol.lean:70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L70) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Bid.cones` | [YM/Bid/Tar.lean:39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Bid/Tar.lean#L39) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.coneM` | [YM/Shift/Closing.lean:23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Closing.lean#L23) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Mink.Lorentz.dual` | [YM/Mink/Lorentz.lean:95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L95) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.shores` | [YM/Shift/Closing.lean:70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Closing.lean#L70) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.dawn` | [YM/Shift/Ridge.lean:24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Ridge.lean#L24) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.Surface.Aurora` | [YM/Shift/Sol.lean:109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L109) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.Distn.fourier` | [YM/Distribution/Tests.lean:108](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L108) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.Probe.hat` | [YM/Distribution/Tests.lean:73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L73) | [Exchange heights for every adjacent pair](../roadmap/every-phase/exchange-height-sequences.md) |
| `YM.Boundary.Surface` | [YM/Boundary/Contour.lean:54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L54) | [Tested stress insertion next to a field](../roadmap/every-phase/tested-current-jump.md), [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md) |
| `YM.Table.Stress` | [YM/Euclid/Stress.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L57) | [Tested stress insertion next to a field](../roadmap/every-phase/tested-current-jump.md) |
| `YM.Table.pin` | [YM/Euclid/Union.lean:26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Union.lean#L26) | [Tested stress insertion next to a field](../roadmap/every-phase/tested-current-jump.md) |
| `YM.Boundary.Joint` | [YM/Distribution/Product.lean:123](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Product.lean#L123) | [Tested stress insertion next to a field](../roadmap/every-phase/tested-current-jump.md) |
| `YM.Bid.ink` | [YM/Bid/Corners.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Bid/Corners.lean#L90) | [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md), [Minkowski jump identity](../roadmap/every-phase/minkowski-jump-identity.md) |
| `YM.Next.BOUNDARY.Descent.lie` | [YM/Next/BOUNDARY/Derived.lean:104](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derived.lean#L104) | [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md) |
| `YM.Next.BOUNDARY.Descent.rankAction` | [YM/Next/BOUNDARY/Derived.lean:114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derived.lean#L114) | [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md) |
| `YM.DiffPlan` | [YM/Euclid/Differential.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L20) | [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md) |
| `YM.Table.Rotation` | [YM/Euclid/Stress.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L22) | [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md) |
| `YM.Table.Tag` | [YM/Euclid/Lift.lean:66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Lift.lean#L66) | [Tested value of the jump](../roadmap/every-phase/tested-jump-value.md) |
| `YM.Table.StressLaws` | [YM/Euclid/Stress.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L90) | [Minkowski jump identity](../roadmap/every-phase/minkowski-jump-identity.md) |
| `YM.Table.Window` | [YM/Euclid/Stress.lean:72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L72) | [Minkowski jump identity](../roadmap/every-phase/minkowski-jump-identity.md) |
| `YM.Table.useAt` | [YM/Euclid/Lift.lean:69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Lift.lean#L69) | [Minkowski jump identity](../roadmap/every-phase/minkowski-jump-identity.md) |
| `YM.conf` | [YM/Space/Configurations.lean:63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L63) | [Minkowski jump identity](../roadmap/every-phase/minkowski-jump-identity.md) |

### DerivativeHelpers

`YM/EveryPhase/DerivativeHelpers.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Next.BOUNDARY.towards_shore` | lemma | [15](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/DerivativeHelpers.lean#L15) | Nontrivial approach even at any of the spectator partial boundaries. |

### Docks

`YM/EveryPhase/Docks.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.safeguard` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L20) |  |
| `YM.EveryPhase.Stress.Dock` | abbrev | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L37) |  |
| `YM.EveryPhase.Stress.town` | def | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L39) |  |
| `YM.EveryPhase.Stress.morn` | def | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L40) |  |
| `YM.EveryPhase.Stress.eve` | def | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L41) |  |
| `YM.EveryPhase.Stress.affordable` | lemma | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L43) |  |
| `YM.EveryPhase.Stress.sundial` | def | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L52) |  |
| `YM.EveryPhase.Stress.scene` | def | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L53) |  |
| `YM.EveryPhase.Stress.arrival` | lemma | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L55) |  |
| `YM.EveryPhase.Stress.apparition` | lemma | [60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L60) |  |
| `YM.EveryPhase.Stress.atlases` | def | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L73) |  |
| `YM.EveryPhase.Stress.displacement` | lemma | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L76) |  |
| `YM.EveryPhase.Stress.tidal_bend` | lemma | [102](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L102) |  |
| `YM.EveryPhase.Stress.tidal_limit` | lemma | [140](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L140) |  |
| `YM.EveryPhase.Stress.allows` | def | [185](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L185) |  |
| `YM.EveryPhase.Stress.tidal_shift` | lemma | [187](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Docks.lean#L187) |  |

Covered by [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) (`YM.EveryPhase.Stress.Dock`, `YM.EveryPhase.Stress.town`, `YM.EveryPhase.Stress.morn`, `YM.EveryPhase.Stress.eve`); and [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) (`YM.EveryPhase.Stress.sundial`, `YM.EveryPhase.Stress.atlases`, `YM.EveryPhase.Stress.allows`).

Lean-side notes:

- `YM.EveryPhase.Stress.apparition` (line 60) shows that the point of the stress at real offset t lies in the spacelike gap of the adjacent pair exactly when |t| is less than the spatial distance to the distinguished point, so `YM.EveryPhase.Stress.allows` says that the derivative supports of the cutoff stay spacelike to that point.
- `YM.EveryPhase.Stress.atlases` asks the two exchange germs to agree only near points of the gap whose times are all zero (`YM.Boundary.NearPair.Panes.sameGround`); agreement on the whole gap is derived afterwards by `YM.Boundary.NearPair.Panes.reaches` (YM/Shift/Exchange.lean:43).

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.NearPair` | [YM/Shift/Swap.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Swap.lean#L19) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |
| `YM.Boundary.NearPair.Fleck` | [YM/Shift/Swap.lean:56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Swap.lean#L56) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |
| `YM.Boundary.Pane` | [YM/Shift/Swap.lean:66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Swap.lean#L66) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |
| `YM.Boundary.NearPair.Panes` | [YM/Shift/Exchange.lean:33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Exchange.lean#L33) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |
| `YM.Boundary.NearPair.Panes.sameGround` | [YM/Shift/Exchange.lean:40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Exchange.lean#L40) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |
| `YM.Mink.spacelike` | [YM/Mink/Geometry.lean:80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L80) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |
| `YM.Boundary.shores` | [YM/Shift/Closing.lean:70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Closing.lean#L70) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |
| `YM.Boundary.Surface.Aurora` | [YM/Shift/Sol.lean:109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L109) | [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) |

### Extension

`YM/EveryPhase/Extension.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.member` | def | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L19) | Weak commutant using actual unbounded adjoint. (Weak definition with all field word domain vectors.) This form doesn't need a convention about what the Lean value of an unbounded operator is off its domain. |
| `YM.EveryPhase.Completed` | structure | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L51) | `L` fixes all choices before any arity, test, or point. In particular retains the **whole** resolution `F.α.space.Out` and its values on compressed whole words; no enlargement of the generating algebra. No further refinement of the ultraviolet or volume limits used in the Final. See `S.Field`, `S.Union`, `Table.useAt`, `Locals` / `Selection.Certificate` (F.phase), `Maxwell.Ranks` (F.phase.transport.comparator), F.room's CellHyp and RankWidths, for the common Euclidean part. So this uses the baseline spec for Yang-Mills (same gauge quantifiers, schedule/tuning/normalization, extraction, actual cell copies and corrected detector polynomial root bounds, ranks etc. as in the old CLOSED). We include some quantitatives internal to reconstruction because of the route we take. `zeroE` projection here is PVM (energy 0) on the FULL space, `bHeat` its boundary evolution e^{-sH}, see `bHeat_pair`, `bHeat_ground`. Stress: all as Minkowski distributions with spec in Charge/Implement. See also Tensor for explicit Lorentz conventions and differentiation on labels, and Decree for the corresponding partial-boundary passage on compact tests, using the shore data `appointment` in `Force`. Polynomial rule uses arbitrary representative sections (such sections exist see `Stress.reps`). |
| `YM.EveryPhase.Completed.isTheory` | field | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L52) |  |
| `YM.EveryPhase.Completed.into_onto` | field | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L53) |  |
| `YM.EveryPhase.Completed.euclid` | field | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L54) |  |
| `YM.EveryPhase.Completed.mink` | field | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L55) |  |
| `YM.EveryPhase.Completed.light` | field | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L57) |  |
| `YM.EveryPhase.Completed.heat` | field | [59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L59) |  |
| `YM.EveryPhase.Completed.commutant` | field | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L64) |  |
| `YM.EveryPhase.Completed.continued_stress` | field | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L65) |  |
| `YM.EveryPhase.Completed.depends` | field | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L67) |  |
| `YM.EveryPhase.Completed.at_words` | field | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L68) |  |
| `YM.EveryPhase.Completed.at_boundary` | field | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L70) |  |
| `YM.EveryPhase.all_characters` | theorem | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L75) |  |
| `YM.EveryPhase.allPlanes` | lemma | [85](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L85) |  |
| `YM.EveryPhase.recognizes` | lemma | [90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L90) |  |
| `YM.EveryPhase.fixedHeat` | lemma | [100](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L100) |  |
| `YM.EveryPhase.exactly_fixed` | lemma | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean#L103) |  |

Covered by [Weak commutant with the Hilbert-space adjoint](../roadmap/every-phase/weak-commutant.md) (`YM.EveryPhase.member`); [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) (`YM.EveryPhase.Completed`); and [Reconstruction in every phase](../roadmap/every-phase/reconstruction-every-phase.md) (`YM.EveryPhase.all_characters`).

Lean-side notes:

- `YM.EveryPhase.member` uses Mathlib's `LinearPMap.adjoint`, whose value on the adjoint domain is 0 when the domain is not dense (`LinearPMap.adjoint_apply_of_not_dense`, Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:172 at the pinned revision). The weak-commutant article states this convention.
- `YM.EveryPhase.Completed` is a proposition on a record and a family. In its field `heat` the heat time is a nonnegative real at least 1 and the bounds hold in the order of the complex numbers; `light` bounds the real value of `YM.EveryPhase.νletter` on `YM.EveryPhase.lowE`; `continued_stress` is `YM.EveryPhase.Stress.Force` for the phase table, the family's continuation, the record's rotations, derivative plan and stress tensor, the hierarchy's reflection and reality symmetry, and the family's Wightman data.
- The fields of `YM.Next.BOUNDARY.FieldCore` (YM/Next/BOUNDARY/Core.lean:34-44) are exactly those of `YM.Boundary.Wightman.Realizes` (YM/Fields/System.lean:124-135) without `unique`. This is why completed-reconstruction can describe the Wightman conditions as the family's conditions plus uniqueness of the vacuum.
- Under `Total` and `sharpPair`, `YM.Boundary.Fields.really` (YM/Fields/System.lean:53) shows that the field of the starred label and conjugated test, on the domain, is a restriction of the Hilbert-space adjoint. `YM.EveryPhase.all_characters` matches `YM.EveryPhase.member` with `YM.EveryPhase.weaklyCentral` through `YM.EveryPhase.precise` (Irreducible.lean:195), which has no article.
- The proof of `YM.EveryPhase.all_characters` uses directly `YM.EveryPhase.almanac`, `YM.EveryPhase.boundary_realizes`, `YM.EveryPhase.reaches`, `YM.EveryPhase.every`, `YM.EveryPhase.boundary_zero_energy`, `YM.EveryPhase.light_bound`, `YM.EveryPhase.inverse_square`, `YM.EveryPhase.precise` with `YM.EveryPhase.irreducible`, `YM.EveryPhase.Stress.force`, `YM.EveryPhase.word_continuity`, `YM.EveryPhase.barycenter`, and `YM.OS.Spread.Resolution.barycenter` (YM/Phase/Mixture.lean:113) for the Euclidean barycenter.
- Indirect proof links of reconstruction-every-phase: boundary-isometry-surjective (`YM.EveryPhase.onto` through `YM.EveryPhase.reaches`), zero-energy-projection-vacuum (`YM.EveryPhase.all_plant` through `YM.EveryPhase.every`, `YM.EveryPhase.boundary_realizes` and `YM.EveryPhase.boundary_zero_energy`) and strict-height-continuity-barycenter (`YM.EveryPhase.strict_evaluation` through `YM.EveryPhase.word_continuity` and `YM.EveryPhase.barycenter`, by way of `YM.EveryPhase.eager`). None of these intermediate declarations has an article. The direct links are low-energy-bound, inverse-square-heat-decay, irreducibility and stress-tensor-every-phase.
- `YM.EveryPhase.allPlanes`, `YM.EveryPhase.recognizes`, `YM.EveryPhase.fixedHeat` and `YM.EveryPhase.exactly_fixed` (Armstrong's Remark V.3.3) have no article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Weak commutant with the Hilbert-space adjoint](../roadmap/every-phase/weak-commutant.md), [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.Boundary.Fields.denselyDefined` | [YM/Fields/System.lean:50](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L50) | [Weak commutant with the Hilbert-space adjoint](../roadmap/every-phase/weak-commutant.md) |
| `YM.Boundary.Wightman.Realizes` | [YM/Fields/System.lean:124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L124) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.OS.Chamber.UniqueHeat` | [YM/Phase/Mixture.lean:35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Phase/Mixture.lean#L35) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.Spectral.PVM` | [YM/Spectral/Projection.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spectral/Projection.lean#L19) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.Word.distinct` | [YM/Euclid/Words.lean:34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Words.lean#L34) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.Table.expect` | [YM/Euclid/Words.lean:93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Words.lean#L93) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.Boundary.Surface` | [YM/Boundary/Contour.lean:54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L54) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.Boundary.Joint` | [YM/Distribution/Product.lean:123](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Product.lean#L123) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.OS.Selection` | [YM/Phase/Mixture.lean:127](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Phase/Mixture.lean#L127) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md) |
| `YM.Spec.Final` | [YM/Spec/Closed.lean:64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spec/Closed.lean#L64) | [Completed reconstruction](../roadmap/every-phase/completed-reconstruction.md), [Reconstruction in every phase](../roadmap/every-phase/reconstruction-every-phase.md) |

### Frequency

`YM/EveryPhase/Frequency.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.reversed` | def | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L17) |  |
| `YM.EveryPhase.reversed_at` | lemma | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L18) |  |
| `YM.EveryPhase.plane_mul_integrable` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L20) |  |
| `YM.EveryPhase.hat_bra` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L24) |  |
| `YM.EveryPhase.merged_inner` | lemma | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L36) |  |
| `YM.EveryPhase.split_plane` | lemma | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L40) |  |
| `YM.EveryPhase.joined_fourier` | lemma | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L45) |  |
| `YM.EveryPhase.merge_height` | lemma | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L64) |  |
| `YM.EveryPhase.along_compact` | lemma | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L67) |  |
| `YM.EveryPhase.bar_compact` | lemma | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L72) |  |
| `YM.EveryPhase.joined_compact` | lemma | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L77) |  |
| `YM.EveryPhase.chilled` | def | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L83) |  |
| `YM.EveryPhase.chilled_zero` | lemma | [85](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L85) |  |
| `YM.EveryPhase.Braided` | lemma | [89](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L89) |  |
| `YM.EveryPhase.boundary_tilt` | lemma | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frequency.lean#L103) |  |

### Frost

`YM/EveryPhase/Frost.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.cloth` | def | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L13) |  |
| `YM.EveryPhase.Stress.clothes` | lemma | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L14) |  |
| `YM.EveryPhase.Stress.pincushion` | def | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L19) |  |
| `YM.EveryPhase.Stress.pincushion_at` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L20) |  |
| `YM.EveryPhase.Stress.effect` | def | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L23) |  |
| `YM.EveryPhase.Stress.effect_at` | lemma | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L26) |  |
| `YM.EveryPhase.Stress.touch` | def | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L35) |  |
| `YM.EveryPhase.Stress.touch_at` | lemma | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L36) |  |
| `YM.EveryPhase.Stress.arch` | def | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L38) |  |
| `YM.EveryPhase.Stress.affect` | def | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L40) |  |
| `YM.EveryPhase.Stress.affect_cont` | lemma | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L41) |  |
| `YM.EveryPhase.Stress.uplifting` | lemma | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L43) |  |
| `YM.EveryPhase.Stress.stack` | def | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L49) |  |
| `YM.EveryPhase.Stress.stack_at` | lemma | [50](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L50) |  |
| `YM.EveryPhase.Stress.stack_zero` | lemma | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L53) |  |
| `YM.EveryPhase.Stress.loads` | def | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L55) |  |
| `YM.EveryPhase.Stress.loads_at` | lemma | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L57) |  |
| `YM.EveryPhase.Stress.survey` | def | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L63) |  |
| `YM.EveryPhase.Stress.survey_walk` | lemma | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L64) |  |
| `YM.EveryPhase.Stress.dial` | lemma | [66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L66) |  |
| `YM.EveryPhase.Stress.town_survey` | lemma | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L69) |  |
| `YM.EveryPhase.Stress.morn_survey` | lemma | [71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L71) |  |
| `YM.EveryPhase.Stress.eve_survey` | lemma | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L73) |  |
| `YM.EveryPhase.Stress.shift_scene` | lemma | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L75) |  |
| `YM.EveryPhase.Stress.shift_strict` | lemma | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L78) |  |
| `YM.EveryPhase.Stress.strict_height` | lemma | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L80) |  |
| `YM.EveryPhase.Stress.judge` | lemma | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L83) |  |
| `YM.EveryPhase.Stress.mandate` | def | [90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L90) |  |
| `YM.EveryPhase.Stress.gavel` | def | [97](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L97) |  |
| `YM.EveryPhase.Stress.mandate_int` | lemma | [102](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L102) |  |
| `YM.EveryPhase.Stress.harvest` | lemma | [118](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Frost.lean#L118) |  |

Covered by [Tested stress insertion next to a field](../roadmap/every-phase/tested-current-jump.md) (`YM.EveryPhase.Stress.cloth`); and [Test functions weighted by a Killing field](../roadmap/every-phase/killing-weighted-tests.md) (`YM.EveryPhase.Stress.pincushion`, `YM.EveryPhase.Stress.effect`, `YM.EveryPhase.Stress.touch`).

Lean-side notes:

- `YM.EveryPhase.Stress.effect` is defined through `SchwartzMap.smulLeftCLM`, which multiplies only by a multiplier of temperate growth and gives 0 otherwise. `YM.EveryPhase.Stress.effect_at` proves the pointwise formula, and with it the temperate growth of the affine multiplier, that killing-weighted-tests states; `YM.EveryPhase.Stress.touch_at` and `YM.EveryPhase.Stress.pincushion_at` give the other two formulas.
- `YM.EveryPhase.Stress.clothes` proves the pointwise formula of `YM.EveryPhase.Stress.cloth` that tested-current-jump states.
- `YM.EveryPhase.Stress.mandate` (line 90) and `YM.EveryPhase.Stress.gavel` (line 97) are used in the proof of `YM.EveryPhase.Stress.verdict` and have no article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Probe` | [YM/Distribution/Tests.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L20) | [Test functions weighted by a Killing field](../roadmap/every-phase/killing-weighted-tests.md) |
| `YM.Boundary.Probe.along` | [YM/Distribution/Tests.lean:29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L29) | [Test functions weighted by a Killing field](../roadmap/every-phase/killing-weighted-tests.md) |
| `YM.Boundary.Probe.combine` | [YM/Distribution/Product.lean:73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Product.lean#L73) | [Test functions weighted by a Killing field](../roadmap/every-phase/killing-weighted-tests.md) |
| `YM.Mink.divide` | [YM/Mink/Geometry.lean:39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L39) | [Test functions weighted by a Killing field](../roadmap/every-phase/killing-weighted-tests.md) |
| `YM.M4.move` | [YM/Space/Orthogonal.lean:24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L24) | [Test functions weighted by a Killing field](../roadmap/every-phase/killing-weighted-tests.md) |

### Hot

`YM/EveryPhase/Hot.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.closer` | lemma, private | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Hot.lean#L16) |  |
| `YM.EveryPhase.vector_cooled` | lemma | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Hot.lean#L29) |  |
| `YM.EveryPhase.hot_cont` | lemma | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Hot.lean#L77) |  |
| `YM.EveryPhase.rangeClosed` | lemma | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Hot.lean#L96) |  |
| `YM.EveryPhase.vector_in` | lemma | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Hot.lean#L99) |  |
| `YM.EveryPhase.shot_in` | lemma | [111](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Hot.lean#L111) |  |

### Implement

`YM/EveryPhase/Implement.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.Modes` | def | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L19) | Represent all classes, for expanding the RHS. Formula will hold whichever of these representative sections is used. |
| `YM.EveryPhase.Stress.reps` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L20) |  |
| `YM.EveryPhase.Stress.involved` | def | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L24) |  |
| `YM.EveryPhase.Stress.repertoire` | def | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L26) |  |
| `YM.EveryPhase.Stress.localized` | lemma | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L28) |  |
| `YM.EveryPhase.Stress.wordAct` | def | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L39) | derivation rule on fields and composition (all pin, domain and operator choices fixed). |
| `YM.EveryPhase.Stress.sumAct` | def | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L43) |  |
| `YM.EveryPhase.Stress.derivation` | lemma | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L47) |  |
| `YM.EveryPhase.Stress.linearity` | lemma | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L51) |  |
| `YM.EveryPhase.Stress.Generates` | def | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L56) |  |
| `YM.EveryPhase.Stress.Derives` | def | [60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L60) |  |
| `YM.EveryPhase.Stress.Generated` | lemma | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L64) |  |
| `YM.EveryPhase.Stress.Force` | structure | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L81) |  |
| `YM.EveryPhase.Stress.Force.appointment` | field | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L83) |  |
| `YM.EveryPhase.Stress.Force.orbital` | field | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L84) |  |
| `YM.EveryPhase.Stress.Force.symmetric` | field | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L87) |  |
| `YM.EveryPhase.Stress.Force.hermitian` | field | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L88) |  |
| `YM.EveryPhase.Stress.Force.conserve` | field | [90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L90) |  |
| `YM.EveryPhase.Stress.Force.commutator` | field | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L91) |  |
| `YM.EveryPhase.Stress.Force.rule` | field | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L92) |  |
| `YM.EveryPhase.Stress.force` | lemma | [94](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Implement.lean#L94) |  |

Covered by [Charges act as derivations on sums of words](../roadmap/every-phase/charge-acts-as-derivation.md) (`YM.EveryPhase.Stress.Modes`, `YM.EveryPhase.Stress.involved`, `YM.EveryPhase.Stress.repertoire`, `YM.EveryPhase.Stress.wordAct`, `YM.EveryPhase.Stress.sumAct`, `YM.EveryPhase.Stress.Derives`); [Charges generate the transformations of fields](../roadmap/every-phase/charge-generates-transformations.md) (`YM.EveryPhase.Stress.Generates`); [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) (`YM.EveryPhase.Stress.Force`); and [The stress tensor in every phase](../roadmap/every-phase/stress-tensor-every-phase.md) (`YM.EveryPhase.Stress.force`).

Lean-side notes:

- `YM.EveryPhase.Stress.Generates`, `YM.EveryPhase.Stress.Derives` and `YM.EveryPhase.Stress.Force` are propositions.
- `YM.EveryPhase.Stress.Generated` (line 64) proves that charges generating the transformations act as derivations, and `YM.EveryPhase.Stress.reps` (line 20) that a choice of representatives exists under the symmetry and inclusion laws. Neither is stated in the articles.
- In `YM.EveryPhase.Stress.Force`, `appointment` only asserts that cutoffs and a Laplace family exist with `YM.EveryPhase.Stress.Prospect` and `YM.EveryPhase.Stress.Gallery`; `orbital` states invariance of the domain as the existence of a domain vector equal to the transformed one; `conserve` uses `YM.EveryPhase.Stress.partialProbe` and `YM.EveryPhase.Stress.eta`. The Euclidean Ward identities `YM.Table.StressLaws` are not a field; they enter only the proof of `YM.EveryPhase.Stress.force`.
- The proof of `YM.EveryPhase.Stress.force` uses `YM.EveryPhase.Stress.local_action` (the article's one proof link) and `YM.EveryPhase.Stress.Generated`, and gets covariance, hermiticity, conservation and symmetry from `YM.EveryPhase.Stress.tensor_lorentz` (Tensor.lean:210), `YM.EveryPhase.Stress.tensor_herm` (Tensor.lean:217), `YM.EveryPhase.Stress.tensor_conserved` (Tensor.lean:227) and `YM.EveryPhase.Stress.M_symmetric` (Tensor.lean:29), none of which has an article. It also uses `YM.EveryPhase.Stress.pair` (jump-admissibility) directly, and builds the witnesses of `YM.EveryPhase.Stress.Prospect` (stress-continuation-hypotheses), `YM.EveryPhase.Stress.Gallery` (exchange-height-sequences) and `YM.EveryPhase.Stress.Generates` (charge-generates-transformations) in its own body.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Charges generate the transformations of fields](../roadmap/every-phase/charge-generates-transformations.md), [Charges act as derivations on sums of words](../roadmap/every-phase/charge-acts-as-derivation.md), [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) |
| `YM.Table.pin` | [YM/Euclid/Union.lean:26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Union.lean#L26) | [Charges act as derivations on sums of words](../roadmap/every-phase/charge-acts-as-derivation.md) |
| `YM.Boundary.Contour` | [YM/Boundary/Contour.lean:115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L115) | [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) |
| `YM.Mink.Poincare` | [YM/Mink/Poincare.lean:32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L32) | [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) |
| `YM.Boundary.Joint.push` | [YM/Distribution/Product.lean:157](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Product.lean#L157) | [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) |
| `YM.Boundary.Probe.bar` | [YM/Distribution/Tests.lean:37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L37) | [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) |
| `YM.Boundary.Action` | [YM/Fields/System.lean:92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L92) | [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) |
| `YM.Next.BOUNDARY.mat` | [YM/Next/BOUNDARY/Coordinates.lean:64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Coordinates.lean#L64) | [Stress tensor of a reconstructed theory](../roadmap/every-phase/stress-tensor-record.md) |
| `YM.Spec.Final` | [YM/Spec/Closed.lean:64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spec/Closed.lean#L64) | [The stress tensor in every phase](../roadmap/every-phase/stress-tensor-every-phase.md) |
| `YM.Spec.Algebra` | [YM/Spec/Closed.lean:28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spec/Closed.lean#L28) | [The stress tensor in every phase](../roadmap/every-phase/stress-tensor-every-phase.md) |
| `YM.Table.Hierarchy` | [YM/Euclid/Words.lean:141](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Words.lean#L141) | [The stress tensor in every phase](../roadmap/every-phase/stress-tensor-every-phase.md) |

### Irreducible

`YM/EveryPhase/Irreducible.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.paste` | theorem, private | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L22) |  |
| `YM.EveryPhase.saturated` | theorem, private | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L56) |  |
| `YM.EveryPhase.weaklyCentral` | def | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L93) | Bounded Hilbert-space operators (complex linear); no hypothesis about B's action on the domain. We write the actual adjoint on word-domain vectors as a field: existing `Fields.really` identifies `(J p, bar f)` on that domain as the restriction of the Hilbert-space adjoint (`LinearPMap` order). |
| `YM.EveryPhase.word_central` | lemma | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L99) |  |
| `YM.EveryPhase.pairing_at` | lemma | [110](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L110) |  |
| `YM.EveryPhase.commutant` | theorem | [118](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L118) |  |
| `YM.EveryPhase.precise` | theorem | [195](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L195) |  |
| `YM.EveryPhase.irreducible` | theorem | [207](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Irreducible.lean#L207) |  |

Covered by [Weakly central bounded operators](../roadmap/every-phase/weakly-central-operators.md) (`YM.EveryPhase.weaklyCentral`); and [Irreducibility in every phase](../roadmap/every-phase/irreducibility.md) (`YM.EveryPhase.irreducible`).

Lean-side notes:

- `YM.EveryPhase.weaklyCentral` assumes nothing about the Wightman data and does not require the operator to map the domain into itself.
- Moved out of the irreducibility article: `YM.EveryPhase.irreducible` takes only the family, the character and the operator. Its forward direction is `YM.EveryPhase.commutant` (line 118), which gives the scalar explicitly as the vacuum expectation of the operator and draws on the family's `YM.Next.BOUNDARY.FieldCore` and `YM.Next.BOUNDARY.Attachment` (lines 126-127); the converse uses the adjoint relation of `YM.Next.BOUNDARY.FieldCore`. Surjectivity of the boundary map is proved separately for every family by `YM.EveryPhase.reaches` (Projection.lean:20) and is not used.
- Proof depends on of irreducibility: `YM.EveryPhase.commutant` reaches `YM.EveryPhase.bHeat` directly (lines 162-163), `YM.EveryPhase.monomial` through `YM.EveryPhase.word_central` (lines 99-102), and `YM.EveryPhase.zeroE` through `YM.EveryPhase.bHeat_limit` (Projection.lean:102), which it applies before rewriting with `YM.EveryPhase.all_plant` (lines 168-169). Hence the four links to boundary-heat-semigroup, sums-of-words, energy-regions and zero-energy-projection-vacuum. It never uses the uniqueness clause of the Wightman conditions, which the family does not carry.
- `YM.EveryPhase.precise` (line 195), the bridge to `YM.EveryPhase.member` under `YM.Next.BOUNDARY.FieldCore`, has no article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Weakly central bounded operators](../roadmap/every-phase/weakly-central-operators.md) |
| `YM.Boundary.Probe.bar` | [YM/Distribution/Tests.lean:37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L37) | [Weakly central bounded operators](../roadmap/every-phase/weakly-central-operators.md) |
| `YM.Boundary.StarOp` | [YM/Fields/Star.lean:37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L37) | [Weakly central bounded operators](../roadmap/every-phase/weakly-central-operators.md) |

### IrreducibleHelpers

`YM/EveryPhase/IrreducibleHelpers.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Paley.highC` | lemma | [10](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/IrreducibleHelpers.lean#L10) |  |

### Killing

`YM/EveryPhase/Killing.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.Killing` | structure | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L20) | All translations plus infinitesimal Lorentz transformations. |
| `YM.EveryPhase.Stress.Killing.translation` | field | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L21) |  |
| `YM.EveryPhase.Stress.Killing.V` | field | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L22) |  |
| `YM.EveryPhase.Stress.Killing.ok` | field | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L23) |  |
| `YM.EveryPhase.Stress.Killing.realV` | def | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L27) |  |
| `YM.EveryPhase.Stress.Killing.w` | def | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L28) |  |
| `YM.EveryPhase.Stress.Killing.we` | def | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L30) |  |
| `YM.EveryPhase.Stress.Killing.w_real` | lemma | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L31) |  |
| `YM.EveryPhase.Stress.Killing.w_wick` | lemma | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L33) |  |
| `YM.EveryPhase.Stress.Killing.tilted` | def | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L36) |  |
| `YM.EveryPhase.Stress.Killing.tilted_space` | lemma | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L37) |  |
| `YM.EveryPhase.Stress.Killing.tilted_boost` | lemma | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L41) |  |
| `YM.EveryPhase.Stress.Killing.tilted_add` | lemma | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L47) |  |
| `YM.EveryPhase.Stress.Killing.tilted_skew` | lemma | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L48) |  |
| `YM.EveryPhase.Stress.Killing.momentum` | lemma | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L56) |  |
| `YM.EveryPhase.Stress.Killing.slope` | lemma | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L62) |  |
| `YM.EveryPhase.Stress.tide` | def | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L77) |  |
| `YM.EveryPhase.Stress.tide_analytic` | lemma | [79](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L79) |  |
| `YM.EveryPhase.Stress.hole_replace` | lemma | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L83) |  |
| `YM.EveryPhase.Stress.emitsL` | lemma | [89](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L89) |  |
| `YM.EveryPhase.Stress.tide_div` | lemma | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L99) |  |
| `YM.EveryPhase.Stress.lodge_cont` | lemma | [135](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L135) |  |
| `YM.EveryPhase.Stress.lay_time` | lemma | [143](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L143) |  |
| `YM.EveryPhase.Stress.needle` | def | [145](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L145) |  |
| `YM.EveryPhase.Stress.lay_space` | lemma | [146](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L146) |  |
| `YM.EveryPhase.Stress.lodge_z` | lemma | [154](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L154) |  |
| `YM.EveryPhase.Stress.lodge_r` | lemma | [168](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L168) |  |
| `YM.EveryPhase.Stress.lodge_smooth` | lemma | [182](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L182) |  |
| `YM.EveryPhase.Stress.laid_hol` | lemma | [204](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L204) |  |
| `YM.EveryPhase.Stress.hole_hol` | lemma | [213](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L213) |  |
| `YM.EveryPhase.Stress.lodge_hol` | lemma | [218](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Killing.lean#L218) |  |

Covered by [Killing fields](../roadmap/every-phase/killing-field.md) (`YM.EveryPhase.Stress.Killing`, `YM.EveryPhase.Stress.Killing.realV`, `YM.EveryPhase.Stress.Killing.w`, `YM.EveryPhase.Stress.Killing.we`); and [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) (`YM.EveryPhase.Stress.tide`).

Lean-side notes:

- The field `ok` is `YM.Next.BOUNDARY.Descent.tangent`: the transpose of the matrix equals minus its conjugate by the time reflection `YM.Next.BOUNDARY.theta`. Since the Minkowski metric diagonal (time 1, space -1) is minus the time reflection, this is the usual Lorentz-algebra condition; the killing-field article states the Lean form and the equivalence.
- `YM.EveryPhase.Stress.Killing.w` includes the Wick factor `YM.EveryPhase.Stress.zeta` and is defined on all complex points, not only on the tube; `YM.EveryPhase.Stress.Killing.we` is its value at the Wick-rotated point. `YM.EveryPhase.Stress.Killing.w_real` and `YM.EveryPhase.Stress.Killing.w_wick` connect the real and Euclidean forms.
- `YM.EveryPhase.Stress.zeta_wick` (Tensor.lean:23) proves that each Wick factor times the corresponding factor of `YM.Next.BOUNDARY.wick` is 1, so the rotation factors of the killing-field article are the inverses of the Wick factors.
- `YM.EveryPhase.Stress.tide` (integrated-current-jump) is declared in this file, at line 77. `YM.EveryPhase.Stress.tide_analytic` (line 79) proves its analyticity on the tube when the Laplace family is holomorphic there (its hypothesis `FullBody`).

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Next.BOUNDARY.Descent.tangent` | [YM/Next/BOUNDARY/Derived.lean:21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derived.lean#L21) | [Killing fields](../roadmap/every-phase/killing-field.md) |
| `YM.Next.BOUNDARY.theta` | [YM/Next/BOUNDARY/Coordinates.lean:84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Coordinates.lean#L84) | [Killing fields](../roadmap/every-phase/killing-field.md) |
| `YM.M4` | [YM/Space/Orthogonal.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L19) | [Killing fields](../roadmap/every-phase/killing-field.md) |
| `YM.Next.BOUNDARY.wick` | [YM/Next/BOUNDARY/Derivative.lean:30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derivative.lean#L30) | [Killing fields](../roadmap/every-phase/killing-field.md) |

### Light

`YM/EveryPhase/Light.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.averaged_bound` | lemma | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L17) |  |
| `YM.EveryPhase.char_int` | lemma | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L27) |  |
| `YM.EveryPhase.fee` | def | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L35) | Costs depend only on mass bound and spatial localization of the commutator. |
| `YM.EveryPhase.ringE` | def | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L40) |  |
| `YM.EveryPhase.measurable_ring` | lemma | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L41) |  |
| `YM.EveryPhase.annulus` | theorem | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L43) |  |
| `YM.EveryPhase.lowE` | def | [132](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L132) |  |
| `YM.EveryPhase.measurable_low` | lemma | [133](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L133) |  |
| `YM.EveryPhase.dyadic` | theorem | [135](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L135) |  |
| `YM.EveryPhase.νletter` | def | [173](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L173) |  |
| `YM.EveryPhase.word_pair` | lemma | [179](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L179) |  |
| `YM.EveryPhase.sum_pair` | lemma | [185](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L185) |  |
| `YM.EveryPhase.word_bound` | theorem | [197](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L197) |  |
| `YM.EveryPhase.late` | theorem | [208](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L208) |  |
| `YM.EveryPhase.light_bound` | theorem | [221](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Light.lean#L221) |  |

Covered by [Zero-energy and low-energy regions](../roadmap/every-phase/energy-regions.md) (`YM.EveryPhase.lowE`); [Spectral measure of a finite sum of words](../roadmap/every-phase/word-spectral-measure.md) (`YM.EveryPhase.νletter`); and [Uniform low-energy bound](../roadmap/every-phase/low-energy-bound.md) (`YM.EveryPhase.light_bound`).

Lean-side notes:

- Moved out of the energy-regions article: `YM.EveryPhase.lowE` is defined for every real bound (empty for bounds at most 0) and is measurable by `YM.EveryPhase.measurable_low` (line 133).
- Moved out of the word-spectral-measure article: the spectral measure is finite by the unnamed instance on `YM.EveryPhase.νletter` (lines 176-177), from the field `finite` of `YM.Spectral.PVM`.
- Moved out of the low-energy-bound article: the bounded value equals the pairing of the word vector with the spectral projection of the low-energy region, by the field `at_pair` of `YM.Spectral.PVM` (measurable sets only) together with `YM.EveryPhase.measurable_low`.
- Indirect proof link of low-energy-bound: `YM.EveryPhase.light_bound` reaches `YM.EveryPhase.strict_evaluation` through `YM.EveryPhase.word_bound` (line 197), `YM.EveryPhase.sum_pair`, `YM.EveryPhase.word_pair`, `YM.EveryPhase.word_continuity` and `YM.EveryPhase.eager`, none of which has an article. The proof also uses `YM.EveryPhase.late` (line 208), `YM.EveryPhase.annulus` (line 43) and `YM.EveryPhase.dyadic` (line 135).

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Spectral.PVM` | [YM/Spectral/Projection.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spectral/Projection.lean#L19) | [Spectral measure of a finite sum of words](../roadmap/every-phase/word-spectral-measure.md), [Uniform low-energy bound](../roadmap/every-phase/low-energy-bound.md) |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Spectral measure of a finite sum of words](../roadmap/every-phase/word-spectral-measure.md) |
| `YM.time` | [YM/Space/Configurations.lean:27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L27) | [Zero-energy and low-energy regions](../roadmap/every-phase/energy-regions.md) |

### Pack

`YM/EveryPhase/Pack.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.x_enter` | lemma, private | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L24) |  |
| `YM.EveryPhase.x_train` | lemma, private | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L32) |  |
| `YM.EveryPhase.buys` | lemma, private | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L53) | Diagonal train estimate suffices (in a chamber of a Hierarchy). |
| `YM.EveryPhase.actual` | lemma, private | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L76) |  |
| `YM.EveryPhase.sameBound` | lemma | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L95) | The unselected multiplet bounds themselves work, uniformly for every character. |
| `YM.EveryPhase.Almanac` | structure | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L117) | Book of contours and reflection constructions, indexed by characters of precisely the compression algebra in Final. No exceptional set deletion; on all of it we can use the existing Wightman construction through `FieldCore` (which requires all of Realizes except vacuum uniqueness). Used below when vacuum uniqueness isn't known yet. Even choose the *same* spaces, contour, and fields as the old construction at its selected point, so U at that point connects those actual two spaces. All operators refer to S.Union. |
| `YM.EveryPhase.Almanac.chambers` | field | [118](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L118) |  |
| `YM.EveryPhase.Almanac.spreads` | field | [119](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L119) |  |
| `YM.EveryPhase.Almanac.pantries` | field | [120](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L120) |  |
| `YM.EveryPhase.Almanac.contours` | field | [121](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L121) |  |
| `YM.EveryPhase.Almanac.cards` | field | [122](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L122) |  |
| `YM.EveryPhase.Almanac.actors` | field | [123](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L123) |  |
| `YM.EveryPhase.Almanac.letters` | field | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L124) |  |
| `YM.EveryPhase.Almanac.spins` | field | [125](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L125) |  |
| `YM.EveryPhase.Almanac.cores` | field | [126](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L126) |  |
| `YM.EveryPhase.Almanac.J` | field | [127](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L127) |  |
| `YM.EveryPhase.Almanac.links` | field | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L128) |  |
| `YM.EveryPhase.Almanac.baseC` | field | [129](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L129) |  |
| `YM.EveryPhase.Almanac.baseS` | field | [130](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L130) |  |
| `YM.EveryPhase.Almanac.baseB` | field | [131](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L131) |  |
| `YM.EveryPhase.Almanac.baseR` | field | [132](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L132) |  |
| `YM.EveryPhase.storeys` | lemma | [134](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L134) |  |
| `YM.EveryPhase.almanac` | lemma | [157](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L157) |  |
| `YM.EveryPhase.Almanac.priced` | lemma | [196](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L196) |  |
| `YM.EveryPhase.Almanac.copy` | lemma | [202](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L202) | records the uniform-in-character arbitrary-copy bounds explicitly. |
| `YM.EveryPhase.Almanac.almostEvery` | lemma | [208](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pack.lean#L208) |  |

Covered by [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) (`YM.EveryPhase.Almanac`).

Lean-side notes:

- `YM.EveryPhase.Almanac` is data, not a proposition. Its field `contours` is a bare continuation with no property; that it continues the phase table with non-tangential boundary values comes only through `cards` (the fields `fromPhase` and `corner` of `YM.Next.BOUNDARY.Compatible`). No vacuum uniqueness is stored: the Wightman data satisfy `YM.Next.BOUNDARY.FieldCore`.
- `letters` equates the star operations and `spins` the whole label action. By `ties` of `YM.Boundary.Spins.Descends` (YM/Fields/Star.lean:27) and `YM.Table.pin_inj` (YM/Euclid/Union.lean:29), for actions satisfying the descent laws the graded-field actions are determined by the action on labels; the articles state equality on labels and on graded fields, as the structure does.
- `baseS` is a heterogeneous equality because the slab operators at the selected character live over its OS space, which equals the selected one only propositionally (`baseC`).
- The boundary map is unique among maps with the boundary-isometry property by the field `attachments` of `YM.Next.BOUNDARY.Compatible`, which the family carries through `cards`; the family itself stores one map.
- Existence of a family is `YM.EveryPhase.almanac` (line 157); uniform slab domination is `YM.EveryPhase.sameBound` (line 95). `YM.EveryPhase.Almanac.priced`, `YM.EveryPhase.Almanac.copy`, `YM.EveryPhase.Almanac.almostEvery` and `YM.EveryPhase.storeys` have no article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Spec.Final` | [YM/Spec/Closed.lean:64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spec/Closed.lean#L64) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.OS.Selection` | [YM/Phase/Mixture.lean:127](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Phase/Mixture.lean#L127) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.OS.Spread.Resolution` | [YM/Phase/Mixture.lean:65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Phase/Mixture.lean#L65) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.OS.Chamber` | [YM/OS/Dynamics.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/OS/Dynamics.lean#L57) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.OS.Spread` | [YM/OS/Slabs.lean:101](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/OS/Slabs.lean#L101) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.OS.Spread.Laws` | [YM/OS/Slabs.lean:153](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/OS/Slabs.lean#L153) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Bid.Pantry` | [YM/Bid/Corners.lean:23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Bid/Corners.lean#L23) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.DiffPlan` | [YM/Euclid/Differential.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L20) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Contour` | [YM/Boundary/Contour.lean:115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L115) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Contour.From` | [YM/Boundary/Contour.lean:119](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L119) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Waves.NonTangentialFree` | [YM/Boundary/Contour.lean:96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L96) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Next.BOUNDARY.Compatible` | [YM/Next/BOUNDARY/Stage.lean:190](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Stage.lean#L190) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Org.Show.Rhythm` | [YM/Org/Theatre.lean:17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Org/Theatre.lean#L17) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Org.Show.Reveals` | [YM/Org/Theatre.lean:47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Org/Theatre.lean#L47) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Next.BOUNDARY.FieldCore` | [YM/Next/BOUNDARY/Core.lean:34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Core.lean#L34) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Next.BOUNDARY.Attachment` | [YM/Next/BOUNDARY/Core.lean:156](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Core.lean#L156) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Action.Intervenes` | [YM/Fields/Spectrum.lean:103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Spectrum.lean#L103) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Small` | [YM/Fields/Tall.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Tall.lean#L19) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Small.concretized` | [YM/Fields/Tall.lean:25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Tall.lean#L25) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Spins` | [YM/Fields/Star.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L22) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.Spins.Descends` | [YM/Fields/Star.lean:26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L26) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |
| `YM.Boundary.starRead` | [YM/Fields/Star.lean:42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L42) | [Family of reconstructions over the phases](../roadmap/every-phase/reconstruction-family.md) |

### Pages

`YM/EveryPhase/Pages.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.power` | theorem | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L19) |  |
| `YM.EveryPhase.scalePath` | def | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L52) |  |
| `YM.EveryPhase.scaleIm` | def | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L54) |  |
| `YM.EveryPhase.path_im` | lemma | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L56) |  |
| `YM.EveryPhase.path_one` | lemma | [59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L59) |  |
| `YM.EveryPhase.path_I` | lemma | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L61) |  |
| `YM.EveryPhase.path_open` | lemma | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L64) |  |
| `YM.EveryPhase.ribbon` | def | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L80) |  |
| `YM.EveryPhase.ribbon_zero` | lemma | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L81) |  |
| `YM.EveryPhase.ribbon_one` | lemma | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L82) |  |
| `YM.EveryPhase.open_ribbon` | lemma | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L83) |  |
| `YM.EveryPhase.pre_ribbon` | lemma | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L84) |  |
| `YM.EveryPhase.path_strict` | lemma | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L86) |  |
| `YM.EveryPhase.path_shift` | lemma | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L92) |  |
| `YM.EveryPhase.from_imaginary` | lemma | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L96) |  |
| `YM.EveryPhase.integral_holomorphic` | theorem | [114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L114) | An integrable locally uniform bound suffices here too; only need the constant-bound finite-measure version. |
| `YM.EveryPhase.imaginary_evaluation` | lemma | [152](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L152) |  |
| `YM.EveryPhase.path_price` | lemma, private | [172](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L172) |  |
| `YM.EveryPhase.path_diff` | lemma, private | [184](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L184) |  |
| `YM.EveryPhase.strict_evaluation` | lemma | [193](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pages.lean#L193) | At strict heights -- includes ALL points, not just tested limits. |

Covered by [Continuations at strict heights: continuity and barycenter in the phase](../roadmap/every-phase/strict-height-continuity-barycenter.md) (`YM.EveryPhase.strict_evaluation`).

Lean-side notes:

- In `YM.EveryPhase.strict_evaluation` the number of points is implicit, so the statement holds for every number including 0; the configuration is unrestricted (no distinctness, no time order); only the heights are assumed strictly increasing.
- Moved out of the strict-height-continuity-barycenter article: the lemma states only continuity and the integral identity. Its proof gets integrability of the evaluation in the character from continuity on the compact phase space (lines 220-221, through `HasCompactSupport.of_compactSpace`), with the probability instance of the phase measure (line 217).
- The proof goes through `YM.EveryPhase.imaginary_evaluation` (line 152), `YM.EveryPhase.power` (line 19), `YM.EveryPhase.propagate_limit` (Vitali.lean:67) and `YM.EveryPhase.integral_holomorphic` (line 114), none of which has an article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Waves.restricted` | [YM/Boundary/Contour.lean:63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L63) | [Continuations at strict heights: continuity and barycenter in the phase](../roadmap/every-phase/strict-height-continuity-barycenter.md) |
| `YM.Boundary.east` | [YM/Boundary/Contour.lean:27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L27) | [Continuations at strict heights: continuity and barycenter in the phase](../roadmap/every-phase/strict-height-continuity-barycenter.md) |
| `YM.Spec.Final` | [YM/Spec/Closed.lean:64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spec/Closed.lean#L64) | [Continuations at strict heights: continuity and barycenter in the phase](../roadmap/every-phase/strict-height-continuity-barycenter.md) |
| `YM.OS.Spread.Resolution` | [YM/Phase/Mixture.lean:65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Phase/Mixture.lean#L65) | [Continuations at strict heights: continuity and barycenter in the phase](../roadmap/every-phase/strict-height-continuity-barycenter.md) |

### Polynomials

`YM/EveryPhase/Polynomials.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.SumOfWords` | abbrev | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L14) |  |
| `YM.EveryPhase.monomial` | def | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L16) |  |
| `YM.EveryPhase.append_op` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L20) |  |
| `YM.EveryPhase.evaluate_word` | lemma | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L25) |  |
| `YM.EveryPhase.star_monomial` | lemma | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L30) |  |
| `YM.EveryPhase.operator` | def | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L38) |  |
| `YM.EveryPhase.reverseP` | def | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L42) |  |
| `YM.EveryPhase.star_operator` | theorem | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L44) |  |
| `YM.EveryPhase.acted` | def | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L54) |  |
| `YM.EveryPhase.stands` | def | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L55) |  |
| `YM.EveryPhase.stands_cons` | lemma | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L57) |  |
| `YM.EveryPhase.cov_operator_vac` | lemma | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L64) |  |
| `YM.EveryPhase.star_moved` | lemma | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L72) |  |
| `YM.EveryPhase.boundedWord` | def | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L83) |  |
| `YM.EveryPhase.finite` | def | [85](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L85) |  |
| `YM.EveryPhase.spacelikeWords` | def | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L87) |  |
| `YM.EveryPhase.mon_comm` | lemma, private | [89](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L89) |  |
| `YM.EveryPhase.op_comm` | theorem | [106](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L106) |  |
| `YM.EveryPhase.transl_support` | lemma | [121](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L121) |  |
| `YM.EveryPhase.compact_bounds` | lemma, private | [130](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L130) |  |
| `YM.EveryPhase.bounded_scope` | lemma, private | [137](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L137) |  |
| `YM.EveryPhase.distant` | lemma | [146](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L146) |  |
| `YM.EveryPhase.fin_reverse` | lemma | [162](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L162) |  |
| `YM.EveryPhase.delta` | def | [171](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L171) |  |
| `YM.EveryPhase.comm_expect` | theorem | [175](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Polynomials.lean#L175) |  |

Covered by [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md) (`YM.EveryPhase.SumOfWords`, `YM.EveryPhase.monomial`, `YM.EveryPhase.operator`, `YM.EveryPhase.stands`); and [Compactly supported sums of words](../roadmap/every-phase/compactly-supported-sums.md) (`YM.EveryPhase.boundedWord`, `YM.EveryPhase.finite`).

Lean-side notes:

- `YM.EveryPhase.SumOfWords` is a list of pairs of a coefficient and a word: order and repetition count, and zero coefficients are allowed. In `YM.EveryPhase.monomial` the first letter is applied last; `YM.EveryPhase.operator` of the empty list is 0.
- Moved out of the sums-of-words article: `YM.EveryPhase.stands_cons` (line 57) gives the vector of a sum with one more entry. Since the vector of the empty word is the vacuum (`YM.Boundary.Fields.vector`, YM/Fields/System.lean:31-35), the vacuum is the vector of the one-entry sum of coefficient 1 and the empty word; `YM.EveryPhase.extends_decay` restates this inside its proof (Vacuum.lean:61-62). The vector of the empty sum is 0 because `YM.EveryPhase.operator` of the empty list is 0.
- The common label space is `YM.Table.Union`, the supremum of the ranges of the maps `YM.Table.spectra` into the functions of exterior data, each injective by `YM.Table.pin_inj` (YM/Euclid/Union.lean:29).
- The compactly-supported-sums article identifies the allowed tests with the smooth compactly supported functions; the inclusion of the latter in Schwartz space is Mathlib's `HasCompactSupport.toSchwartzMap` (Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:555 at the pinned revision). `YM.EveryPhase.finite` constrains every entry, zero coefficients included, so it is a condition on the list, not on the operator.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Boundary.Letter` | [YM/Fields/Star.lean:38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L38) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md) |
| `YM.Boundary.Sentence` | [YM/Fields/Star.lean:39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Star.lean#L39) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md), [Compactly supported sums of words](../roadmap/every-phase/compactly-supported-sums.md) |
| `YM.Boundary.Fields` | [YM/Fields/System.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L22) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md) |
| `YM.Table.observations` | [YM/Euclid/Union.lean:23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Union.lean#L23) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md) |
| `YM.Table.Union` | [YM/Euclid/Union.lean:24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Union.lean#L24) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md) |
| `YM.Table.spectra` | [YM/Euclid/Null.lean:93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Null.lean#L93) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md) |
| `YM.Boundary.Test4` | [YM/Distribution/Product.lean:122](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Product.lean#L122) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md), [Compactly supported sums of words](../roadmap/every-phase/compactly-supported-sums.md) |
| `YM.Boundary.Probe` | [YM/Distribution/Tests.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Distribution/Tests.lean#L20) | [Finite sums of words and their vectors](../roadmap/every-phase/sums-of-words.md), [Compactly supported sums of words](../roadmap/every-phase/compactly-supported-sums.md) |

### Projection

`YM/EveryPhase/Projection.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.reaches` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L20) |  |
| `YM.EveryPhase.zeroE` | def | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L30) |  |
| `YM.EveryPhase.aboveE` | def | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L31) |  |
| `YM.EveryPhase.zeroE_m` | lemma | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L32) |  |
| `YM.EveryPhase.aboveE_m` | lemma | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L33) |  |
| `YM.EveryPhase.boltz` | def | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L35) |  |
| `YM.EveryPhase.direct` | lemma | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L37) |  |
| `YM.EveryPhase.boltzmann` | lemma | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L44) |  |
| `YM.EveryPhase.boltz_int` | lemma | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L52) |  |
| `YM.EveryPhase.boltz_zero_atom` | lemma | [59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L59) |  |
| `YM.EveryPhase.reflection_projection` | theorem | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L77) |  |
| `YM.EveryPhase.bHeat` | def | [94](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L94) | The actual real-time heat kernel H≥0 from the PVM; realized on the whole boundary space. bHeat J V (diagonal identity below characterizes this operator). |
| `YM.EveryPhase.bHeat_pair` | lemma | [97](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L97) |  |
| `YM.EveryPhase.bHeat_limit` | lemma | [102](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L102) |  |
| `YM.EveryPhase.bHeat_ground` | lemma | [111](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L111) |  |
| `YM.EveryPhase.cave` | lemma | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L124) |  |
| `YM.EveryPhase.residual` | lemma | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L128) |  |
| `YM.EveryPhase.residual_pair` | lemma | [145](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Projection.lean#L145) |  |

Covered by [Zero-energy and low-energy regions](../roadmap/every-phase/energy-regions.md) (`YM.EveryPhase.zeroE`); and [Heat operators pulled back along a bounded map](../roadmap/every-phase/boundary-heat-semigroup.md) (`YM.EveryPhase.bHeat`).

Lean-side notes:

- Moved out of the energy-regions article: the zero-energy region is measurable by `YM.EveryPhase.zeroE_m` (line 32).
- Moved out of the boundary-heat-semigroup article: `YM.EveryPhase.bHeat` states no semigroup law and puts no condition on the bounded map. It is used with the family's boundary map and OS space (`YM.EveryPhase.Almanac.J`, `YM.EveryPhase.Almanac.chambers`) at Decay.lean:114 and 176, Extension.lean:62 and Vacuum.lean:54 and 90. The isometry enters only through `YM.Next.BOUNDARY.Attachment` in `YM.EveryPhase.bHeat_pair` (line 97), `YM.EveryPhase.bHeat_limit` (line 102) and `YM.EveryPhase.bHeat_ground` (line 111).
- `YM.EveryPhase.reaches` (line 20) applies `YM.EveryPhase.onto` at each character, taking its staging hypotheses from the field `reveals` of `YM.Next.BOUNDARY.Compatible` and rewriting the label action with `spins` of `YM.EveryPhase.Almanac`.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.E4` | [YM/Space/Configurations.lean:24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L24) | [Zero-energy and low-energy regions](../roadmap/every-phase/energy-regions.md) |
| `YM.time` | [YM/Space/Configurations.lean:27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L27) | [Zero-energy and low-energy regions](../roadmap/every-phase/energy-regions.md) |
| `YM.timeAxis` | [YM/Space/Index.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L20) | [Zero-energy and low-energy regions](../roadmap/every-phase/energy-regions.md) |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Heat operators pulled back along a bounded map](../roadmap/every-phase/boundary-heat-semigroup.md) |
| `YM.OS.Chamber` | [YM/OS/Dynamics.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/OS/Dynamics.lean#L57) | [Heat operators pulled back along a bounded map](../roadmap/every-phase/boundary-heat-semigroup.md) |
| `YM.OS.Semigroup` | [YM/OS/Flow.lean:94](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/OS/Flow.lean#L94) | [Heat operators pulled back along a bounded map](../roadmap/every-phase/boundary-heat-semigroup.md) |

### Pure

`YM/EveryPhase/Pure.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.fibers` | lemma | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pure.lean#L13) |  |
| `YM.EveryPhase.Stress.pure_clock` | theorem | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Pure.lean#L43) |  |

Covered by [The current jump at Euclidean points](../roadmap/every-phase/euclidean-current-jump.md) (`YM.EveryPhase.Stress.pure_clock`).

Lean-side notes:

- `YM.EveryPhase.Stress.pure_clock` assumes no group laws of the rotations: only their generators enter, through `YM.Table.StressLaws` and `YM.Next.BOUNDARY.Descent.rankAction`. No hypothesis keeps the other points out of the support of the cutoff; the only constraint on the cutoff is that it equals 1 near the distinguished spatial point. `YM.Work.C20.ordered` makes the slot order the time order.
- The proof uses `YM.EveryPhase.Stress.euclidean_shell` (Shell.lean:128), `YM.EveryPhase.Stress.fibers` (line 13), `preparation`, `hatChi`, `split_space` and `curtainsFTC`; it has no proof link in the vault.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Work.C20.ordered` | [YM/Work/C20.lean:145](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Work/C20.lean#L145) | [The current jump at Euclidean points](../roadmap/every-phase/euclidean-current-jump.md) |
| `YM.Table.StressLaws` | [YM/Euclid/Stress.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L90) | [The current jump at Euclidean points](../roadmap/every-phase/euclidean-current-jump.md) |
| `YM.Table.Window` | [YM/Euclid/Stress.lean:72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L72) | [The current jump at Euclidean points](../roadmap/every-phase/euclidean-current-jump.md) |
| `YM.Table.Stress` | [YM/Euclid/Stress.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L57) | [The current jump at Euclidean points](../roadmap/every-phase/euclidean-current-jump.md) |
| `YM.Bid.ink` | [YM/Bid/Corners.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Bid/Corners.lean#L90) | [The current jump at Euclidean points](../roadmap/every-phase/euclidean-current-jump.md) |
| `YM.Table.Rotation` | [YM/Euclid/Stress.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L22) | [The current jump at Euclidean points](../roadmap/every-phase/euclidean-current-jump.md) |

### Seeds

`YM/EveryPhase/Seeds.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.hatChi` | def | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L20) |  |
| `YM.EveryPhase.Stress.hat_diff` | lemma | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L22) |  |
| `YM.EveryPhase.Stress.hat_size` | lemma | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L26) |  |
| `YM.EveryPhase.Stress.hat_jets` | lemma | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L43) |  |
| `YM.EveryPhase.Stress.pureReady` | def | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L81) |  |
| `YM.EveryPhase.Stress.preparation` | lemma | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L84) |  |
| `YM.EveryPhase.Stress.hat_window` | lemma | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L91) |  |
| `YM.EveryPhase.Stress.split_space` | lemma | [120](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L120) |  |
| `YM.EveryPhase.Stress.curtainsFTC` | lemma | [135](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Seeds.lean#L135) |  |

### Shell

`YM/EveryPhase/Shell.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.first` | def | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L13) |  |
| `YM.EveryPhase.Stress.first_coord` | lemma | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L19) |  |
| `YM.EveryPhase.Stress.first_next` | lemma | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L20) |  |
| `YM.EveryPhase.Stress.hole_first` | lemma | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L22) |  |
| `YM.EveryPhase.Stress.seat_first` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L24) |  |
| `YM.EveryPhase.Stress.pureU` | def | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L27) |  |
| `YM.EveryPhase.Stress.pureDock` | def | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L28) |  |
| `YM.EveryPhase.Stress.pure_time` | lemma | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L29) |  |
| `YM.EveryPhase.Stress.pure_lay` | lemma | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L31) |  |
| `YM.EveryPhase.Stress.ink_hole` | lemma | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L34) |  |
| `YM.EveryPhase.Stress.sets_scene` | lemma | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L39) |  |
| `YM.EveryPhase.Stress.opens_scene` | lemma | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L42) |  |
| `YM.EveryPhase.Stress.lodge_sets` | lemma | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L46) |  |
| `YM.EveryPhase.Stress.ordered_conf` | lemma | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L51) |  |
| `YM.EveryPhase.Stress.linger` | def | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L55) |  |
| `YM.EveryPhase.Stress.ordering` | def | [66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L66) |  |
| `YM.EveryPhase.Stress.order_corr` | lemma | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L68) |  |
| `YM.EveryPhase.Stress.curtain` | def | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L81) |  |
| `YM.EveryPhase.Stress.waveT_pure` | lemma | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L84) |  |
| `YM.EveryPhase.Stress.one_variable` | lemma | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L95) |  |
| `YM.EveryPhase.Stress.we_split` | lemma | [108](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L108) |  |
| `YM.EveryPhase.Stress.grounds` | def | [121](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L121) |  |
| `YM.EveryPhase.Stress.taskE` | def | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L124) |  |
| `YM.EveryPhase.Stress.euclidean_shell` | lemma | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Shell.lean#L128) |  |

Covered by [Euclidean value of the current jump](../roadmap/every-phase/euclidean-jump-value.md) (`YM.EveryPhase.Stress.pureU`, `YM.EveryPhase.Stress.pureDock`, `YM.EveryPhase.Stress.taskE`).

Lean-side notes:

- `YM.EveryPhase.Stress.taskE` and `YM.EveryPhase.Stress.taskC` see the rotations only through `YM.Next.BOUNDARY.Descent.rankAction` (YM/Next/BOUNDARY/Derived.lean:114-118, with the closed form `rank_eq`), built from the generators alone; the group action and its laws are not used.
- `YM.EveryPhase.Stress.task_pure` (Through.lean:18) shows that the continued value at the purely imaginary base point equals the Euclidean value for time-ordered points.
- `YM.EveryPhase.Stress.euclidean_shell` (line 128), the Euclidean contact identity, has no article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Table.useAt` | [YM/Euclid/Lift.lean:69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Lift.lean#L69) | [Euclidean value of the current jump](../roadmap/every-phase/euclidean-jump-value.md) |
| `YM.Table.Tag` | [YM/Euclid/Lift.lean:66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Lift.lean#L66) | [Euclidean value of the current jump](../roadmap/every-phase/euclidean-jump-value.md) |
| `YM.Table.Rotation` | [YM/Euclid/Stress.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L22) | [Euclidean value of the current jump](../roadmap/every-phase/euclidean-jump-value.md) |
| `YM.Next.BOUNDARY.Descent.rankAction` | [YM/Next/BOUNDARY/Derived.lean:114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derived.lean#L114) | [Euclidean value of the current jump](../roadmap/every-phase/euclidean-jump-value.md) |
| `YM.DiffPlan` | [YM/Euclid/Differential.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L20) | [Euclidean value of the current jump](../roadmap/every-phase/euclidean-jump-value.md) |

### Slots

`YM/EveryPhase/Slots.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.pair` | def | [11](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L11) |  |
| `YM.EveryPhase.Stress.hole` | def | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L13) |  |
| `YM.EveryPhase.Stress.hole_self` | lemma | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L14) |  |
| `YM.EveryPhase.Stress.hole_next` | lemma | [15](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L15) |  |
| `YM.EveryPhase.Stress.first_slot` | lemma | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L16) |  |
| `YM.EveryPhase.Stress.second_slot` | lemma | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L17) |  |
| `YM.EveryPhase.Stress.switch_hole` | lemma | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L19) |  |
| `YM.EveryPhase.Stress.seat` | def | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L39) |  |
| `YM.EveryPhase.Stress.seat_seat` | lemma | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L41) |  |
| `YM.EveryPhase.Stress.seat_next` | lemma | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L42) |  |
| `YM.EveryPhase.Stress.cushion` | def | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L43) |  |
| `YM.EveryPhase.Stress.chairs` | def | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L56) |  |
| `YM.EveryPhase.Stress.chairMeasure` | lemma | [58](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L58) |  |
| `YM.EveryPhase.Stress.laid` | def | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L62) | real spatial arguments throughout. |
| `YM.EveryPhase.Stress.lay` | def | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L63) |  |
| `YM.EveryPhase.Stress.lay_real` | lemma | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L64) |  |
| `YM.EveryPhase.Stress.laid_at` | lemma | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L68) |  |
| `YM.EveryPhase.Stress.laid_inside` | lemma | [74](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L74) |  |
| `YM.EveryPhase.Stress.laid_place` | lemma | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L76) |  |
| `YM.EveryPhase.Stress.lodge` | def | [79](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L79) |  |
| `YM.EveryPhase.Stress.lodge_name` | lemma | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L82) |  |
| `YM.EveryPhase.Stress.hole_ord` | lemma | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L88) |  |
| `YM.EveryPhase.Stress.affords` | lemma | [101](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Slots.lean#L101) | local uniform strip over exterior complex times. |

Covered by [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) (`YM.EveryPhase.Stress.pair`); [Insertion into a slot](../roadmap/every-phase/slot-insertion.md) (`YM.EveryPhase.Stress.hole`); [Tested stress insertion next to a field](../roadmap/every-phase/tested-current-jump.md) (`YM.EveryPhase.Stress.seat`, `YM.EveryPhase.Stress.cushion`, `YM.EveryPhase.Stress.chairs`); and [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) (`YM.EveryPhase.Stress.laid`, `YM.EveryPhase.Stress.lodge`).

Lean-side notes:

- `YM.EveryPhase.Stress.hole` is the nondependent insertion of an entry into a tuple; `YM.EveryPhase.Stress.hole_self` and `YM.EveryPhase.Stress.hole_next` are its simplification lemmas. `YM.EveryPhase.Stress.seat_seat` and `YM.EveryPhase.Stress.seat_next` give the slot entries of `YM.EveryPhase.Stress.seat`; `YM.EveryPhase.Stress.chairMeasure` (line 58) shows that `YM.EveryPhase.Stress.chairs` preserves measure (not used in the articles).

### Strip

`YM/EveryPhase/Strip.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.compact_analytic_int` | lemma | [12](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L12) |  |
| `YM.EveryPhase.Stress.waveT` | def | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L61) |  |
| `YM.EveryPhase.Stress.harbors` | def | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L64) |  |
| `YM.EveryPhase.Stress.drift` | def | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L68) |  |
| `YM.EveryPhase.Stress.drift_at` | lemma | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L69) |  |
| `YM.EveryPhase.Stress.drift_compact` | lemma | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L70) |  |
| `YM.EveryPhase.Stress.docks` | def | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L77) |  |
| `YM.EveryPhase.Stress.waveT_cont` | lemma | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L81) |  |
| `YM.EveryPhase.Stress.harbors_cont` | lemma | [97](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L97) |  |
| `YM.EveryPhase.Stress.integral_harbors` | lemma | [111](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L111) |  |
| `YM.EveryPhase.Stress.harbors_hol` | lemma | [125](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L125) |  |
| `YM.EveryPhase.Stress.waveT_smooth` | lemma | [136](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L136) |  |
| `YM.EveryPhase.Stress.waveT_space` | lemma | [145](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L145) |  |
| `YM.EveryPhase.Stress.harbors_speed` | lemma | [156](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Strip.lean#L156) |  |

Covered by [Spatially integrated current and its jump](../roadmap/every-phase/integrated-current-jump.md) (`YM.EveryPhase.Stress.waveT`, `YM.EveryPhase.Stress.harbors`); and [Admissible base points for the current jump](../roadmap/every-phase/jump-admissibility.md) (`YM.EveryPhase.Stress.drift`).

Lean-side notes:

- `YM.EveryPhase.Stress.harbors` is a Bochner integral over space, which reads 0 when the integrand is not integrable. `YM.EveryPhase.Stress.drift` is the derivative along a standard basis vector of space.

### Surjective

`YM/EveryPhase/Surjective.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.fromRef` | def, private | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L21) |  |
| `YM.EveryPhase.fromTrain` | lemma, private | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L28) |  |
| `YM.EveryPhase.fromPoint` | lemma, private | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L33) |  |
| `YM.EveryPhase.nextRef` | lemma, private | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L37) |  |
| `YM.EveryPhase.Room` | def, private | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L44) |  |
| `YM.EveryPhase.tailRoom` | lemma, private | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L47) |  |
| `YM.EveryPhase.pinned` | def, private | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L51) |  |
| `YM.EveryPhase.raw` | def, private | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L52) |  |
| `YM.EveryPhase.iz` | def, private | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L53) |  |
| `YM.EveryPhase.oneSlab` | lemma, private | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L55) |  |
| `YM.EveryPhase.euclideanRef` | lemma, private | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L65) |  |
| `YM.EveryPhase.euclideanShot` | lemma, private | [104](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L104) |  |
| `YM.EveryPhase.ample_room` | lemma, private | [114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L114) |  |
| `YM.EveryPhase.bright_shot` | lemma | [119](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L119) |  |
| `YM.EveryPhase.plant_ext` | lemma, private | [138](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L138) |  |
| `YM.EveryPhase.same_plant` | lemma, private | [148](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L148) |  |
| `YM.EveryPhase.ordered_covered` | lemma | [160](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L160) |  |
| `YM.EveryPhase.onto` | lemma | [178](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Surjective.lean#L178) |  |

Covered by [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) (`YM.EveryPhase.onto`).

Lean-side notes:

- The algebra argument of `YM.Org.Show.Reveals` is unused: no field of it mentions the algebra, and `YM.Org.Show.Lights` and `YM.Bid.Hull` do not take it. So the algebra hypothesis of `YM.EveryPhase.onto` is unconstrained, and the field `reveals` of `YM.Next.BOUNDARY.Compatible` does not depend on the record's field algebra beyond its type.
- The fields `linked` and `smears` of `YM.Next.BOUNDARY.Attachment` quantify over families realized by slab operators with no bound; the polynomial bound enters only through the staging's `price` field of `YM.Org.Show.Rhythm`.
- Translation covariance in the staging (`time` of `YM.Boundary.Small.Lamp`) transports words through the label action at the identity transformation. That this action is the identity is the field `identity` of `YM.Boundary.Spins.Descends`, which `YM.EveryPhase.onto` does not assume; hence the action at the identity in hypothesis 2(e) of the article.
- The proof uses `YM.EveryPhase.ordered_covered` (line 160), `YM.EveryPhase.bright_shot` (line 119), `YM.EveryPhase.margins_exists` (SurjectiveHelpers), `YM.EveryPhase.shot_in` (Hot.lean:111) and declarations of YM/Work/B14.lean; none has an article. The lemma is applied at each character of a family of reconstructions in `YM.EveryPhase.reaches` (Projection.lean:20).

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Next.BOUNDARY.Attachment` | [YM/Next/BOUNDARY/Core.lean:156](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Core.lean#L156) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Org.Show.Rhythm` | [YM/Org/Theatre.lean:17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Org/Theatre.lean#L17) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Org.Show.Lights` | [YM/Org/Theatre.lean:39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Org/Theatre.lean#L39) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Org.Show.Reveals` | [YM/Org/Theatre.lean:47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Org/Theatre.lean#L47) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Bid.Hull` | [YM/Bid/Grow.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Bid/Grow.lean#L19) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Table.Symmetric` | [YM/Euclid/Table.lean:71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Table.lean#L71) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Table.Smooth` | [YM/Euclid/Table.lean:88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Table.lean#L88) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Table.respects` | [YM/Euclid/Lift.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Lift.lean#L20) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Boundary.Waves.NonTangentialFree` | [YM/Boundary/Contour.lean:96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L96) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.OS.Chamber` | [YM/OS/Dynamics.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/OS/Dynamics.lean#L57) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Boundary.Small` | [YM/Fields/Tall.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Tall.lean#L19) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Boundary.Small.Lamp` | [YM/Fields/Tall.lean:96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Tall.lean#L96) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Boundary.Surface.Aurora` | [YM/Shift/Sol.lean:109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L109) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Boundary.NearPair.Panes` | [YM/Shift/Exchange.lean:33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Exchange.lean#L33) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |
| `YM.Boundary.Surface.Persists` | [YM/Fields/Stems.lean:38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/Stems.lean#L38) | [The boundary isometry is onto](../roadmap/every-phase/boundary-isometry-surjective.md) |

### SurjectiveHelpers

`YM/EveryPhase/SurjectiveHelpers.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Next.BOUNDARY.margins_exists` | lemma | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/SurjectiveHelpers.lean#L16) |  |

### Tensor

`YM/EveryPhase/Tensor.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.eta` | def | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L20) | Metric, for contravariant derivative. |
| `YM.EveryPhase.Stress.zeta` | def | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L22) |  |
| `YM.EveryPhase.Stress.zeta_wick` | lemma | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L23) |  |
| `YM.EveryPhase.Stress.zeta_square` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L24) |  |
| `YM.EveryPhase.Stress.M` | def | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L27) | Minkowski-normalized stress label. |
| `YM.EveryPhase.Stress.M_symmetric` | lemma | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L29) |  |
| `YM.EveryPhase.Stress.column` | def | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L33) | Tensor column convention. (The stress field requested below is Φ of these labels.) |
| `YM.EveryPhase.Stress.column_apply_one` | lemma | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L35) |  |
| `YM.EveryPhase.Stress.M_Herm` | lemma | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L38) |  |
| `YM.EveryPhase.Stress.column_mult` | lemma | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L52) |  |
| `YM.EveryPhase.Stress.rank_derivative` | theorem | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L67) | The rank action appearing below really is the infinitesimal action of the chosen label representation, along any differentiable Lorentz curve. |
| `YM.EveryPhase.Stress.rank_boost_formula` | lemma | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L81) |  |
| `YM.EveryPhase.Stress.speedTensor` | def | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L84) |  |
| `YM.EveryPhase.Stress.column_speed` | lemma | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L87) |  |
| `YM.EveryPhase.Stress.speedE` | lemma | [100](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L100) |  |
| `YM.EveryPhase.Stress.boost_scale` | lemma | [109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L109) |  |
| `YM.EveryPhase.Stress.speedM` | lemma | [121](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L121) |  |
| `YM.EveryPhase.Stress.column_var` | lemma | [135](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L135) |  |
| `YM.EveryPhase.Stress.boost_M` | lemma | [144](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L144) |  |
| `YM.EveryPhase.Stress.space_scale` | lemma | [171](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L171) |  |
| `YM.EveryPhase.Stress.rotate_M` | lemma | [183](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L183) |  |
| `YM.EveryPhase.Stress.transform_M` | lemma | [190](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L190) |  |
| `YM.EveryPhase.Stress.fieldM` | def | [206](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L206) | The stress as a tested operator on the common domain. |
| `YM.EveryPhase.Stress.TM` | lemma | [207](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L207) |  |
| `YM.EveryPhase.Stress.tensor_lorentz` | theorem | [210](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L210) |  |
| `YM.EveryPhase.Stress.tensor_herm` | theorem | [217](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L217) |  |
| `YM.EveryPhase.Stress.partialProbe` | def | [223](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L223) | Minus partial derivative on test. |
| `YM.EveryPhase.Stress.eucl_partial` | lemma | [224](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L224) |  |
| `YM.EveryPhase.Stress.tensor_conserved` | theorem | [227](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Tensor.lean#L227) |  |

Covered by [Minkowski stress labels and the stress field](../roadmap/every-phase/minkowski-stress-field.md) (`YM.EveryPhase.Stress.eta`, `YM.EveryPhase.Stress.zeta`, `YM.EveryPhase.Stress.M`, `YM.EveryPhase.Stress.fieldM`, `YM.EveryPhase.Stress.partialProbe`).

Lean-side notes:

- Moved out of the minkowski-stress-field article: `YM.EveryPhase.Stress.zeta_square` (line 24) proves that the square of each Wick factor is minus the metric entry, and `YM.EveryPhase.Stress.TM` (lines 207-208) that the stress field is minus the product of two Wick factors times the field of the Euclidean label. The injectivity of the inclusion of each graded label space in the common label space is `YM.Table.pin_inj` (YM/Euclid/Union.lean:29).
- `YM.EveryPhase.Stress.M` needs no symmetry of the stress; `YM.EveryPhase.Stress.M_symmetric` (line 29) needs conservation. `YM.EveryPhase.Stress.fieldM` is defined for arbitrary Wightman data, not for one phase.
- `YM.EveryPhase.Stress.partialProbe` is minus the derivative along a basis vector; `YM.EveryPhase.Stress.eucl_partial` relates it to the Euclidean test derivative by the factor `YM.Next.BOUNDARY.wick`.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Table.Stress` | [YM/Euclid/Stress.lean:57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L57) | [Minkowski stress labels and the stress field](../roadmap/every-phase/minkowski-stress-field.md) |
| `YM.Table.pin` | [YM/Euclid/Union.lean:26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Union.lean#L26) | [Minkowski stress labels and the stress field](../roadmap/every-phase/minkowski-stress-field.md) |
| `YM.Table.Union` | [YM/Euclid/Union.lean:24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Union.lean#L24) | [Minkowski stress labels and the stress field](../roadmap/every-phase/minkowski-stress-field.md) |
| `YM.Boundary.Wightman` | [YM/Fields/System.lean:117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L117) | [Minkowski stress labels and the stress field](../roadmap/every-phase/minkowski-stress-field.md) |
| `YM.Boundary.Fields` | [YM/Fields/System.lean:22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L22) | [Minkowski stress labels and the stress field](../roadmap/every-phase/minkowski-stress-field.md) |

### Through

`YM/EveryPhase/Through.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.Stress.taskC` | def | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Through.lean#L13) |  |
| `YM.EveryPhase.Stress.task_pure` | lemma | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Through.lean#L18) |  |
| `YM.EveryPhase.Stress.neighborhoods` | lemma | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Through.lean#L23) |  |
| `YM.EveryPhase.Stress.core_jump` | lemma | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Through.lean#L41) |  |
| `YM.EveryPhase.Stress.through_jump` | theorem | [129](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Through.lean#L129) | simultaneous limit, to simplify uniformity on test supports. |

Covered by [Continued value of the current jump](../roadmap/every-phase/continued-jump-value.md) (`YM.EveryPhase.Stress.taskC`); and [Joint limit of the current jump](../roadmap/every-phase/joint-current-jump-limit.md) (`YM.EveryPhase.Stress.through_jump`).

Lean-side notes:

- The weight of `YM.EveryPhase.Stress.taskC` is `YM.EveryPhase.Stress.Killing.w` at the distinguished complex point of the base point.
- Indirect proof link of joint-current-jump-limit: `YM.EveryPhase.Stress.through_jump` combines `YM.EveryPhase.Stress.first_ports` (Cross.lean:91), `YM.EveryPhase.Stress.variation` (Cross.lean:133) and `YM.EveryPhase.Stress.core_jump` (line 41); `YM.EveryPhase.Stress.core_jump`, which has no article, uses `YM.EveryPhase.Stress.pure_clock` and `YM.EveryPhase.Stress.task_pure`. The limit is taken along the product of the neighborhood filter of the base point and the right neighborhoods of 0.
- Neither `YM.EveryPhase.Stress.pure_clock` nor `YM.EveryPhase.Stress.through_jump` asks the spectator points to lie outside the support of the cutoff.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Bid.ink` | [YM/Bid/Corners.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Bid/Corners.lean#L90) | [Continued value of the current jump](../roadmap/every-phase/continued-jump-value.md), [Joint limit of the current jump](../roadmap/every-phase/joint-current-jump-limit.md) |
| `YM.Boundary.Surface.Aurora.emit` | [YM/Shift/Sol.lean:116](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Shift/Sol.lean#L116) | [Continued value of the current jump](../roadmap/every-phase/continued-jump-value.md) |
| `YM.Next.BOUNDARY.Descent.rankAction` | [YM/Next/BOUNDARY/Derived.lean:114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Next/BOUNDARY/Derived.lean#L114) | [Continued value of the current jump](../roadmap/every-phase/continued-jump-value.md) |
| `YM.DiffPlan` | [YM/Euclid/Differential.lean:20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Differential.lean#L20) | [Continued value of the current jump](../roadmap/every-phase/continued-jump-value.md) |
| `YM.Boundary.strict` | [YM/Boundary/Contour.lean:28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Boundary/Contour.lean#L28) | [Joint limit of the current jump](../roadmap/every-phase/joint-current-jump-limit.md) |
| `YM.Table.StressLaws` | [YM/Euclid/Stress.lean:90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Euclid/Stress.lean#L90) | [Joint limit of the current jump](../roadmap/every-phase/joint-current-jump-limit.md) |

### Vacuum

`YM/EveryPhase/Vacuum.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.groundvac` | lemma | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L16) |  |
| `YM.EveryPhase.proj_eq` | theorem | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L22) |  |
| `YM.EveryPhase.univ_of_closed` | lemma | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L42) |  |
| `YM.EveryPhase.extends_decay` | theorem | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L51) |  |
| `YM.EveryPhase.cluster_zero` | lemma | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L80) |  |
| `YM.EveryPhase.all_plant` | lemma | [115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L115) |  |
| `YM.EveryPhase.every` | theorem | [146](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L146) |  |
| `YM.EveryPhase.boundary_realizes` | lemma | [155](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L155) |  |
| `YM.EveryPhase.boundary_zero_energy` | lemma | [158](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vacuum.lean#L158) |  |

Covered by [No exceptional phase: zero energy is the vacuum](../roadmap/every-phase/zero-energy-projection-vacuum.md) (`YM.EveryPhase.all_plant`).

Lean-side notes:

- Moved out of the zero-energy-projection-vacuum article: since the vacuum has norm 1 (the field `norm` of `YM.Boundary.Fields.Total`, YM/Fields/System.lean:42, reached through the family's `YM.Next.BOUNDARY.FieldCore`), the identity says that the zero-energy projection is the orthogonal projection onto the multiples of the vacuum. The fixed-point form is `YM.EveryPhase.boundary_zero_energy` (line 158).
- Indirect proof links of zero-energy-projection-vacuum: the proof of `YM.EveryPhase.all_plant` goes through `YM.EveryPhase.cluster_zero` (line 80), `YM.EveryPhase.extends_decay` (line 51), `YM.EveryPhase.uniform_heat` (Decay.lean:113), `YM.EveryPhase.proj_eq` (line 22), `YM.EveryPhase.groundvac` (line 16), `YM.EveryPhase.bHeat_limit` and `YM.EveryPhase.Almanac.almostEvery` (Pack.lean:208), none of which has an article. Through them it uses `YM.EveryPhase.stands` and `YM.EveryPhase.operator` (line 131), `YM.EveryPhase.finite` (the hypothesis of `YM.EveryPhase.cluster_zero`, lines 133-137), `YM.EveryPhase.bHeat` (line 90), `YM.EveryPhase.sum_pair` and `YM.EveryPhase.uniform_heat` (lines 64-65; the latter uses `YM.EveryPhase.νletter` at Decay.lean:117), and `YM.EveryPhase.inverse_square` through `YM.EveryPhase.extends_decay`.
- `YM.EveryPhase.every` (line 146), `YM.EveryPhase.boundary_realizes` (line 155) and `YM.EveryPhase.boundary_zero_energy` (line 158) feed `YM.EveryPhase.all_characters` and have no article.

Unmapped prerequisites that these articles describe in words:

| Lean name | Location | Named in |
| --- | --- | --- |
| `YM.Spectral.PVM` | [YM/Spectral/Projection.lean:19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Spectral/Projection.lean#L19) | [No exceptional phase: zero energy is the vacuum](../roadmap/every-phase/zero-energy-projection-vacuum.md) |
| `YM.Boundary.Fields.vacuum` | [YM/Fields/System.lean:39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Fields/System.lean#L39) | [No exceptional phase: zero energy is the vacuum](../roadmap/every-phase/zero-energy-projection-vacuum.md) |

### Vitali

`YM/EveryPhase/Vitali.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.EveryPhase.boundedHere` | def | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vitali.lean#L16) | Local bound need only be on a tail, no control of early functions. |
| `YM.EveryPhase.nearby` | theorem | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vitali.lean#L19) |  |
| `YM.EveryPhase.equi_on` | lemma | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vitali.lean#L44) |  |
| `YM.EveryPhase.propagate_limit` | theorem | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Vitali.lean#L67) |  |

