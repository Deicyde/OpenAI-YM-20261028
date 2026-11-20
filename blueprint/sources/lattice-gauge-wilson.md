# Ledger of the setting: lattice, symmetries, gauge groups and the Wilson measure

These 34 files hold Armstrong's unit I.1, the setting of the construction:
the lattice and its paths, the symmetries of space and of Minkowski spacetime,
the gauge groups, and the Wilson measure. They are the files most of whose
declarations Armstrong assigns to the unit. This page lists every declaration
that AutoformBot's Lean source index records in them, file by file in line
order, with a link to the declaration's line in the original source at commit
3456e5e and its docstring. The article that covers a declaration says so in
the notes under the file's table; a declaration without such a note has no
article in this version of the book.

### Voices

`YM/AnalyticNext/CONNECTED_ACTIVITY_BOUNDS/Voices.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.AnalyticNext.ConnectedActivity.Due.carriage` | lemma | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/AnalyticNext/CONNECTED_ACTIVITY_BOUNDS/Voices.lean#L37) |  |
| `YM.AnalyticNext.ConnectedActivity.Due.post_goods` | lemma | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/AnalyticNext/CONNECTED_ACTIVITY_BOUNDS/Voices.lean#L43) |  |

### Mint

`YM/AnalyticNext/GRID_STOP_ATTENUATION/Alphabet/Mint.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.AnalyticNext.GridStop.Alphabet.mint_zero` | lemma | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/AnalyticNext/GRID_STOP_ATTENUATION/Alphabet/Mint.lean#L38) | Mint at stock exponent needs no gate (higher exponents do). |
| `YM.AnalyticNext.GridStop.Alphabet.paid` | lemma, private | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/AnalyticNext/GRID_STOP_ATTENUATION/Alphabet/Mint.lean#L46) |  |

### Fill

`YM/Corona/Fill.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Corona.Touch` | abbrev | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L20) |  |
| `YM.Lattice.Corona.Ships` | abbrev | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L22) |  |
| `YM.Lattice.Corona.sym` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L24) |  |
| `YM.Lattice.Corona.grow` | lemma | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L29) |  |
| `YM.Lattice.Corona.lap` | lemma | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L32) |  |
| `YM.Lattice.Corona.line` | def | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L42) | explicit lattice line, saturated at target. |
| `YM.Lattice.Corona.line_home` | lemma | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L44) |  |
| `YM.Lattice.Corona.line_end` | lemma | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L49) |  |
| `YM.Lattice.Corona.line_dist` | lemma | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L54) |  |
| `YM.Lattice.Corona.halo_mono` | lemma | [58](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L58) |  |
| `YM.Lattice.Corona.line_path` | lemma | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L61) |  |
| `YM.Lattice.Corona.ship_halo` | lemma | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L69) |  |
| `YM.Lattice.Corona.halo_ship` | lemma | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L95) |  |
| `YM.Lattice.Corona.list_cost` | lemma | [113](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L113) |  |
| `YM.Lattice.Corona.box_size` | lemma | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L117) |  |
| `YM.Lattice.Corona.halo_size` | lemma | [120](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L120) |  |
| `YM.Lattice.Corona.pays` | lemma | [129](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fill.lean#L129) |  |

### Fit

`YM/Corona/Fit.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Corona.enlarge` | lemma, private | [9](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fit.lean#L9) |  |
| `YM.Lattice.Corona.ring_path` | lemma | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fit.lean#L38) |  |
| `YM.Lattice.Corona.path_span` | lemma | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fit.lean#L76) |  |
| `YM.Lattice.Corona.extent` | lemma | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Fit.lean#L84) |  |

### Halo

`YM/Corona/Halo.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Corona.cover_mono` | lemma | [10](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Halo.lean#L10) |  |
| `YM.Lattice.Corona.meets_sum` | lemma | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Halo.lean#L14) |  |
| `YM.Lattice.Corona.combine` | lemma, private | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Halo.lean#L32) |  |
| `YM.Lattice.Corona.tile` | lemma | [66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Halo.lean#L66) |  |
| `YM.Lattice.Corona.tiling` | lemma | [115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Halo.lean#L115) |  |

### Spend

`YM/Corona/Spend.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Corona.near` | lemma | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Spend.lean#L17) |  |
| `YM.Lattice.Corona.below` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Spend.lean#L24) |  |
| `YM.Lattice.Corona.foreshorten` | lemma | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Spend.lean#L32) |  |
| `YM.Lattice.Corona.fuel` | lemma | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Spend.lean#L38) |  |
| `YM.Lattice.Corona.collapse` | lemma | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Corona/Spend.lean#L73) | Explicit Fproj with full halo price. Incident shifts can use some B's from s. |

### Casimir

`YM/Gauge/Casimir.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Gauge.Simple.nonabelian` | theorem | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L22) |  |
| `YM.Gauge.Simple.ideals` | theorem | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L30) |  |
| `YM.Gauge.Simple.nontrivial_color` | theorem | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L52) |  |
| `YM.Gauge.ad_jacobi` | theorem | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L56) |  |
| `YM.Gauge.ad_skew` | theorem | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L64) |  |
| `YM.Gauge.minusKilling` | def | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L72) |  |
| `YM.Gauge.minusKilling_symm` | theorem | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L88) |  |
| `YM.Gauge.minusKilling_invariant` | theorem | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L91) |  |
| `YM.Gauge.invariant_scalar` | theorem | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L99) | Every real symmetric Lie-invariant form has this shape. |
| `YM.Gauge.minusKilling_sq` | theorem | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L128) | `-tr ad_X²` is actually a Frobenius norm square on color endomorphisms. |
| `YM.Gauge.trace_adjoint` | theorem | [140](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L140) |  |
| `YM.Gauge.casimir_pos` | theorem | [160](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L160) |  |
| `YM.Gauge.slopeConstant_pos` | theorem | [174](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Casimir.lean#L174) |  |

Covered by [Invariant symmetric forms on the colour space are multiples of the standard inner product](../roadmap/setting/lattice-gauge-wilson/invariant-forms-are-scalar.md) (`YM.Gauge.invariant_scalar`).

Lean-side notes:

- The proof of `YM.Gauge.invariant_scalar` (line 99) represents $B$ by a symmetric operator through `InnerProductSpace.toDual`, takes its eigenvalue at index $0$, shows that the eigenspace is invariant under the colour bracket by `YM.Gauge.ad_skew` (line 64, $\langle \mathrm{ad}(x)y, z \rangle = -\langle y, \mathrm{ad}(x)z \rangle$), and concludes that the eigenspace is the whole colour space by `YM.Gauge.Simple.ideals` (line 30). `YM.Gauge.Simple.nontrivial_color` (line 52) supplies a nonzero colour.
- Other declarations with no article: `YM.Gauge.Simple.nonabelian` (line 22) restates the nonabelian clause in colour coordinates; `YM.Gauge.ad_jacobi` (line 56) gives $\mathrm{ad}(\mathrm{ad}(x)y) = \mathrm{ad}(x)\mathrm{ad}(y) - \mathrm{ad}(y)\mathrm{ad}(x)$; the form `YM.Gauge.minusKilling` (line 72) meets the hypotheses of `YM.Gauge.invariant_scalar` by `YM.Gauge.minusKilling_symm` (line 88) and `YM.Gauge.minusKilling_invariant` (line 91), and `YM.Gauge.trace_adjoint` (line 140) applies the theorem to it, giving $-\operatorname{tr}(\mathrm{ad}(x)\mathrm{ad}(y)) = C\langle x, y \rangle$ with the Casimir constant `YM.Gauge.casimir` (Colors.lean:180); `YM.Gauge.casimir_pos` (line 160) and `YM.Gauge.slopeConstant_pos` (line 174) follow.

### Chart

`YM/Gauge/Chart.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Gauge.Normal` | abbrev | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L26) |  |
| `YM.Gauge.exp_inv_range` | lemma | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L28) |  |
| `YM.Gauge.direction_in_lie` | lemma | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L40) |  |
| `YM.Gauge.isolates` | lemma | [71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L71) |  |
| `YM.Gauge.addNormal` | def | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L93) |  |
| `YM.Gauge.addNormal_apply` | theorem | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L96) |  |
| `YM.Gauge.contDiff_exp` | theorem | [98](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L98) |  |
| `YM.Gauge.exp_jet` | theorem | [102](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L102) |  |
| `YM.Gauge.splitNormal` | def | [106](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L106) |  |
| `YM.Gauge.mat_lieExp_zero` | theorem | [108](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L108) |  |
| `YM.Gauge.splitNormal_zero` | theorem | [110](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L110) |  |
| `YM.Gauge.splitDiff` | theorem | [112](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L112) |  |
| `YM.Gauge.expDiff_zero` | theorem | [118](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L118) |  |
| `YM.Gauge.splitDeriv` | theorem | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L124) |  |
| `YM.Gauge.coord` | abbrev, private | [135](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L135) |  |
| `YM.Gauge.plog` | def | [138](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L138) |  |
| `YM.Gauge.coord_in` | lemma, private | [140](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L140) |  |
| `YM.Gauge.coord_out` | lemma, private | [143](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L143) |  |
| `YM.Gauge.coord_one` | lemma, private | [147](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L147) |  |
| `YM.Gauge.plog_one` | theorem | [150](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L150) |  |
| `YM.Gauge.plog_diff` | theorem | [152](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L152) |  |
| `YM.Gauge.plog_left` | theorem | [157](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L157) |  |
| `YM.Gauge.plog_right` | theorem | [164](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Chart.lean#L164) |  |

### Colors

`YM/Gauge/Colors.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Gauge.frobInner` | def | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L26) | Real Frobenius inner product in the defining representation (not normalized). |
| `YM.Gauge.lieDim` | abbrev | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L41) |  |
| `YM.Gauge.ColorIndex` | abbrev | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L42) |  |
| `YM.Gauge.Color` | abbrev | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L43) |  |
| `YM.Gauge.colorScale` | def | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L46) | scale factor from physical to Frobenius coordinates. |
| `YM.Gauge.colorScale_pos` | theorem | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L48) |  |
| `YM.Gauge.colorScale_sq` | theorem | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L49) |  |
| `YM.Gauge.colorIso` | def | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L52) | A fixed orthogonal frame with the physical normalization. |
| `YM.Gauge.inner_frob_color` | theorem | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L56) |  |
| `YM.Gauge.colorMat` | def | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L64) |  |
| `YM.Gauge.colorMat_mem` | theorem | [66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L66) |  |
| `YM.Gauge.colorMat_skew` | theorem | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L68) |  |
| `YM.Gauge.trace_color` | theorem | [71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L71) |  |
| `YM.Gauge.trace_color_real` | theorem | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L77) |  |
| `YM.Gauge.colorMat_injective` | theorem | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L88) |  |
| `YM.Gauge.colorMat_norm` | theorem | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L91) |  |
| `YM.Gauge.projectColor` | def | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L96) |  |
| `YM.Gauge.colorMat_project` | theorem | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L99) |  |
| `YM.Gauge.colorMat_project_self` | theorem | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L103) |  |
| `YM.Gauge.project_colorMat` | theorem | [106](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L106) |  |
| `YM.Gauge.project_norm` | theorem | [109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L109) |  |
| `YM.Gauge.adjoint` | def | [114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L114) | Gauge group adjoint through coordinates |
| `YM.Gauge.mat_adjoint` | theorem | [119](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L119) |  |
| `YM.Gauge.adjoint_one` | theorem | [123](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L123) |  |
| `YM.Gauge.adjoint_mul` | theorem | [126](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L126) |  |
| `YM.Gauge.norm_adjoint` | theorem | [130](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L130) |  |
| `YM.Gauge.ad` | def | [136](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L136) |  |
| `YM.Gauge.colorMat_ad` | theorem | [152](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L152) |  |
| `YM.Gauge.lieExp_mem` | theorem | [156](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L156) |  |
| `YM.Gauge.lieExp` | def | [160](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L160) | Actual exponential into the gauge group. |
| `YM.Gauge.mat_lieExp` | theorem | [162](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L162) |  |
| `YM.Gauge.lieExp_cont` | theorem | [165](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L165) |  |
| `YM.Gauge.curvature` | def | [173](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L173) | projection of the real skew part, in physical coordinates. |
| `YM.Gauge.curvature_inv` | theorem | [175](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L175) |  |
| `YM.Gauge.casimir` | def | [180](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L180) | `C_A`, fixed in terms of the trace of the adjoint action on physical colors. |
| `YM.Gauge.slopeConstant` | def | [184](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Colors.lean#L184) |  |

Covered by [Real Frobenius inner product](../roadmap/setting/lattice-gauge-wilson/frobenius-inner-product.md) (`YM.Gauge.frobInner`); [Colour coordinates on the Lie algebra](../roadmap/setting/lattice-gauge-wilson/colour-frame.md) (`YM.Gauge.colorIso`, `YM.Gauge.colorMat`, `YM.Gauge.Color`, `YM.Gauge.ColorIndex`, `YM.Gauge.lieDim`, `YM.Gauge.colorScale`); [Projection of matrices onto colours](../roadmap/setting/lattice-gauge-wilson/colour-projection.md) (`YM.Gauge.projectColor`); and [Bracket in colour coordinates](../roadmap/setting/lattice-gauge-wilson/colour-bracket.md) (`YM.Gauge.ad`).

Lean-side notes:

- `YM.Gauge.frobInner` (line 26) is marked `@[instance_reducible]` and is not a global instance: this file opens it with `attribute [local instance]` (line 37), and so does Size.lean. It is defined for every matrix size, and the gauge-group declarations use it at size $n + 1$. Its norm is Mathlib's scoped Frobenius norm, through `YM.Gauge.frob_sq` (MatrixGroup.lean:34).
- `YM.Gauge.colorIso` (line 52) is the inverse coordinate map of Mathlib's `stdOrthonormalBasis` of $\mathfrak g$, for the restriction of `YM.Gauge.frobInner`, followed by multiplication by `YM.Gauge.colorScale` $= \sqrt{n+1}$ (line 46). `stdOrthonormalBasis` (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:1077`) is chosen with `Classical.choose`, so the frame is one fixed but unspecified orthonormal basis.
- Consequences with no article: `YM.Gauge.colorScale_pos` (line 48) and `YM.Gauge.colorScale_sq` (line 49); $\langle X_c, X_{c'} \rangle_F = (n+1)\langle c, c' \rangle$, `YM.Gauge.inner_frob_color` (line 56); $X_c \in \mathfrak g$, `YM.Gauge.colorMat_mem` (line 66); $X_c^* = -X_c$, `YM.Gauge.colorMat_skew` (line 68); $-\operatorname{Re} \operatorname{tr}(X_c X_{c'}) = (n+1)\langle c, c' \rangle$, `YM.Gauge.trace_color` (line 71); $\operatorname{Im} \operatorname{tr}(X_c X_{c'}) = 0$, `YM.Gauge.trace_color_real` (line 77); injectivity of $c \mapsto X_c$, `YM.Gauge.colorMat_injective` (line 88); $\|X_c\|_F = \sqrt{n+1}\,|c|$, `YM.Gauge.colorMat_norm` (line 91).
- `YM.Gauge.projectColor` (line 96) is the inverse colour frame after the orthogonal projection onto $\mathfrak g$. Its characterizations are theorems: $X_{\Pi A} = P_{\mathfrak g} A$, `YM.Gauge.colorMat_project` (line 99); $X_{\Pi A} = A$ for $A \in \mathfrak g$, `YM.Gauge.colorMat_project_self` (line 103); $\Pi X_c = c$, `YM.Gauge.project_colorMat` (line 106); $|\Pi A| \le \|A\|_F / \sqrt{n+1}$, `YM.Gauge.project_norm` (line 109).
- `YM.Gauge.ad` (line 136) is a real bilinear map, $\mathrm{ad}(c)c' = \Pi(X_c X_{c'} - X_{c'} X_c)$, whose linearity proofs are part of the definition. $X_{\mathrm{ad}(c)c'} = X_c X_{c'} - X_{c'} X_c$ is the theorem `YM.Gauge.colorMat_ad` (line 152), from `YM.Gauge.bracket_mem` (Lie.lean:159).

### Curvature

`YM/Gauge/Curvature.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Gauge.conjugateL` | def | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L16) |  |
| `YM.Gauge.conjugateL_act` | theorem | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L26) |  |
| `YM.Gauge.conjugate_inv` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L28) |  |
| `YM.Gauge.project_conjugate` | theorem | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L35) |  |
| `YM.Gauge.curvature_unit` | theorem | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L49) |  |
| `YM.Gauge.continuous_curvature` | theorem | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L51) |  |
| `YM.Gauge.curvature_conjugate` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L55) |  |
| `YM.Gauge.curvature_norm` | theorem | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L62) |  |
| `YM.Gauge.leading_curvature` | theorem | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Curvature.lean#L78) | First variation with the actual normalization. |

### Lie

`YM/Gauge/Lie.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Gauge.Generates` | def | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L26) | One-parameter generators of this closed subgroup, in the defining representation. |
| `YM.Gauge.tangent_skew` | theorem | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L31) |  |
| `YM.Gauge.generates_skew` | theorem | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L42) |  |
| `YM.Gauge.frob_pow_difference` | theorem | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L47) | Frobenius norm avoids exponential constants in telescoping. |
| `YM.Gauge.tangent_approx` | theorem | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L61) |  |
| `YM.Gauge.tangent_generates` | theorem | [98](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L98) |  |
| `YM.Gauge.generates_add` | theorem | [114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L114) |  |
| `YM.Gauge.lie` | def | [126](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L126) |  |
| `YM.Gauge.Alg` | abbrev | [137](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L137) |  |
| `YM.Gauge.mem_lie` | theorem | [139](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L139) |  |
| `YM.Gauge.closed_lie` | theorem | [141](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L141) |  |
| `YM.Gauge.conjugate` | def | [144](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L144) | Conjugation in the defining representation. |
| `YM.Gauge.exp_conjugate` | theorem | [146](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L146) |  |
| `YM.Gauge.conjugate_mem` | theorem | [151](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L151) |  |
| `YM.Gauge.bracket_mem` | theorem | [159](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L159) |  |
| `YM.Gauge.Simple` | def | [179](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Lie.lean#L179) | Real simplicity with the nonabelian clause. |

Covered by [Lie algebra of a gauge group](../roadmap/setting/lattice-gauge-wilson/gauge-lie-algebra.md) (`YM.Gauge.lie`, `YM.Gauge.Generates`, `YM.Gauge.Alg`); and [Real simplicity of a gauge group](../roadmap/setting/lattice-gauge-wilson/real-simplicity.md) (`YM.Gauge.Simple`).

Lean-side notes:

- `YM.Gauge.Generates X` (line 26) says that $\exp(tX)$ lies in the range of `YM.Gauge.mat` for every real $t$. `YM.Gauge.lie` (line 126) packages it as a real submodule of the matrices: closure under addition is `YM.Gauge.generates_add` (line 114), proved with the tangent criterion `YM.Gauge.tangent_generates` (line 98) and the closedness of the range of `YM.Gauge.mat`; $0$ is a generator because $\exp 0 = 1$; closure under real multiples reparametrizes $t$. `YM.Gauge.Alg` (line 137) is the subtype of `YM.Gauge.lie`, and `YM.Gauge.mem_lie` (line 139) is `Iff.rfl`.
- Moved out of the gauge-lie-algebra article: every generator is skew-Hermitian, `YM.Gauge.generates_skew` (line 42); $\mathfrak g$ is closed, `YM.Gauge.closed_lie` (line 141); it is closed under $XY - YX$, `YM.Gauge.bracket_mem` (line 159); it is invariant under conjugation by $G$, `YM.Gauge.conjugate_mem` (line 151), with `YM.Gauge.conjugate` (line 144) and `YM.Gauge.exp_conjugate` (line 146); the tangent criterion, `YM.Gauge.tangent_generates` (line 98), with `YM.Gauge.tangent_approx` (line 61) and `YM.Gauge.tangent_skew` (line 31). The module docstring says that the definition "Applies also to disconnected G".
- `YM.Gauge.Simple` (line 179) quantifies over real submodules $I$ of the matrices with $I \le \mathfrak g$ and $XY - YX \in I$ for $X \in \mathfrak g$, $Y \in I$, not over subspaces of the subtype `YM.Gauge.Alg`; the article states it that way. Its two clauses are restated in colour coordinates by `YM.Gauge.Simple.nonabelian` (Casimir.lean:22) and `YM.Gauge.Simple.ideals` (Casimir.lean:30).
- Relation to the public notions, which the articles do not state (rule 5): `YangMills.GaugeGroup.core` (WilsonBridge.lean:10) sends a public gauge group to the internal record $(n, G)$ with its closedness, and `YangMills.GaugeGroup.coreSimple` (WilsonBridge.lean:12) proves that public simplicity implies internal simplicity, by identifying the internal Lie algebra with the public one through the exponential condition (Armstrong's unit VIII.1).

### MatrixGroup

`YM/Gauge/MatrixGroup.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.GaugeU` | abbrev | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L20) | We index a representation of dimension `n+1`. |
| `YM.Gauge` | structure | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L23) | A closed compact matrix group in its fixed faithful unitary representation. |
| `YM.Gauge.n` | field | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L24) |  |
| `YM.Gauge.imageGroup` | field | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L25) |  |
| `YM.Gauge.closed_imageGroup` | field | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L26) |  |
| `YM.Gauge.frob_sq` | theorem | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L34) | Trace characterization of the Frobenius norm. |
| `YM.Gauge.mul_frob_eq` | theorem | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L45) |  |
| `YM.Gauge.frob_mul_eq` | theorem | [50](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L50) |  |
| `YM.Gauge.unitary_frob` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L55) |  |
| `YM.Gauge.compactGaugeU` | theorem | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L61) |  |
| `YM.Gauge.repDim` | abbrev | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L73) | Dimension of the defining representation (not number of Lie colors). |
| `YM.Gauge.dimPos` | theorem | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L75) |  |
| `YM.Gauge.El` | abbrev | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L78) | Physical link state space. |
| `YM.Gauge.Mat` | abbrev | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L92) |  |
| `YM.Gauge.mat` | def | [94](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L94) |  |
| `YM.Gauge.continuous_mat` | theorem | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L96) |  |
| `YM.Gauge.mat_injective` | theorem | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L99) |  |
| `YM.Gauge.closed_matrices` | theorem | [102](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L102) |  |
| `YM.Gauge.mat_one` | theorem | [105](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L105) |  |
| `YM.Gauge.mat_mul` | theorem | [106](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L106) |  |
| `YM.Gauge.mat_inv` | theorem | [107](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L107) |  |
| `YM.Gauge.mat_mul_star` | theorem | [108](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L108) |  |
| `YM.Gauge.mat_star_mul` | theorem | [109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L109) |  |
| `YM.Gauge.price` | def | [112](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L112) | `s(U)`. |
| `YM.Gauge.chord` | def | [115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L115) | The normalized HS chord, not the operator norm. |
| `YM.Gauge.chord_price` | theorem | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L117) |  |
| `YM.Gauge.chord_one` | theorem | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L128) |  |
| `YM.Gauge.price_one` | theorem | [129](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L129) |  |
| `YM.Gauge.chord_nonneg` | theorem | [132](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L132) |  |
| `YM.Gauge.chord_le_two` | theorem | [134](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L134) |  |
| `YM.Gauge.price_range` | theorem | [141](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L141) |  |
| `YM.Gauge.chord_triangle` | theorem | [146](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L146) |  |
| `YM.Gauge.price_inv` | theorem | [157](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L157) |  |
| `YM.Gauge.price_conj` | theorem | [160](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L160) |  |
| `YM.Gauge.chord_inv` | theorem | [166](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L166) |  |
| `YM.Gauge.chord_conj` | theorem | [169](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L169) |  |
| `YM.Gauge.continuous_chord` | theorem | [172](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L172) |  |
| `YM.Gauge.continuous_price` | theorem | [173](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L173) |  |
| `YM.Gauge.elMeasurableSpace` | instance | [180](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L180) | The normalized HS chord, not the operator norm. -/ def chord (u : G.El) : ℝ := ‖G.mat u - 1‖ / Real.sqrt G.repDim theorem chord_price (u : G.El) : G.chord u ^ 2 = 2 * G.price u := by unfold chord price rw [div_pow, frob_sq, Real.sq_sqrt (Nat.cast_nonneg _)] simp only [star_sub, star_one, mul_sub, sub_mul, one_mul, mul_one, mat_mul_star] simp only [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, Complex.star_def, Complex.sub_re, Complex.conj_re, Complex.natCast_re] field_simp ring @[simp] theorem chord_one : G.chord 1 = 0 := by simp [chord] @[simp] theorem price_one : G.price 1 = 0 := by have := G.chord_price 1; simpa using this.symm theorem chord_nonneg (u : G.El) : 0 ≤ G.chord u := by unfold chord; positivity theorem chord_le_two (u : G.El) : G.chord u ≤ 2 := by unfold chord rw [div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast G.dimPos))] apply (norm_sub_le _ _).trans rw [unitary_frob (G.mat_mul_star u), unitary_frob (show (1 : Matrix (Fin G.repDim) (Fin G.repDim) ℂ) * star 1 = 1 from G.mat_mul_star 1)] rw [two_mul] theorem price_range (u : G.El) : G.price u ∈ Set.Icc (0 : ℝ) 2 := by have h := G.chord_price u have h1 := G.chord_le_two u constructor <;> nlinarith [G.chord_nonneg u] theorem chord_triangle (u v : G.El) : G.chord (u*v) ≤ G.chord u + G.chord v := by have h :‖G.mat u * G.mat v - 1‖ ≤ ‖G.mat u - 1‖ + ‖G.mat v - 1‖ := calc ‖G.mat u * G.mat v - 1‖ = ‖(G.mat u - 1) + G.mat u * (G.mat v - 1)‖ := by simp only [mul_sub, mul_one]; congr 1; abel _ ≤ _ := by simpa only [mul_frob_eq _ _ (mat_star_mul G u)] using norm_add_le (G.mat u - 1) (G.mat u * (G.mat v - 1)) unfold chord rw [G.mat_mul, ← add_div] exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg _) @[simp] theorem price_inv (u : G.El) : G.price u⁻¹ = G.price u := by simp [price, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose] @[simp] theorem price_conj (u v : G.El) : G.price (u*v*u⁻¹) = G.price v := by have h : (G.mat (u*v*u⁻¹)).trace = (G.mat v).trace := by simp only [G.mat_mul, G.mat_inv, Matrix.trace_mul_cycle, G.mat_star_mul, one_mul] unfold price rw [h] @[simp] theorem chord_inv (u : G.El) : G.chord u⁻¹ = G.chord u := by rw [← sq_eq_sq₀ (chord_nonneg _ _) (chord_nonneg _ _), chord_price, price_inv, chord_price] @[simp] theorem chord_conj (u v : G.El) : G.chord (u*v*u⁻¹) = G.chord v := by rw [← sq_eq_sq₀ (chord_nonneg _ _) (chord_nonneg _ _), chord_price, price_conj, chord_price] @[fun_prop] theorem continuous_chord : Continuous G.chord := by unfold chord; fun_prop @[fun_prop] theorem continuous_price : Continuous G.price := by have h : G.price = fun x ↦ G.chord x ^ 2 / 2 := by funext; rw [G.chord_price]; ring rw [h]; fun_prop /-! Choose Borel on this subtype. Do not also introduce a measurable-space instance on `GaugeU`. |
| `YM.Gauge.elBorelSpace` | instance | [181](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L181) |  |
| `YM.Gauge.allElements` | def | [183](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L183) |  |
| `YM.Gauge.probHaar` | def | [187](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L187) | Probability Haar used throughout including blocked expectations. |
| `YM.Gauge.probHaar_isHaar` | instance | [189](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L189) |  |
| `YM.Gauge.probHaar_isProbability` | instance | [190](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L190) |  |
| `YM.Gauge.probHaar_rightInv` | instance | [193](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L193) |  |
| `YM.Gauge.probHaar_invInv` | instance | [202](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L202) |  |
| `YM.Gauge.preserve_inv` | theorem | [209](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L209) |  |
| `YM.Gauge.preserve_two_sided` | theorem | [212](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/MatrixGroup.lean#L212) |  |

Covered by [Gauge group in a unitary representation](../roadmap/setting/lattice-gauge-wilson/gauge-group-in-representation.md) (`YM.Gauge`, `YM.GaugeU`); [Elements and matrices of a gauge group](../roadmap/setting/lattice-gauge-wilson/group-elements-and-matrices.md) (`YM.Gauge.El`, `YM.Gauge.mat`, `YM.Gauge.Mat`, `YM.Gauge.repDim`); [Normalized chord and chord balls](../roadmap/setting/lattice-gauge-wilson/chord-and-chord-balls.md) (`YM.Gauge.chord`); and [Haar probability measure of a gauge group](../roadmap/setting/lattice-gauge-wilson/haar-probability.md) (`YM.Gauge.probHaar`, `YM.Gauge.allElements`, `YM.Gauge.elMeasurableSpace`).

Lean-side notes:

- `YM.Gauge` (line 23) has exactly three fields: `n`, `imageGroup : Subgroup (GaugeU n)` and `closed_imageGroup`. Its docstring says "closed compact", but compactness is not a field: it is the unnamed instance `CompactSpace G.El` (line 80), proved from closedness and `YM.Gauge.compactGaugeU` (line 61, which places $U(n+1)$ in the Frobenius closed ball of radius $\sqrt{n+1}$). Second countability is the unnamed instance at line 84. The articles state neither.
- `YM.GaugeU n` (line 20) is Mathlib's `Matrix.unitaryGroup (Fin (n+1)) ℂ`, with the subspace topology of the entrywise topology on matrices.
- `YM.Gauge.repDim` (line 73) is $n + 1$; its docstring reads "Dimension of the defining representation (not number of Lie colors)". The number of colours is `YM.Gauge.lieDim` (Colors.lean:41). `YM.Gauge.dimPos` (line 75) proves $0 < n + 1$. `YM.Gauge.Mat` (line 92) is an abbrev for the complex $(n+1) \times (n+1)$ matrices, so Mathlib's ring, star, module and topology instances on matrices apply; the Frobenius norm is opened as a scoped instance in the file.
- The docstring of `YM.Gauge.El` (line 78) is "Physical link state space."; the article does not repeat it. `YM.Gauge.mat` (line 94) is the double coercion of an element to its matrix. Separate theorems support identifying an element with its matrix: `YM.Gauge.continuous_mat` (line 96), `YM.Gauge.mat_injective` (line 99), `YM.Gauge.closed_matrices` (line 102), `YM.Gauge.mat_one`, `YM.Gauge.mat_mul` and `YM.Gauge.mat_inv` (lines 105 to 107, all `rfl`, the inverse being the conjugate transpose), and `YM.Gauge.mat_mul_star` and `YM.Gauge.mat_star_mul` (lines 108 and 109).
- `YM.Gauge.chord` (line 115) is $\|u - 1\|_F / \sqrt{n+1}$ with Mathlib's scoped Frobenius norm, not `YM.Gauge.frobInner`. Moved out of the chord article: $\chi^2 = 2\sigma$ for the plaquette cost `YM.Gauge.price` (line 112), `YM.Gauge.chord_price` (line 117); $\chi(1) = 0$, `YM.Gauge.chord_one` (line 128); $\chi \ge 0$, `YM.Gauge.chord_nonneg` (line 132), so a chord ball of negative radius is empty; $\chi \le 2$, `YM.Gauge.chord_le_two` (line 134); the triangle inequality, `YM.Gauge.chord_triangle` (line 146); invariance under inversion and conjugation, `YM.Gauge.chord_inv` (line 166) and `YM.Gauge.chord_conj` (line 169); continuity, `YM.Gauge.continuous_chord` (line 172).
- `YM.Gauge.elMeasurableSpace` (line 180) is the Borel σ-algebra on $G$; `YM.Gauge.elBorelSpace` (line 181, no article) records that it is Borel. `YM.Gauge.allElements` (line 183) is all of $G$ as a compact set with nonempty interior, using the compactness instance of line 80. `YM.Gauge.probHaar` (line 187) is Mathlib's `Measure.haarMeasure` of that set, defined as the measure of the Haar content divided by its value on the set (`Mathlib/MeasureTheory/Measure/Haar/Basic.lean:517`).
- Moved out of the Haar article: $h_G$ is a Haar measure, `YM.Gauge.probHaar_isHaar` (line 189); $h_G(G) = 1$, `YM.Gauge.probHaar_isProbability` (line 190, through Mathlib's `Measure.haarMeasure_self`); right invariance, `YM.Gauge.probHaar_rightInv` (line 193); invariance under inversion, `YM.Gauge.probHaar_invInv` (line 202); $u \mapsto u^{-1}$ and $u \mapsto vuw$ preserve $h_G$, `YM.Gauge.preserve_inv` (line 209) and `YM.Gauge.preserve_two_sided` (line 212).
- Defect of this table: the docstring cell of the `YM.Gauge.elMeasurableSpace` row holds Lean source, from the docstring of `YM.Gauge.chord` (line 114) to the module comment before line 180; the source index took that comment for the declaration's docstring. The declaration has no docstring; the comment before it reads "Choose Borel on this subtype. Do not also introduce a measurable-space instance on `GaugeU`."

### Nearest

`YM/Gauge/Nearest.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Gauge.Nearest` | def | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L26) |  |
| `YM.Gauge.nearest_exists` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L28) |  |
| `YM.Gauge.nearest_left` | lemma | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L33) |  |
| `YM.Gauge.nearest_right` | lemma | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L38) |  |
| `YM.Gauge.nearest_normal_one` | lemma | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L43) |  |
| `YM.Gauge.nearest_normal` | lemma | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L65) |  |
| `YM.Gauge.tubular` | def | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L70) |  |
| `YM.Gauge.tubular_zero` | theorem | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L72) |  |
| `YM.Gauge.tubularDiff` | theorem | [74](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L74) |  |
| `YM.Gauge.tubularDeriv` | theorem | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L78) |  |
| `YM.Gauge.tube` | abbrev, private | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L88) |  |
| `YM.Gauge.focus` | def | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L91) |  |
| `YM.Gauge.tube_in` | lemma, private | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L93) |  |
| `YM.Gauge.focus_diff` | theorem | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L95) |  |
| `YM.Gauge.focuses` | lemma, private | [100](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L100) |  |
| `YM.Gauge.nearest_is_focus` | theorem | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L128) |  |
| `YM.Gauge.nearest_tube` | theorem | [141](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L141) |  |
| `YM.Gauge.focus_deriv` | theorem | [155](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L155) |  |
| `YM.Gauge.nearest_approximate` | theorem | [172](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Nearest.lean#L172) |  |

### Size

`YM/Gauge/Size.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Gauge.shell` | def | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Size.lean#L28) |  |
| `YM.Gauge.shell_meas` | lemma | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Size.lean#L29) |  |
| `YM.Gauge.package` | theorem, private | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Size.lean#L31) |  |
| `YM.Gauge.shell_ge` | theorem | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Gauge/Size.lean#L80) | purely real. enough to use log arm. |

Covered by [Normalized chord and chord balls](../roadmap/setting/lattice-gauge-wilson/chord-and-chord-balls.md) (`YM.Gauge.shell`); and [Haar mass of small chord balls](../roadmap/setting/lattice-gauge-wilson/haar-mass-small-balls.md) (`YM.Gauge.shell_ge`).

Lean-side notes:

- `YM.Gauge.shell r` (line 28) is $\{v : \chi(v) \le r\}$ for every real $r$: a closed chord ball around $1$, despite its name. Its measurability is `YM.Gauge.shell_meas` (line 29).
- `YM.Gauge.shell_ge` (line 80) bounds `G.probHaar.real (G.shell r)`, the measure as a real number (finite, since $h_G$ is a probability measure), from below by $(r/4)$ to the power `Module.finrank ℝ G.Mat`. The local instance `YM.Gauge.frobInner` keeps the entrywise real vector-space structure of the matrices, so the exponent is $2(n+1)^2$. The proof is a packing argument through the private `YM.Gauge.package` (line 31) and uses `YM.Gauge.colorScale` (Colors.lean:46).

### Box

`YM/Lattice/Box.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.box` | def | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L13) |  |
| `YM.Lattice.box_test` | theorem | [15](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L15) |  |
| `YM.Lattice.center_box` | theorem | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L18) |  |
| `YM.Lattice.box_covariant` | theorem | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L20) |  |
| `YM.Lattice.straight` | def | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L34) | Leg with integer signed length in axis `a`. |
| `YM.Lattice.axisRoute` | def | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L36) |  |
| `YM.Lattice.Order` | abbrev | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L39) |  |
| `YM.Lattice.allAxes` | def | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L41) |  |
| `YM.Lattice.route` | def | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L44) |  |
| `YM.Lattice.straight_stop` | theorem | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L46) |  |
| `YM.Lattice.axisRoute_end` | theorem | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L63) |  |
| `YM.Lattice.route_end` | theorem | [74](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L74) |  |
| `YM.Lattice.route_same` | theorem | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Box.lean#L82) |  |

### Crossing

`YM/Lattice/Crossing.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Ratio.half_box` | lemma | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Crossing.lean#L19) |  |
| `YM.Lattice.Ratio.half_lift` | lemma | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Crossing.lean#L27) |  |
| `YM.Lattice.Ratio.embed_parent` | lemma | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Crossing.lean#L33) |  |
| `YM.Lattice.Ratio.embed_leap` | lemma | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Crossing.lean#L38) |  |
| `YM.Lattice.Ratio.root_id` | lemma | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Crossing.lean#L44) |  |
| `YM.Lattice.Ratio.parents_hop` | theorem | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Crossing.lean#L54) | Determine parent of the neighbor to apply T_cp. |
| `YM.Lattice.Ratio.internal` | lemma | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Crossing.lean#L86) |  |

### Faces

`YM/Lattice/Faces.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.PlaqAxes` | abbrev | [13](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L13) |  |
| `YM.Lattice.Face` | abbrev | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L14) |  |
| `YM.Lattice.PlaqAxes.ordered` | def | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L18) |  |
| `YM.Lattice.PlaqAxes.rotate` | def | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L24) |  |
| `YM.Lattice.PlaqAxes.rotate_inv` | theorem | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L27) |  |
| `YM.Lattice.PlaqAxes.transform` | def | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L38) |  |
| `YM.Lattice.faceValue` | def | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L47) |  |
| `YM.Lattice.face_gauge` | theorem | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L49) |  |
| `YM.Lattice.Step.rev_rev` | theorem | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L54) |  |
| `YM.Lattice.oriented` | def | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L57) |  |
| `YM.Lattice.stop_oriented` | theorem | [59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L59) |  |
| `YM.Lattice.oriented_swap` | theorem | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L62) |  |
| `YM.Lattice.oriented_next` | theorem | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L69) | Starting a square at the next corner cyclically conjugates its transport. |
| `YM.Lattice.price_flip` | theorem | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L81) |  |
| `YM.Lattice.atFace` | def | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L88) | Unsigned positive base, before swapping axes to use increasing order. |
| `YM.Lattice.price_shift_pos` | theorem | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L92) |  |
| `YM.Lattice.Face.lower` | def | [112](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L112) |  |
| `YM.Lattice.Face.send` | def | [115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L115) |  |
| `YM.Lattice.Face.injective_send` | theorem | [119](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L119) | Shifts in bases do not affect face counts. |
| `YM.Lattice.Face.send_price` | theorem | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Faces.lean#L128) |  |

### Foliation

`YM/Lattice/Foliation.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.layers` | def | [15](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L15) |  |
| `YM.Lattice.slab` | def | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L18) | pinned patch from box by fixing all unvisited axes to some coordinates. |
| `YM.Lattice.box_iff_layers` | lemma | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L21) |  |
| `YM.Lattice.card_layers` | lemma | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L23) |  |
| `YM.Lattice.slab_iff` | lemma | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L25) |  |
| `YM.Lattice.update_box` | lemma | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L27) |  |
| `YM.Lattice.lower_pin` | lemma | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L30) |  |
| `YM.Lattice.step_between` | lemma | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L42) |  |
| `YM.Lattice.slab_update_image` | lemma | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L52) |  |
| `YM.Lattice.slab_sum` | theorem | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L62) |  |
| `YM.Lattice.axis_orthogonal` | lemma | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L73) |  |
| `YM.Lattice.square_corners` | theorem | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L80) |  |
| `YM.Lattice.axis_route_support` | lemma | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L86) |  |
| `YM.Lattice.carry_succ` | theorem | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Foliation.lean#L91) |  |

### Path

`YM/Lattice/Path.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Links` | abbrev | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L21) | Link arrays with positive orientations only. |
| `YM.Lattice.Step` | structure | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L23) |  |
| `YM.Lattice.Step.dir` | field | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L24) |  |
| `YM.Lattice.Step.neg` | field | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L25) |  |
| `YM.Lattice.Walk` | abbrev | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L27) |  |
| `YM.Lattice.posDir` | def | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L29) |  |
| `YM.Lattice.negDir` | def | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L30) |  |
| `YM.Lattice.Step.vec` | def | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L31) |  |
| `YM.Lattice.Step.rev` | def | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L34) |  |
| `YM.Lattice.Step.rotate` | def | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L35) |  |
| `YM.Lattice.Step.rev_pos` | theorem | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L38) |  |
| `YM.Lattice.Step.rev_neg` | theorem | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L39) |  |
| `YM.Lattice.Step.rotate_one` | theorem | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L41) |  |
| `YM.Lattice.Step.rev_rotate` | theorem | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L44) |  |
| `YM.Lattice.Step.rotate_mul` | theorem | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L47) |  |
| `YM.Lattice.Step.vec_rotate` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L55) | Step's displacement transforms by the same signed permutation. |
| `YM.Lattice.Step.used` | def | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L65) |  |
| `YM.Lattice.Step.vec_rev` | theorem | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L69) | Step backwards returns to the same site. |
| `YM.Lattice.stop` | def | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L72) |  |
| `YM.Lattice.visits` | def | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L76) |  |
| `YM.Lattice.stop_append` | theorem | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L80) |  |
| `YM.Lattice.Step.vec_pos` | theorem | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L83) |  |
| `YM.Lattice.Step.vec_neg` | theorem | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L84) |  |
| `YM.Lattice.square` | def | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L86) |  |
| `YM.Lattice.square_stop` | theorem | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L88) |  |
| `YM.Lattice.Step.read` | def | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L93) |  |
| `YM.Lattice.Step.pos_read` | theorem | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L96) |  |
| `YM.Lattice.Step.neg_read` | theorem | [98](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L98) |  |
| `YM.Lattice.Step.read_rev` | theorem | [101](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L101) |  |
| `YM.Lattice.travel` | def | [105](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L105) |  |
| `YM.Lattice.travel_append` | theorem | [109](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L109) |  |
| `YM.Lattice.reverse` | def | [113](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L113) |  |
| `YM.Lattice.reverse_stop` | theorem | [115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L115) |  |
| `YM.Lattice.travel_reverse` | theorem | [122](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L122) |  |
| `YM.Lattice.gauge` | def | [132](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L132) | Pull under a vertex gauge rotation, including the inverse at the *final* site. |
| `YM.Lattice.GaugeInvariant` | def | [135](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L135) |  |
| `YM.Lattice.Step.gauge_read` | theorem | [137](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L137) |  |
| `YM.Lattice.travel_gauge` | theorem | [141](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L141) |  |
| `YM.Lattice.affine` | def | [145](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L145) |  |
| `YM.Lattice.pull` | def | [147](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L147) |  |
| `YM.Lattice.Step.pull_read` | theorem | [150](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L150) |  |
| `YM.Lattice.travel_pull` | theorem | [160](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L160) |  |
| `YM.Lattice.pull_id` | theorem | [169](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L169) |  |
| `YM.Lattice.pull_pull` | theorem | [173](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L173) |  |
| `YM.Lattice.translate` | def | [182](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L182) | Translations with `translate b U` at `x` equal to `U` at `x+b`. |
| `YM.Lattice.pull_one` | theorem | [184](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L184) |  |
| `YM.Lattice.Agrees` | def | [192](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L192) |  |
| `YM.Lattice.LocalOn` | def | [196](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L196) | When the underlying lattice changes, use ALL read endpoints. |
| `YM.Lattice.travel_local` | theorem | [200](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L200) |  |
| `YM.Lattice.expandAt` | def | [224](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L224) |  |
| `YM.Lattice.expandAt_pull` | theorem | [227](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L227) |  |
| `YM.Lattice.wrap_vec` | theorem | [237](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L237) |  |
| `YM.Lattice.travel_at` | theorem | [240](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L240) |  |
| `YM.Lattice.expandAt_gauge` | theorem | [249](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L249) |  |
| `YM.Lattice.LocalOn.expandAt` | theorem | [254](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Path.lean#L254) |  |

Covered by [Links and link arrays](../roadmap/setting/lattice-gauge-wilson/links-and-link-arrays.md) (`YM.Lattice.Links`).

Lean-side notes:

- `YM.Lattice.Links R K` (line 21) is `Edge (Four R) → K` for arbitrary types `R` and `K`; its docstring reads "Link arrays with positive orientations only." Its torus instance is `YM.Wilson.Config` (Wilson/Law.lean:24, with `R` the integers modulo the side); its cover instance `YM.Wilson.CoverConfig` (Law.lean:25, with `R = ℤ`) has no article.
- The chapter page describes in words, without articles: transport `YM.Lattice.travel` (line 105), the ordered product of `YM.Lattice.Step.read` (line 93) along a walk, where a forward step from $y$ along axis $i$ reads $U(y, i)$ and a backward step reads $U(y - e_i, i)^{-1}$, through `YM.Lattice.Step.used` (line 65); gauge transformations `YM.Lattice.gauge` (line 132), $U^g(x, i) = g(x)\,U(x, i)\,g(x + e_i)^{-1}$; the pullback `YM.Lattice.pull` (line 147) along $x \mapsto \rho x + b$, `YM.Lattice.affine` (line 145), whose value on the link $(x, i)$ reads the rotated positive step at the image of $x$; and the unit square walk $+e_i, +e_j, -e_i, -e_j$, `YM.Lattice.square` (line 86).

### Route

`YM/Lattice/Route.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.reverse_append` | theorem | [10](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L10) |  |
| `YM.Lattice.reverse_straight` | theorem | [12](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L12) |  |
| `YM.Lattice.axisRoute_append` | theorem | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L17) |  |
| `YM.Lattice.axisRoute_reverse` | theorem | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L19) |  |
| `YM.Lattice.rev_range` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L24) |  |
| `YM.Lattice.backward` | def | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L26) |  |
| `YM.Lattice.backward_back` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L28) |  |
| `YM.Lattice.backOrder` | def | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L30) |  |
| `YM.Lattice.back_axes` | theorem | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L32) |  |
| `YM.Lattice.back_route` | theorem | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L36) |  |
| `YM.Lattice.indexRoute` | lemma | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L39) |  |
| `YM.Lattice.sendOrder` | def | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L45) |  |
| `YM.Lattice.sendOrder_inv` | lemma | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L47) |  |
| `YM.Lattice.orderEquiv` | def | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L49) |  |
| `YM.Lattice.send_route` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Route.lean#L55) |  |

### Scale

`YM/Lattice/Scale.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Schedule` | structure | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L28) |  |
| `YM.Schedule.block` | field | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L29) |  |
| `YM.Schedule.block_odd` | field | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L30) |  |
| `YM.Schedule.block_large` | field | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L31) |  |
| `YM.Schedule.period` | field | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L32) |  |
| `YM.Schedule.period_four` | field | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L33) |  |
| `YM.Schedule.period_strict` | field | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L34) |  |
| `YM.Schedule.denominator` | def | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L39) |  |
| `YM.Schedule.steps` | def | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L43) |  |
| `YM.Schedule.den_zero` | theorem | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L48) |  |
| `YM.Schedule.den_add` | theorem | [50](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L50) |  |
| `YM.Schedule.den_odd` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L55) |  |
| `YM.Schedule.den_strict` | theorem | [60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L60) |  |
| `YM.Schedule.side` | def | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L67) |  |
| `YM.Schedule.radius` | def | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L69) |  |
| `YM.Schedule.radius_pos` | theorem | [71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L71) |  |
| `YM.Schedule.radius_diverges` | theorem | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L73) |  |
| `YM.Schedule.side_four` | theorem | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L76) |  |
| `YM.Schedule.oneStep` | def | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L78) |  |
| `YM.Schedule.oneStep_odd` | theorem | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L81) |  |
| `YM.Schedule.toDepth` | def | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L83) |  |
| `YM.Schedule.toDepth_odd` | theorem | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L92) |  |
| `YM.Schedule.a` | def | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L99) |  |
| `YM.Schedule.a_zero` | theorem | [101](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L101) |  |
| `YM.Schedule.a_step` | theorem | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L103) |  |
| `YM.Schedule.a_pos` | theorem | [106](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L106) |  |
| `YM.Schedule.shrinks` | theorem | [108](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L108) |  |
| `YM.Schedule.strictAnti` | theorem | [111](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L111) |  |
| `YM.Schedule.scale` | def | [115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L115) |  |
| `YM.Schedule.divergent` | theorem | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L117) |  |
| `YM.Schedule.scale_zero` | theorem | [122](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L122) |  |
| `YM.Schedule.scale_succ` | theorem | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L124) |  |
| `YM.Schedule.Gentle` | def | [129](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L129) |  |
| `YM.Schedule.mesh_inequality` | theorem | [133](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L133) | No need to additionally assume mesh inequality, it follows from Gentle. |
| `YM.Schedule.gridPoint` | def | [164](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L164) |  |
| `YM.Schedule.place` | def | [167](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L167) | Centered, *right*-closed fundamental cell representatives. |
| `YM.Schedule.span_side` | theorem | [169](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L169) |  |
| `YM.Schedule.places_period` | theorem | [173](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L173) |  |
| `YM.Schedule.embeds_scale` | theorem | [184](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L184) |  |
| `YM.Schedule.embeds_place` | theorem | [191](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Scale.lean#L191) |  |

### Site

`YM/Lattice/Site.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Side` | abbrev | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L17) |  |
| `YM.Lattice.Per` | abbrev | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L18) |  |
| `YM.Lattice.Site` | abbrev | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L19) |  |
| `YM.Lattice.Cover` | abbrev | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L20) |  |
| `YM.Lattice.Edge` | abbrev | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L21) |  |
| `YM.Lattice.step` | def | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L26) | Native unit edge increment. |
| `YM.Lattice.step_apply` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L28) |  |
| `YM.Lattice.site_card` | theorem | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L32) |  |
| `YM.Lattice.wrap` | def | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L35) |  |
| `YM.Lattice.wrap_step` | theorem | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L40) |  |
| `YM.Lattice.wrap_signed` | theorem | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L45) |  |
| `YM.Lattice.lift` | def | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L51) |  |
| `YM.Lattice.wrap_lift` | theorem | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L53) |  |
| `YM.Lattice.lift_centers` | theorem | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L56) |  |
| `YM.Lattice.lift_eq_iff` | theorem | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L61) |  |
| `YM.Lattice.wrap_injOn` | theorem | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L70) |  |
| `YM.Lattice.pdist` | def | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L78) | Native torus modulus. |
| `YM.Lattice.separation` | def | [81](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L81) | Canonical lifted max-distance; the separation on the torus. |
| `YM.Lattice.separation_self` | theorem | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L83) |  |
| `YM.Lattice.component_le` | theorem | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L86) |  |
| `YM.Lattice.pdist_neg` | theorem | [89](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L89) |  |
| `YM.Lattice.separation_comm` | theorem | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L93) |  |
| `YM.Lattice.pdist_triangle` | theorem | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L96) |  |
| `YM.Lattice.separation_triangle` | theorem | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L103) |  |
| `YM.Lattice.pdist_invariant` | theorem | [107](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L107) |  |
| `YM.Lattice.separation_translate` | theorem | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L117) |  |
| `YM.Lattice.separation_signed` | theorem | [119](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Site.lean#L119) |  |

Covered by [Sites of the periodic lattice](../roadmap/setting/lattice-gauge-wilson/torus-sites.md) (`YM.Lattice.Site`, `YM.Lattice.Side`, `YM.Lattice.Per`); [Centred lift of a site](../roadmap/setting/lattice-gauge-wilson/centred-lift.md) (`YM.Lattice.lift`, `YM.Lattice.Cover`); [Separation of two sites](../roadmap/setting/lattice-gauge-wilson/torus-separation.md) (`YM.Lattice.separation`, `YM.Lattice.pdist`); and [Links and link arrays](../roadmap/setting/lattice-gauge-wilson/links-and-link-arrays.md) (`YM.Lattice.Edge`).

Lean-side notes:

- The Lean calls the side `n`; the book writes $M$, because $n$ is the gauge group's matrix index. `YM.Lattice.Side` (line 17) is `ℕ+`, `YM.Lattice.Per n` (line 18) is `ZMod n.val`, `YM.Lattice.Site n` (line 19) is `Four (Per n)` and `YM.Lattice.Cover` (line 20) is `Four ℤ`.
- `YM.Lattice.Edge X` (line 21) is `X × Axis` for every type `X`. It is declared in this file, not in Path.lean, so the links article cites both ledger sections.
- `YM.Lattice.lift` (line 51) applies Mathlib's `ZMod.valMinAbs` (`Mathlib/Data/ZMod/ValMinAbs.lean:23`) to each coordinate: a residue $v$ is kept if $v \le \lfloor M/2 \rfloor$ and replaced by $v - M$ otherwise. Moved out of the centred-lift article: each coordinate satisfies $-M < 2\tilde x_i \le M$, `YM.Lattice.lift_centers` (line 56); the lift is the unique $y \in \mathbb Z^4$ that reduces to $x$ with $-M < 2y_i \le M$ for all $i$, `YM.Lattice.lift_eq_iff` (line 61); reducing the lift gives $x$ back, `YM.Lattice.wrap_lift` (line 53); reduction is injective on the centred box, `YM.Lattice.wrap_injOn` (line 70). Reduction $\mathbb Z^4 \to \Lambda_M$ is the additive homomorphism `YM.Lattice.wrap` (line 35).
- Moved out of the torus-sites article: $|\Lambda_M| = M^4$, `YM.Lattice.site_card` (line 32).
- `YM.Lattice.pdist` (line 78) is the supremum over the axes of the natural absolute values of the lift's coordinates, a natural number, and `YM.Lattice.separation x y` (line 81) is `pdist (x - y)`. Moved out of the torus-separation article: $|x - x|_M = 0$, `YM.Lattice.separation_self` (line 83); symmetry, `YM.Lattice.separation_comm` (line 93); the triangle inequality, `YM.Lattice.separation_triangle` (line 103), from `YM.Lattice.pdist_triangle` (line 96); translation invariance, `YM.Lattice.separation_translate` (line 117); invariance under signed permutations of the axes, `YM.Lattice.separation_signed` (line 119), from `YM.Lattice.pdist_invariant` (line 107); $|-z|_M = |z|_M$, `YM.Lattice.pdist_neg` (line 89); $|\tilde z_i| \le |z|_M$, `YM.Lattice.component_le` (line 86).
- No declaration in YM/Lattice, YM/Corona, YM/Space, YM/Gauge, YM/Mink or YM/Wilson states the converse of `YM.Lattice.separation_self`, that $|x - y|_M = 0$ implies $x = y$ (searched for statements of `separation` or `pdist` equal to zero).

### Subdivision

`YM/Lattice/Subdivision.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Ratio` | structure | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L22) | A subdivision of two tori of the same period. |
| `YM.Lattice.Ratio.count` | field | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L23) |  |
| `YM.Lattice.Ratio.exact_size` | field | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L24) |  |
| `YM.Lattice.Ratio.embed` | def | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L29) |  |
| `YM.Lattice.Ratio.lift_embed` | theorem | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L31) |  |
| `YM.Lattice.Ratio.embed_injective` | theorem | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L44) |  |
| `YM.Lattice.Ratio.embed_wrap` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L55) | Canonical embedding is multiplicative scaling even for off-window lifts. |
| `YM.Lattice.Ratio.root` | def | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L67) |  |
| `YM.Lattice.Ratio.root_embed` | theorem | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L77) |  |
| `YM.Lattice.Ratio.signed` | theorem | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L78) |  |
| `YM.Lattice.Ratio.count_dvd` | theorem, private | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L83) |  |
| `YM.Lattice.Ratio.residue` | def | [85](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L85) |  |
| `YM.Lattice.Ratio.residue_wrap` | theorem | [90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L90) |  |
| `YM.Lattice.Ratio.residue_embed` | theorem | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L93) |  |
| `YM.Lattice.Ratio.assemble` | def | [98](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L98) | Every site is uniquely in one centered block. |
| `YM.Lattice.Ratio.assemble_res` | theorem | [100](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L100) |  |
| `YM.Lattice.Ratio.assemble_bijective` | theorem | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L103) |  |
| `YM.Lattice.Ratio.splitSites` | def | [113](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L113) |  |
| `YM.Lattice.Ratio.parent` | def | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L117) | The projected ancestor of a fine site. |
| `YM.Lattice.Ratio.unpack` | theorem | [119](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L119) |  |
| `YM.Lattice.Ratio.assemble_parent` | theorem | [125](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L125) |  |
| `YM.Lattice.Ratio.unpack_at` | theorem | [128](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L128) |  |
| `YM.Lattice.Ratio.unambiguous` | theorem | [132](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L132) |  |
| `YM.Lattice.Ratio.lift_signed_of_odd` | theorem | [138](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L138) |  |
| `YM.Lattice.Ratio.assemble_signed` | theorem | [150](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L150) |  |
| `YM.Lattice.Ratio.parent_signed` | theorem | [154](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Subdivision.lean#L154) |  |

### Support

`YM/Lattice/Support.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Lattice.Support` | abbrev | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L16) |  |
| `YM.Lattice.pdist_step` | theorem | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L20) |  |
| `YM.Lattice.walk_conn` | theorem | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L27) |  |
| `YM.Lattice.wrap_stop_cover` | theorem | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L38) |  |
| `YM.Lattice.halo` | def | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L43) |  |
| `YM.Lattice.halo_spec` | theorem | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L46) |  |
| `YM.Lattice.halo_subset` | theorem | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L49) |  |
| `YM.Lattice.covers` | def | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L52) | Full union of M-balls (not induced subgraph on the centers). |
| `YM.Lattice.covers_some` | theorem | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L57) |  |
| `YM.Lattice.coverNumber` | def | [71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L71) | Minimum number of native `M`-balls with connected union covering X. |
| `YM.Lattice.coverNumber_realized` | theorem | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L73) |  |
| `YM.Lattice.Nonwrapping` | def | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L80) | Strict anchored chart on the torus in native sites (about the tag, not post hoc recentering). Within this box use `lift (x-o)`. |
| `YM.Lattice.agrees_mono` | theorem | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Lattice/Support.lean#L83) | Endpoints need both vertices. |

### Boost

`YM/Mink/Boost.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Mink.Ray` | abbrev | [15](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L15) |  |
| `YM.Mink.Ray.along` | def | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L20) |  |
| `YM.Mink.Ray.alongL` | def | [22](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L22) |  |
| `YM.Mink.Ray.crossT` | def | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L27) |  |
| `YM.Mink.Ray.scalesT` | def | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L28) |  |
| `YM.Mink.Ray.shift` | def | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L30) |  |
| `YM.Mink.Ray.alongL_at` | theorem | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L32) |  |
| `YM.Mink.Ray.along_le` | lemma | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L33) |  |
| `YM.Mink.Ray.ticksT` | theorem | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L36) |  |
| `YM.Mink.Ray.liesT` | theorem | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L37) |  |
| `YM.Mink.Ray.ticksS` | theorem | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L38) |  |
| `YM.Mink.Ray.liesS` | theorem | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L39) |  |
| `YM.Mink.Ray.newClock` | lemma | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L41) |  |
| `YM.Mink.Ray.newSpace` | lemma | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L43) |  |
| `YM.Mink.Ray.newProjection` | lemma | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L45) |  |
| `YM.Mink.Ray.adds` | lemma | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L48) |  |
| `YM.Mink.Ray.beginShift` | lemma | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L54) |  |
| `YM.Mink.Ray.motion` | def | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L56) |  |
| `YM.Mink.Ray.steps` | theorem | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L62) |  |
| `YM.Mink.Ray.start` | theorem | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L63) |  |
| `YM.Mink.Ray.groupL` | theorem | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L64) |  |
| `YM.Mink.Ray.flip` | theorem | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L65) |  |
| `YM.Mink.Ray.positive` | lemma | [67](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L67) |  |
| `YM.Mink.Ray.staysM` | lemma | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L86) |  |
| `YM.Mink.Ray.boost` | def | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L92) |  |
| `YM.Mink.Ray.boost_at` | theorem | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L103) |  |
| `YM.Mink.Ray.boost_start` | theorem | [104](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L104) |  |
| `YM.Mink.Ray.boost_add` | theorem | [105](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L105) |  |
| `YM.Mink.Ray.boost_neg` | theorem | [106](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L106) |  |
| `YM.Mink.Ray.continuousBoost` | lemma | [108](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L108) |  |
| `YM.Mink.Ray.generator` | theorem | [114](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L114) |  |
| `YM.Mink.Ray.fromAxis` | def | [120](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L120) | Convenient positive coordinate ray. |
| `YM.Mink.Ray.onAxis` | theorem | [121](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L121) |  |
| `YM.Mink.Ray.time_gen` | theorem | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L124) |  |
| `YM.Mink.Ray.space_gen` | theorem | [127](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L127) | Positive boost sign used in the boost Lie contract. |
| `YM.Mink.Lorentz.from_half` | theorem | [135](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Boost.lean#L135) | joint halfspace assertion for every Lorentz-transformed word *really* sharpens to the cone (in the Euclidean frequency convention). |

### Geometry

`YM/Mink/Geometry.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Mink.clockL` | def | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L18) |  |
| `YM.Mink.restL` | def | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L21) |  |
| `YM.Mink.clockL_at` | theorem | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L24) |  |
| `YM.Mink.restL_at` | theorem | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L25) |  |
| `YM.Mink.clock_cont` | theorem | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L27) |  |
| `YM.Mink.rest_cont` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L28) |  |
| `YM.Mink.clock_add` | theorem | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L29) |  |
| `YM.Mink.clock_mul` | theorem | [30](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L30) |  |
| `YM.Mink.clock_neg` | theorem | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L31) |  |
| `YM.Mink.rest_add` | theorem | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L32) |  |
| `YM.Mink.rest_mul` | theorem | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L33) |  |
| `YM.Mink.rest_neg` | theorem | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L34) |  |
| `YM.Mink.clock_zero` | theorem | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L35) |  |
| `YM.Mink.rest_zero` | theorem | [36](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L36) |  |
| `YM.Mink.divide` | def | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L39) | Coordinates interconvert continuously; volume assertion below. |
| `YM.Mink.divide_at` | theorem | [47](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L47) |  |
| `YM.Mink.combine_at` | theorem | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L48) |  |
| `YM.Mink.ext_by` | theorem | [50](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L50) |  |
| `YM.Mink.roll_clock` | lemma | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L53) |  |
| `YM.Mink.roll_space` | lemma | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L54) |  |
| `YM.Mink.pairing` | lemma | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L57) |  |
| `YM.Mink.squares` | lemma | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L62) |  |
| `YM.Mink.divide₂` | def | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L65) |  |
| `YM.Mink.volume_divide` | theorem | [74](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L74) |  |
| `YM.Mink.m` | def | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L77) |  |
| `YM.Mink.cone` | def | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L78) |  |
| `YM.Mink.inside` | def | [79](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L79) |  |
| `YM.Mink.spacelike` | def | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L80) |  |
| `YM.Mink.cont_m` | lemma | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L82) |  |
| `YM.Mink.closed_cone` | lemma | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L83) |  |
| `YM.Mink.open_inside` | lemma | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L84) |  |
| `YM.Mink.open_spacelike` | lemma | [85](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L85) |  |
| `YM.Mink.cone_self` | lemma | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L87) |  |
| `YM.Mink.strict_self` | lemma | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L95) |  |
| `YM.Mink.lateral` | lemma | [103](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L103) |  |
| `YM.Mink.self_pair` | lemma | [107](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L107) |  |
| `YM.Mink.cone_test` | lemma | [113](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L113) |  |
| `YM.Mink.strict_pair` | theorem | [131](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Geometry.lean#L131) |  |

### Lorentz

`YM/Mink/Lorentz.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Mink.Coord` | abbrev | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L16) |  |
| `YM.Mink.General` | abbrev | [17](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L17) |  |
| `YM.Mink.General.walk` | def | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L20) |  |
| `YM.Mink.General.stretch` | def | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L21) |  |
| `YM.Mink.General.walk_one` | theorem | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L23) |  |
| `YM.Mink.General.walk_mul` | theorem | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L24) |  |
| `YM.Mink.General.retrace` | theorem | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L25) |  |
| `YM.Mink.General.proceeds` | theorem | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L26) |  |
| `YM.Mink.General.north` | theorem | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L27) |  |
| `YM.Mink.General.comp` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L28) |  |
| `YM.Mink.General.ext` | theorem | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L29) |  |
| `YM.Mink.Proper` | def | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L32) |  |
| `YM.Mink.Lorentz` | abbrev | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L46) |  |
| `YM.Mink.Lorentz.act` | abbrev | [49](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L49) |  |
| `YM.Mink.Lorentz.det` | theorem | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L51) |  |
| `YM.Mink.Lorentz.keeps` | theorem | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L52) |  |
| `YM.Mink.Lorentz.keepsCone` | theorem | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L53) |  |
| `YM.Mink.Lorentz.stays` | theorem | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L54) |  |
| `YM.Mink.Lorentz.act_one` | theorem | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L61) |  |
| `YM.Mink.Lorentz.act_mul` | theorem | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L62) |  |
| `YM.Mink.Lorentz.undoes` | theorem | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L63) |  |
| `YM.Mink.Lorentz.starts` | theorem | [64](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L64) |  |
| `YM.Mink.Lorentz.ext` | theorem | [66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L66) |  |
| `YM.Mink.Lorentz.sends` | def | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L68) |  |
| `YM.Mink.Lorentz.sent` | theorem | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L69) |  |
| `YM.Mink.Lorentz.forwards` | theorem | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L70) |  |
| `YM.Mink.Lorentz.usual` | theorem | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L73) |  |
| `YM.Mink.Lorentz.preserves` | theorem | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L75) |  |
| `YM.Mink.Lorentz.reverseL` | def | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L82) | Spatial reversal for switching between placements and covectors via the spacetime metric. Frequency/position pair, however, stays Euclidean. |
| `YM.Mink.Lorentz.reversing` | theorem | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L91) |  |
| `YM.Mink.Lorentz.reversal` | theorem | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L92) |  |
| `YM.Mink.Lorentz.reverse_inv` | theorem | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L93) |  |
| `YM.Mink.Lorentz.dual` | def | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L95) |  |
| `YM.Mink.Lorentz.bil` | lemma, private | [105](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L105) |  |
| `YM.Mink.Lorentz.dual_sent` | theorem | [120](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L120) |  |
| `YM.Mink.Lorentz.dual_involution` | theorem | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L124) |  |
| `YM.Mink.Lorentz.dual_adjoint` | lemma | [132](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Lorentz.lean#L132) |  |

### Poincare

`YM/Mink/Poincare.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Mink.Lorentz.properTurn` | abbrev | [14](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L14) |  |
| `YM.Mink.Lorentz.spatialTurn` | def | [16](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L16) |  |
| `YM.Mink.Lorentz.room` | def | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L18) |  |
| `YM.Mink.Poincare` | structure | [32](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L32) |  |
| `YM.Mink.Poincare.Λ` | field | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L33) |  |
| `YM.Mink.Poincare.b` | field | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L34) |  |
| `YM.Mink.Poincare.ext` | theorem | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L38) |  |
| `YM.Mink.Poincare.sends` | def | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L41) |  |
| `YM.Mink.Poincare.base` | lemma | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L42) |  |
| `YM.Mink.Poincare.by_placement` | theorem | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L44) |  |
| `YM.Mink.Poincare.oneL` | theorem | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L52) |  |
| `YM.Mink.Poincare.oneB` | theorem | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L53) |  |
| `YM.Mink.Poincare.productL` | theorem | [54](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L54) |  |
| `YM.Mink.Poincare.productB` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L55) |  |
| `YM.Mink.Poincare.invL` | theorem | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L56) |  |
| `YM.Mink.Poincare.invB` | theorem | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L57) |  |
| `YM.Mink.Poincare.sends_one` | theorem | [58](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L58) |  |
| `YM.Mink.Poincare.sends_mul` | theorem | [59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L59) |  |
| `YM.Mink.Poincare.backwards` | theorem | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L61) |  |
| `YM.Mink.Poincare.unmade` | theorem | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L70) |  |
| `YM.Mink.Poincare.emerges` | theorem | [71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L71) |  |
| `YM.Mink.Poincare.presentations` | def | [73](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L73) |  |
| `YM.Mink.Poincare.standard` | lemma | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L75) |  |
| `YM.Mink.Poincare.continuousL` | theorem | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L76) |  |
| `YM.Mink.Poincare.continuousB` | theorem | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L77) |  |
| `YM.Mink.Poincare.ct` | theorem | [78](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L78) |  |
| `YM.Mink.Poincare.togetherCt` | theorem | [79](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L79) |  |
| `YM.Mink.Poincare.continuousPlacement` | theorem | [80](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L80) |  |
| `YM.Mink.Poincare.translation` | def | [86](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L86) | Pure translations. |
| `YM.Mink.Poincare.motion` | def | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L87) |  |
| `YM.Mink.Poincare.stand` | theorem | [88](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L88) |  |
| `YM.Mink.Poincare.inactive` | theorem | [89](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L89) |  |
| `YM.Mink.Poincare.as_move` | theorem | [90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L90) |  |
| `YM.Mink.Poincare.as_active` | theorem | [91](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L91) |  |
| `YM.Mink.Poincare.overL` | theorem | [92](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L92) |  |
| `YM.Mink.Poincare.overE` | theorem | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L93) |  |
| `YM.Mink.Poincare.continuousM` | theorem | [94](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L94) |  |
| `YM.Mink.Poincare.continuousE` | theorem | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L95) |  |
| `YM.Mink.Poincare.preserving` | lemma | [101](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L101) |  |
| `YM.Mink.Poincare.togetherL` | def | [104](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L104) |  |
| `YM.Mink.Poincare.togetherL_at` | theorem | [112](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L112) |  |
| `YM.Mink.Poincare.togetherS_at` | theorem | [113](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L113) |  |
| `YM.Mink.Poincare.zusammen` | def | [115](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L115) |  |
| `YM.Mink.Poincare.together` | lemma | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Mink/Poincare.lean#L117) |  |

### Configurations

`YM/Space/Configurations.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.E4` | abbrev | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L24) |  |
| `YM.Space3` | abbrev | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L25) |  |
| `YM.time` | def | [27](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L27) |  |
| `YM.spatial` | def | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L28) |  |
| `YM.position` | def | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L29) |  |
| `YM.time_position` | theorem | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L31) |  |
| `YM.spatial_position` | theorem | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L33) |  |
| `YM.position_eta` | theorem | [35](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L35) |  |
| `YM.basis` | def | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L42) |  |
| `YM.basis_eq` | theorem | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L44) |  |
| `YM.basis_inner` | theorem | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L46) |  |
| `YM.basis_norm` | theorem | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L48) |  |
| `YM.cubedist` | def | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L51) | The `L^∞` distance used in the cell bounds (includes time). |
| `YM.continuous_cubedist` | theorem | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L53) |  |
| `YM.Points` | abbrev | [56](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L56) |  |
| `YM.points` | def | [59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L59) | Wrap a tuple. |
| `YM.points_apply` | theorem | [60](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L60) |  |
| `YM.points_eta` | theorem | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L61) |  |
| `YM.conf` | def | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L63) |  |
| `YM.generic` | def | [66](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L66) | All coordinate projections separate. Do not confuse with `conf`. |
| `YM.spaced` | def | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L70) | Stated as a predicate avoiding an `n ≥ 2` condition. Use with `0 < r` for separated positions; with `r ≤ 1` for the capped bounds. |
| `YM.generic_conf` | theorem | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L72) |  |
| `YM.spaced_conf` | theorem | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L76) |  |
| `YM.conf_open` | theorem | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L83) |  |
| `YM.Points.head` | def | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L96) |  |
| `YM.Points.tail` | def | [97](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L97) |  |
| `YM.Points.cons` | def | [98](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L98) |  |
| `YM.Points.peel` | def | [100](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L100) |  |
| `YM.Points.peel_fst` | theorem | [129](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L129) |  |
| `YM.Points.peel_snd` | theorem | [130](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L130) |  |
| `YM.Points.flatten` | def | [133](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L133) | Flatten spacetime vectors (including times) to Euclidean `4n` vectors. |
| `YM.Points.flatten_at` | theorem | [145](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L145) |  |
| `YM.Points.volume_nil` | theorem | [147](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L147) |  |
| `YM.Points.volume_product` | theorem | [153](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Configurations.lean#L153) | Defuse the PiLp vs Pi convention for spacetime Lebesgue volume. |

### Index

`YM/Space/Index.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Axis` | abbrev | [18](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L18) |  |
| `YM.SpaceAxis` | abbrev | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L19) |  |
| `YM.timeAxis` | abbrev | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L20) |  |
| `YM.Four` | abbrev | [21](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L21) |  |
| `YM.Signed` | structure | [23](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L23) |  |
| `YM.Signed.perm` | field | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L24) |  |
| `YM.Signed.flip` | field | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L25) |  |
| `YM.Signed.one_perm` | theorem | [38](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L38) |  |
| `YM.Signed.one_flip` | theorem | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L39) |  |
| `YM.Signed.mul_perm` | theorem | [40](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L40) |  |
| `YM.Signed.mul_perm_apply` | theorem | [41](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L41) |  |
| `YM.Signed.mul_flip` | theorem | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L42) |  |
| `YM.Signed.inv_perm` | theorem | [44](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L44) |  |
| `YM.Signed.inv_flip` | theorem | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L45) |  |
| `YM.Signed.mirror` | def | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L55) |  |
| `YM.Signed.mirror_inv` | theorem | [57](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L57) |  |
| `YM.Signed.act` | def | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L62) |  |
| `YM.Signed.act_at` | theorem | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L65) |  |
| `YM.Signed.act_one` | theorem | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L68) |  |
| `YM.Signed.act_mul` | theorem | [70](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L70) |  |
| `YM.Signed.act_inv` | theorem | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L76) |  |
| `YM.Signed.inv_act` | theorem | [77](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L77) |  |
| `YM.Signed.act_add` | theorem | [83](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L83) |  |
| `YM.Signed.actEquiv` | def | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L87) |  |
| `YM.Signed.act_zero` | theorem | [94](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L94) |  |
| `YM.Signed.act_neg` | theorem | [95](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L95) |  |
| `YM.Signed.act_sub` | theorem | [96](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L96) |  |
| `YM.Signed.act_injective` | theorem | [98](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Index.lean#L98) |  |

Covered by [Axes and four-component arrays](../roadmap/setting/lattice-gauge-wilson/axes-and-arrays.md) (`YM.Axis`, `YM.Four`).

Lean-side notes:

- `YM.Axis` (line 18) is `Fin 4` and `YM.Four R` (line 21) is the type of maps from the axes to `R`; neither adds structure. When `R` has an addition, arrays (and the sites of the periodic lattice) are added coordinatewise by Mathlib's instances on function types (`Mathlib/Algebra/Group/Pi/Basic.lean`, imported by the file); no declaration of the unit adds it.
- The time axis is the separate declaration `YM.timeAxis` (line 20), `Fin.last 3`, and the module docstring says "Time is axis 3 throughout". The spatial axes are `YM.SpaceAxis` (line 19), `Fin 3`. Neither has an article; the axes-and-arrays article states that axis 3 is time only as the book's convention.

### Orthogonal

`YM/Space/Orthogonal.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.M4` | abbrev | [19](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L19) |  |
| `YM.Ortho` | abbrev | [20](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L20) |  |
| `YM.M4.move` | def | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L24) |  |
| `YM.M4.at_coord` | theorem | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L26) |  |
| `YM.M4.move_one` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L28) |  |
| `YM.M4.move_mul` | theorem | [33](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L33) |  |
| `YM.M4.move_basis` | theorem | [37](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L37) |  |
| `YM.Ortho.transp` | theorem | [43](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L43) |  |
| `YM.Ortho.move` | def | [46](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L46) |  |
| `YM.Ortho.move_mul` | theorem | [48](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L48) |  |
| `YM.Ortho.move_one` | theorem | [51](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L51) |  |
| `YM.Ortho.move_inv` | theorem | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L52) |  |
| `YM.Ortho.inv_move` | theorem | [53](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L53) |  |
| `YM.Ortho.move_norm` | theorem | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L55) |  |
| `YM.Ortho.motion` | def | [63](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L63) |  |
| `YM.Ortho.motion_at` | theorem | [72](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L72) |  |
| `YM.Ortho.move_injective` | theorem | [74](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L74) |  |
| `YM.Ortho.ext` | theorem | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L76) |  |
| `YM.Signed.matrix` | def | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L87) |  |
| `YM.Signed.matrix_at` | lemma | [90](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L90) |  |
| `YM.Signed.ortho` | def | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L93) |  |
| `YM.Signed.ortho_move` | theorem | [108](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L108) |  |
| `YM.Signed.inclusionO` | def | [117](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L117) |  |
| `YM.Signed.reflect` | def | [122](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L122) |  |
| `YM.Signed.mirrored` | theorem | [124](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L124) |  |
| `YM.Ortho.skewSpace` | def | [132](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L132) | `so(4)` as real skew matrices. |
| `YM.Ortho.Skew` | abbrev | [144](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L144) |  |
| `YM.Ortho.oneParameter` | def | [146](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L146) |  |
| `YM.Ortho.plane` | def | [152](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Space/Orthogonal.lean#L152) | Entry `(i,j)=1`, `(j,i)=-1` when distinct. In `Plane timeAxis l`, coordinate vector field is `xˡ∂_y - y∂_l` with `y = Euclidean time` . |

### Unison

`YM/TraceExtension/Quince/Unison.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.PhysicalNext.Repeat.Quince.wipe` | def | [10](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/TraceExtension/Quince/Unison.lean#L10) |  |
| `YM.PhysicalNext.Repeat.Quince.wiping` | lemma | [12](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/TraceExtension/Quince/Unison.lean#L12) |  |
| `YM.PhysicalNext.Repeat.Quince.wound` | lemma | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/TraceExtension/Quince/Unison.lean#L24) |  |
| `YM.PhysicalNext.Repeat.Quince.prime_fuel` | lemma | [26](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/TraceExtension/Quince/Unison.lean#L26) |  |

### Law

`YM/Wilson/Law.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Wilson.Config` | abbrev | [24](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L24) |  |
| `YM.Wilson.CoverConfig` | abbrev | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L25) |  |
| `YM.Wilson.energy` | def | [29](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L29) |  |
| `YM.Wilson.energy_nonneg` | theorem | [31](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L31) |  |
| `YM.Wilson.continuous_travel` | theorem | [34](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L34) |  |
| `YM.Wilson.energy_cont` | theorem | [42](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L42) |  |
| `YM.Wilson.energy_pull` | theorem | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L45) |  |
| `YM.Wilson.energy_gauge` | theorem | [52](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L52) |  |
| `YM.Wilson.prior` | def | [55](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L55) |  |
| `YM.Wilson.bare` | def | [58](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L58) |  |
| `YM.Wilson.bare_pos` | theorem | [59](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L59) |  |
| `YM.Wilson.bare_cont` | theorem | [61](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L61) |  |
| `YM.Wilson.measurable_bare` | theorem | [62](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L62) |  |
| `YM.Wilson.bare_pull` | theorem | [65](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L65) |  |
| `YM.Wilson.bare_gauge` | theorem | [68](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L68) |  |
| `YM.Wilson.bare_integrable` | theorem | [71](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L71) |  |
| `YM.Wilson.partition` | def | [74](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L74) |  |
| `YM.Wilson.partition_pos` | theorem | [76](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L76) |  |
| `YM.Wilson.weight` | def | [82](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L82) |  |
| `YM.Wilson.weight_meas` | theorem | [84](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L84) |  |
| `YM.Wilson.law` | def | [87](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L87) |  |
| `YM.Wilson.moment` | def | [99](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L99) | Use with integrable functions only. |
| `YM.Wilson.continuous_integrable` | theorem | [101](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L101) |  |
| `YM.Wilson.bounded_integrable` | theorem | [105](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L105) |  |
| `YM.Wilson.moment_formula` | theorem | [110](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Law.lean#L110) | Rewrite law back in terms of unnormalized weight. |

Covered by [Lattice gauge configurations](../roadmap/setting/lattice-gauge-wilson/lattice-gauge-configurations.md) (`YM.Wilson.Config`).

Lean-side notes:

- `YM.Wilson.Config G n` (line 24) is `Links (Per n) G.El`, with no conditions. Its product topology and measurable structure come from Mathlib's instances on function types, not from the definition.
- The product Haar measure is `YM.Wilson.prior` (line 55, `Measure.pi` of `YM.Gauge.probHaar` over the links), and the Boltzmann weight is `YM.Wilson.bare` (line 58, $e^{-\beta E(U)}$ with `YM.Wilson.energy`, line 29). Neither has an article; the configuration article mentions neither. The cover configurations `YM.Wilson.CoverConfig` (line 25, `Links ℤ G.El`) have no article.
- The Wilson energy and law that the chapter page describes in words: `YM.Wilson.energy` (line 29) sums `YM.Gauge.price` $= 1 - \operatorname{Re}\operatorname{tr}(\cdot)/(n+1)$ (MatrixGroup.lean:112) of `YM.Lattice.faceValue` (Faces.lean:47), the transport around the unit square, over `YM.Lattice.Face` (Faces.lean:14), the pairs of a site and axes $i < j$; `YM.Wilson.partition` (line 74) is the integral of `YM.Wilson.bare` against `YM.Wilson.prior`, positive by `YM.Wilson.partition_pos` (line 76); `YM.Wilson.law` (line 87) is `YM.Wilson.prior` with density `YM.Wilson.weight` (line 82), $e^{-\beta E}/Z$, for every real $\beta$.
- Relation to the public notions, which the articles do not state (rule 5): `YangMills.energy_eq` (WilsonBridge.lean:32) proves that the public Wilson action of a configuration equals `YM.Wilson.energy` for the internal gauge group `YangMills.GaugeGroup.core g`, and `YangMills.law_eq` (WilsonBridge.lean:43) that the public Wilson measure with Haar measure `g.core.probHaar` equals `YM.Wilson.law`; `YangMills.wilsonFamily` (WilsonBridge.lean:20) sets the Haar measure of the public family it builds to `g.core.probHaar`. These declarations belong to Armstrong's unit VIII.1.

### Symmetry

`YM/Wilson/Symmetry.lean`

| Lean name | Kind | Line | Docstring |
| --- | --- | --- | --- |
| `YM.Wilson.sendEdge` | def | [25](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L25) | Permutation used in the Haar computation, maps positive links to positive orientations of their images. On e.g. a negative reflection this also shifts the base by one negative step. |
| `YM.Wilson.sendEdge_injective` | theorem | [28](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L28) |  |
| `YM.Wilson.continuous_pull` | theorem | [39](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L39) |  |
| `YM.Wilson.prior_pull` | theorem | [45](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L45) | Pullback is one relabelling of independent Haar links, with inversion. |
| `YM.Wilson.prior_gauge` | theorem | [69](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L69) |  |
| `YM.Wilson.law_preserved` | theorem | [75](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L75) | No bijectivity assumption needed here. |
| `YM.Wilson.law_pull` | theorem | [93](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L93) |  |
| `YM.Wilson.law_gauge` | theorem | [97](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L97) |  |
| `YM.Wilson.law_translate` | theorem | [101](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L101) |  |
| `YM.Wilson.moment_pull` | theorem | [106](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Wilson/Symmetry.lean#L106) |  |

