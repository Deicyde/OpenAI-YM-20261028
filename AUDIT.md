# Audit of the public challenge in `yang-mills-group/OpenAI-YM-20261028`

Scope: `Challenge.lean` and its trusted base `ChallengeSpec.lean`, `PublicWilson.lean`,
`PublicTheory.lean` (613 lines) on top of Mathlib `81a5d257`, Lean `v4.32.0`.
Repository state: single commit `3456e5e` (2026-11-05). Audit date: 2026-11-11.

Companion documents:
- `AUDIT-DEFINITIONS.md`: verdicts for all 173 trusted items, with adversarial checks on
  every finding.
- `Audit/`: Lean checks built only on the trusted files.
- `AuditScripts/`: the inventory scripts, the axiom check, and the probes cited in the
  definition audit.

## Bottom line

1. **Mechanically the trusted surface is clean.**
   - The four files compile on the pinned toolchain and Mathlib.
   - They contain no axioms, no compile-time code (`#eval`, `run_cmd`, `initialize`), and
     no macros, notations or elaborators.
   - The only `sorry` is the intended placeholder.
2. **The lattice clause carries no content. This is proved in Lean.**
   `YMAudit.jointExistence_of_continuum` (`Audit/Reduction/Main.lean`) derives
   `JointExistence` from continuum data alone. It needs a hierarchy satisfying the three
   continuum clauses `Reconstructed`, `OperatorProductExpansion` and `TraceTest`, plus one
   mild extra condition, `ZeroInvisible` (correlations vanish on words containing the
   zero field vector). The Wilson family it builds has insertions that never read the
   gauge field, so the Wilson measure, plaquette action, β and Haar measure play no role.
   It builds from scratch with only the standard axioms (§4).
3. **What remains is satisfiable without Yang–Mills.** On paper, a generalized free field
   satisfies every continuum clause. The gauge group enters only through the constant
   `3·dim 𝔤/π⁴`, which can itself be fixed by rescaling the trace field (a Lean probe
   shows this). So a Comparator pass on `YangMills.jointExistence` does not certify
   "a Wightman QFT obtained as a scaling limit of Wilson lattice gauge theory", nor does
   it distinguish gauge groups. Any evidence for that stronger claim lives in the
   submission's internal definitions.
4. **Most of the ~200 trusted items are faithful.** Of 173 audited items:
   - 98 carry real content, mostly faithful Wightman, OPE and reconstruction definitions;
   - 29 are redundant;
   - 38 are inert under the reduction (the entire lattice layer, `WilsonRegularity`, the
     Wilson clause and the non-selected phases);
   - 7 form the gauge-group layer, which matters only through `dim 𝔤`.

   See `AUDIT-DEFINITIONS.md`.
5. **The submitter's bundled verification logs are for a different `PublicTheory.lean`**
   (`3940e8dd…`) than the one shipped (`94111ad2…`). The group's own Comparator record of
   30 Oct used the shipped file, and I rebuilt the shipped sources myself.

## 1. Main finding: the lattice clause is redundant

Let `T₀` be any hierarchy, over any Wilson family, such that:
- `Reconstructed`, `OperatorProductExpansion` and `TraceTest` hold;
- its selected phase gives correlation 0 to words containing the zero vector
  (`ZeroInvisible`; true whenever correlations are linear in each field).

From `T₀`, `Audit/Reduction/Defs.lean` builds the following.

**Wilson family (`blindFamily`).** Use periods `p+1`, denominators `N+2` and
`β_{N,p} = log(N+2) = log(1/a_N)`, so the slope is 1. Take `haar` to be the Haar
probability measure and `Token := Σ d, Field d`. The insertion is
`I_{N,p}(v, x; U) := 1` if `v = ⟨0, 0⟩` (the zero vector of grade 0), and `0` otherwise.
It is constant in `U`, so it is continuous, gauge invariant and local with an empty
stencil.

**Hierarchy (`reduced T₀`).** Reuse `T₀`'s Hilbert space, fields, labels, continuation and
trace, and set `project := id`. Take two phases, realized as the subset `{0, 1}` of `ℝ`,
with the uniform measure and `selected := 0`. Let `P(a) := 1` if every tag of the word `a`
is `⟨0, 0⟩` (including the empty word), and `0` otherwise. Then set:
- `correlation (some 0) := S` (the selected phase of `T₀`)
- `correlation none := P`
- `correlation (some 1) := 2P − S`

The channels are `T₀`'s channels plus one extra grade-0 channel. Its actor is the zero
vector and its coefficient is `P(a)`. `T₀`'s coefficient is set to 0 on any channel whose
actor is the zero vector.

**Why every clause holds, and where it is proved:**

| Clause | Why | Lean |
|---|---|---|
| `WilsonRegularity` | Insertions are constant in the links. | `Regular.lean` |
| Haar probability measure | `g.image` is a compact group. | `Haar.lean` |
| Finite moments | The Wilson law is a probability measure, so moments are 0 or 1. | `Law.lean` |
| `wilson` (`Converges`) | The smeared sums are lattice Riemann sums of `t`. | `Riemann.lean`, `Converges.lean` |
| `Reconstructed` | Selected-phase clauses are `T₀`'s; the two phases average to `P`. | `Recon.lean` |
| `OperatorProductExpansion` | Phase `S`: new terms vanish by `ZeroInvisible`. Phase `P`: the remainder is 0. Phase `2P − S`: remainder is minus the `S` one. | `OPE.lean` |
| `TraceTest` | It reads only the selected phase. | `Trace.lean` |

All files are under `Audit/Reduction/`. `Main.lean` assembles them into
`wilson_clause_redundant` (per gauge group) and `jointExistence_of_continuum`.

**The extra hypothesis.** `ZeroInvisible` is not a clause of the challenge. It is needed
because `Hierarchy.correlation` is never required to be linear in the field vectors. It
holds in every multilinear model, including, on paper, the generalized free field below.
It does not follow from `Reconstructed` in general. The definition audit's follow-up 3
shows that `Reconstructed.boundary` forces it for one-point words, but not for words with
two or more points: Lean's Bochner integral returns 0 on non-integrable integrands, so
those words are not pinned.

**Satisfying the hypothesis without Yang–Mills (paper argument, not in Lean).** Take the
scalar field `φ` with Källén–Lehmann density `ρ(s) = (dim 𝔤/16π²)·s²/log² s` for
`s ≥ s₀ > 1`. Its derivatives and Wick monomials are graded by engineering dimension.
Then:
- `S₂(r) ~ 3·dim 𝔤/(π⁴ r⁸ log²(1/r))`;
- Wick's theorem gives an all-orders OPE with finitely many monomials per grade;
- the Fock space gives W0–W3;
- `excludes` follows from the log² law. The submission's own `Wick.euclidean_excludes`
  uses only that law.

Two independent reviewers attempted to derive a contradiction from the hypothesis and
found none.

**Mechanism.**
- `Properties.wilson` (`ChallengeSpec.lean:178`) reads only the unselected correlation.
- `Reconstructed` (`ChallengeSpec.lean:117`) requires a Wightman theory only for the
  selected phase.
- `WilsonFamily.insertion` (`PublicWilson.lean:45`) is otherwise unconstrained.
- `correlation` and `coefficient` (`ChallengeSpec.lean:41, 46`) need not be multilinear.

The detailed theorem `YangMills.constructed` does prove a reconstruction for every
character (`Construction.lean:27`), but `JointExistence` does not ask for it.

**What would close it.**
1. **F1 (recommended).** Require `Reconstructed` for every character, not only the
   selected one. Per-character data forces the zero-word correlation to be 0, which rules
   out the `2P − S` phase; Lean check: `AuditScripts/Probes/reconbridge_perphase.lean`. A
   standard-math argument extends this to every link-blind Wilson limit. The detailed
   theorem already proves this data, so `Solution.lean` would not need to change.
2. **F2 (complementary).** Require `correlation`, `coefficient` and `continuation` to be
   multilinear in the field vectors. This needs a `Module ℂ` structure on
   `WilsonFamily.Token`.
3. **Not sufficient on their own:**
   - fixing the insertions to specified lattice operators, because bounded insertions
     concentrate as β → ∞ and reproduce `P`;
   - a stronger `localSupport`;
   - identifying `centeredTrace` with a lattice observable.

The group's `AcceptanceSpec.lean` (in `yang-mills-group/YM`) avoids this hole by
quantifying over the submission's own `YM.Family` and `Spec.Final`. The price is that
those internal definitions then need human review.

## 2. Other findings

| # | Severity | Location | Finding |
|---|---|---|---|
| 2.1 | High (evidence) | `verification/verified-sources.sha256`, `verification/joint-check.log:5` | The submitter's logged verification used `PublicTheory.lean` with SHA-256 `3940e8dd…`. The shipped file, `challenge.sha256`, `SOURCES.sha256` and the group's import all give `94111ad2…`. The other 19 verified files match. The `3940e8dd…` version is not public, so the change is unknown. The group's 30 Oct Comparator record ran on the shipped file. It ran in non-isolated macOS dev mode, and its recorded paths are under `/Users/oai/Documents/Codex/…`, so the independence of that run is worth confirming. |
| 2.2 | High | `ChallengeSpec.lean:168–175`, `:181` | `TraceTest` amounts to `centered ∧ shortDistance`. `amplitudePositive` follows from `IsSimple`, and `excludes` follows from `shortDistance`. So the "non-freeness" test is one two-point asymptotic for an unidentified grade-4 field, which a generalized free field passes. The README and assessment concede that generalized free fields are not excluded. |
| 2.3 | Medium | `ChallengeSpec.lean:48`, `:172–174` | The gauge group can be rescaled away. Scaling every label by `k` multiplies `traceTwo` by `k²` and preserves every other clause. So the constant `3·dim 𝔤/π⁴`, or any nonzero complex constant, can be met, and `JointExistence` for one group yields it for all groups (`AuditScripts/Probes/inventory_crossgroup.lean`). Nothing fixes the normalization or Hermiticity of `centeredTrace`. |
| 2.4 | Medium | `ChallengeSpec.lean:139–143` | `Reconstructed.boundary` uses a Bochner integral, which Lean sets to 0 on non-integrable integrands, and `continuation` has no growth hypothesis. For words with a zero-label tag and at least two points, the Euclidean correlation is therefore not pinned. One consequence: `TraceTest.centered` is vacuous when `centeredTrace = 0`. For one-point words the clause does force the correlation to vanish (`AuditScripts/Probes/reconbridge_zerojunk.lean` plus a paper argument). Fix: require integrability, or impose multilinearity (F2). |
| 2.5 | Medium | `ChallengeSpec.lean:28–31`, `:45–47`, `:120–122` | `Hierarchy.Field`, `actor`, `coefficient`: actors need not be nonzero or independent, and coefficients need not be multilinear, covariant or measurable. `covers` with `injective` forces cumulative grades, so a "grade" is a filtration level chosen by the prover. |
| 2.6 | Low | `PublicTheory.lean:225`, `:288–307` | `onLabels` may depend on the translation part of a Poincaré element, unlike Streater–Wightman. Inside `JointExistence` this is neutralized (`AuditScripts/Probes/labelope_orbit.lean` plus an argument via the OPE). |
| 2.7 | Low | `ChallengeSpec.lean:13–14` | `running` accepts any positive slope (not the asymptotic-freedom slope) and allows an `o(log a⁻¹)` drift. |
| 2.8 | Info | `ChallengeSpec.lean:186–188` | The hierarchy may depend on the subsequence, so there is no uniqueness of the limit. This is acknowledged in the README. |
| 2.9 | Info | `PublicTheory.lean:181` | `EnergyMomentumMeasure.projection` is defined on all sets. Its values on non-Borel sets are junk but never read. |
| 2.10 | Info | `PublicTheory.lean:99` | The field named `module` is fine. In Lean 4.32 `module` is a header-only keyword and is not in the global token table; the shipped file compiles with it. |

## 3. What checks out

- **Gauge group.** `GaugeGroup` / `IsSimple` (`PublicTheory.lean:25–45`): the Lie algebra
  is pinned exactly by `exp`, and simplicity means nonabelian with no proper nonzero
  ideals. Both are correct and satisfiable (SU(2)). Disconnected groups and reducible
  faithful representations are allowed by design.
- **Lattice.** The periodic lattice, plaquette orientation, Wilson energy
  `1 − Re tr/(n+1)`, normalized law, finite moments and the `mesh^{4n}` Riemann-sum
  smearing over `(−P/2, P/2]` are all standard. `Converges` takes the full UV limit at
  fixed volume, then the IR limit along the subsequence. `volume` on `Points n` is
  Lebesgue.
- **Wightman axioms.** W0–W3 are a reasonable rendering:
  - `charFun` uses `exp(+i⟨x,t⟩)`, so with the forward-cone condition `U(τe_t) = e^{iHτ}`
    with `H ≥ 0`. This is consistent with the covariance and with the orientation of
    `orderedTube`.
  - Temperedness is stated as strong continuity (stronger than usual).
  - The cyclic domain is exactly the polynomial domain.
  - Adjoint, locality and unique vacuum are present.
- **OPE.** A faithful, uniform all-orders estimate with one coefficient system shared by
  all phases. It is generic, though: a generalized free field satisfies it too.
- **Smoothness.** `∞` means C^∞, and `TestFunction … ⊤` is smooth with compact support.

## 4. Mechanical checks performed

- **Challenge build.** `lake build WilsonReference` compiles `PublicTheory`,
  `PublicWilson`, `ChallengeSpec` and `Challenge` on Lean 4.32.0 with the pinned Mathlib.
  The only warning is the expected `sorry` in `Challenge.lean:5`.
- **Audit library.** A from-scratch `lake build Audit` compiles `Audit.BlindFamily` and
  all ten `Audit.Reduction` modules with no `sorry`. `AuditScripts/Axioms.lean` reports
  that each of the following depends only on `propext`, `Classical.choice` and
  `Quot.sound`:
  - `YMAudit.jointExistence_of_continuum`
  - `YMAudit.wilson_clause_redundant`
  - `AuditDemo.blind_regular`

  Every theorem statement in `Audit/Reduction` is unchanged from the skeleton it was
  written against.
- **Probes** cited in `AUDIT-DEFINITIONS.md`, compiled in the same tree with
  `lake env lean`:

  | Probe | Shows | Result |
  |---|---|---|
  | `bridge_decouple` | selected phase decoupled from the Wilson limit | compiles; 3 axiom report(s), standard only |
  | `gffgap_emptycluster` | empty-cluster OPE forces an identity field | compiles; 4 axiom report(s), standard only |
  | `hierope_antiphase` | the `2P − S` phase: shared OPE and mixture | compiles; 5 axiom report(s), standard only |
  | `inventory_crossgroup` | gauge-group rescaling and cross-group transfer (finding 2.3) | compiles; 12 axiom report(s), standard only |
  | `labelope_orbit` | translation action on labels is neutralized (finding 2.6) | compiles; 4 axiom report(s), standard only |
  | `poincareW123_labels` | label representation facts | compiles; 3 axiom report(s), standard only |
  | `poincareW123_structure` | Poincaré action structure facts | compiles; 8 axiom report(s), standard only |
  | `rebaseline_jointchain` | verbatim re-run of the reduction chain | compiles; 11 axiom report(s), standard only |
  | `reconbridge_perphase` | per-character reconstruction (F1) blocks the anti-phase | compiles; 2 axiom report(s), standard only |
  | `reconbridge_zerojunk` | `boundary` on zero-label words (finding 2.4) | compiles; 2 axiom report(s), standard only |
  | `translationsW0_spectral` | translation and spectral conventions | compiles; 4 axiom report(s), standard only |
  | `w0_spectral` | W0 spectral-measure conventions | compiles; no axiom report |
  | `wilsonlimit_converges` | lattice clauses met without the lattice | compiles; 11 axiom report(s), standard only |

- **Trusted-surface inventory** (`AuditScripts/Inventory.lean`,
  `AuditScripts/Surface.lean`; output in `Audit/inventory.tsv`, `Audit/surface.txt`).
  The three trusted modules introduce:
  - 23 structures with 143 fields in total;
  - 57 top-level definitions;
  - 1 relevant instance.

  All of them are reachable from `JointExistence`.
- **Hashes.** `verification/challenge.sha256` matches the shipped challenge and Lake
  files. All 9,507 entries of `SOURCES.sha256` verify.
- **Static scan** of all 9,477 project `.lean` files:
  - 0 `axiom`, `native_decide`, `implemented_by`/`extern`, `unsafe`, `opaque` or `csimp`;
  - no kernel or debug options;
  - one `sorry` (the placeholder);
  - one custom elaborator (`vintage`), which goes through the kernel-checked
    `Lean.addDecl`.
- **`VerifyJoint.lean` design.** It checks type equality, equality of the public
  declarations, and the absence of project axioms, then kernel-replays the reachable
  declarations. The design is sound; its bundled log is for the old `PublicTheory` (2.1).

## 5. Reproducing

From a checkout of this branch with the pinned Mathlib cache (`lake exe cache get`):

```sh
lake build WilsonReference                  # the four challenge files
lake build Audit                            # BlindFamily and the reduction
lake env lean AuditScripts/Axioms.lean      # axioms of the main theorems
lake env lean AuditScripts/Inventory.lean   # writes Audit/inventory.tsv
lake env lean AuditScripts/Surface.lean     # writes Audit/surface.txt
lake env lean AuditScripts/Probes/<name>.lean
```

## 6. Open items

- **The generalized-free-field witness is not formalized.** The redundancy of the
  lattice clause is proved. That a non-Yang–Mills theory satisfies the remaining
  hypothesis is a paper argument.
- **One link in the rescaling probe is unchecked.** Its instantiation at the
  submission's `su2` depends on private lemmas in `YM/Examples/SU2.lean`, which the probe
  could not load.
- **Not reproduced.** The submitter's `VerifyJoint.lean` replay and the full solution
  build (9,457 modules).
