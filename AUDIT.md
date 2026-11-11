# Audit of the public challenge in `yang-mills-group/OpenAI-YM-20261028`

Scope: `Challenge.lean` and its trusted base `ChallengeSpec.lean`, `PublicWilson.lean`,
`PublicTheory.lean` (613 lines) on top of Mathlib `81a5d257`, Lean `v4.32.0`.
Repository state: single commit `3456e5e` (2026-11-05). Audit date: 2026-11-11.
Status: work in progress (see §6).

## Bottom line

1. **Mechanically the trusted surface is clean.**
   - The four files compile on the pinned toolchain and Mathlib.
   - They contain no axioms, no compile-time code (`#eval`, `run_cmd`, `initialize`), and
     no macros, notations or elaborators.
   - The only `sorry` is the intended placeholder.
   - The Mathlib definitions the statement relies on behave as intended (§4).
2. **The theorem does not tie the continuum theory to Yang–Mills or to the Wilson
   lattice.** The lattice clause can be met with insertions that never read the gauge
   field. This works because only the *selected* phase has to be a Wightman theory, so
   the other phases can absorb any difference. What remains is satisfiable, on paper, by
   a generalized free field. A Comparator pass on `YangMills.jointExistence` therefore
   certifies much less than "a Wightman QFT obtained as a scaling limit of Wilson lattice
   gauge theory". Any evidence for that stronger claim lives in the submission's internal
   definitions, not in this statement. See §1. A Lean formalization of the reduction is in
   `Audit/Reduction/`; its final theorem compiles, and the remaining lemma proofs are in
   progress (§6).
3. **The submitter's bundled verification logs are for a different `PublicTheory.lean`**
   (`3940e8dd…`) than the one shipped (`94111ad2…`). The group's own Comparator record of
   30 Oct used the shipped file. I rebuilt the four challenge files from the shipped
   sources, but did not replay the submitter's `VerifyJoint.lean` or the 9,457-module
   solution build.

## 1. Main finding: a solution with no Yang–Mills content

Let `T₀` be any single-phase package of continuum data:
- a Wightman theory;
- graded finite-dimensional field spaces `Field d`;
- Euclidean correlations `S` that give 0 to any word containing the zero field vector
  (true whenever correlations are linear in each field);
- a continuation, OPE channels and coefficients;
- `Reconstructed`, `OperatorProductExpansion` and `TraceTest` holding.

A generalized free field supplies `T₀` on paper. Take the scalar field `φ` with
Källén–Lehmann density `ρ(s) ∝ s²/log² s` at large `s`. Its derivatives and Wick monomials
are graded by engineering dimension, and the field is rescaled so the constant is
`3·dim 𝔤/π⁴`. Then:
- `S₂(r) ~ C/(r⁸ log²(1/r))`;
- Wick's theorem gives an all-orders OPE with finitely many monomials per grade;
- unique vacuum, positivity, locality and faithfulness are standard;
- the exclusion clause follows from the log² law alone. The submission's own
  `Wick.euclidean_excludes` uses only that law.

Given `T₀`, here is a proof of `JointExistence g` for any simple `g`. This is the
construction formalized in `Audit/Reduction/Defs.lean`.

**Wilson family (`blindFamily`).** Use periods `p+1`, denominators `N+2` and
`β_{N,p} = log(N+2) = log(1/a_N)`, so the slope is 1. Take `haar` to be the Haar
probability measure and `Token := Σ d, Field d`. The insertion is
`I_{N,p}(v, x; U) := 1` if `v = ⟨0, 0⟩` (the zero vector of grade 0), and `0` otherwise.
It is constant in `U`, so it is continuous, gauge invariant and local with an empty
stencil. That gives `WilsonRegularity`, proved in Lean: `Audit/Reduction/Regular.lean`,
and for constant insertions in general `Audit/BlindFamily.lean`.

**Hierarchy (`reduced T₀`).** Reuse `T₀`'s Hilbert space, fields, labels, continuation and
trace, and set `project := id`. Take two phases, realized as the subset `{0, 1}` of `ℝ`,
with the uniform measure and `selected := 0`. Let `P(a) := 1` if every tag of the word `a`
is `⟨0, 0⟩` (including the empty word), and `0` otherwise. Then set:
- `correlation (some 0) := S`
- `correlation none := P`
- `correlation (some 1) := 2P − S`

The channels are `T₀`'s channels plus one extra grade-0 channel. Its actor is the zero
vector and its coefficient is `P(a)`. `T₀`'s coefficient is set to 0 on any channel whose
actor is the zero vector.

**Why every clause holds:**
- `wilson`: finite moments are 0 or 1. The smeared sums are Riemann sums of `t`, so the
  limit is `∫ t · P` for every token word.
- `mixture`: `(S + (2P − S))/2 = P`. `characterContinuity`, `fullSupport` and
  `normalized` are immediate on a two-point discrete space. `P` is constant, so it is
  smooth and permutation-invariant.
- OPE in phase `S`: every new or zeroed term is a coefficient times `S` of a word
  containing the zero vector, which is 0. So `T₀`'s expansion is untouched.
- OPE in phase `P`: every `T₀` actor has `P`-value 0. The extra channel contributes exactly
  `P(a)P(b) = P(a ∪ b)`, so the remainder is 0.
- OPE in phase `2P − S`: its remainder is minus the `S` remainder. The new coefficient
  satisfies `|P(a)| ≤ 1 ≤ r^{−w−ε}`.
- The selected-phase clauses of `Reconstructed`, and all of `TraceTest`, are inherited
  from `T₀`. `TraceTest` is proved in Lean: `Audit/Reduction/Trace.lean`.

**Consequence.** `JointExistence` follows from the existence of `T₀`. `T₀` involves no
lattice measure and no gauge group, except the constant `3·dim 𝔤/π⁴`, which is a choice
of field normalization. In Lean this is
`YMAudit.jointExistence_of_continuum` (`Audit/Reduction/Main.lean`), stated directly in
terms of the trusted definitions. It compiles; the lemmas it uses are listed in §6.

**Mechanism.**
- `Hierarchy.Properties.wilson` (`ChallengeSpec.lean:178`) ties only the unselected
  average to the lattice.
- `Reconstructed` (`ChallengeSpec.lean:117`) requires a Wightman theory only for
  `T.selected`.
- `WilsonFamily.insertion` (`PublicWilson.lean:45`) is otherwise unconstrained.
- `correlation` (`ChallengeSpec.lean:41`) is not required to be multilinear.

The detailed theorem `YangMills.constructed` does prove a reconstruction for every
character (`Construction.lean:27`), but `JointExistence` does not ask for it.

**What would close it:**
1. Require `Reconstructed`, or at least reflection positivity plus multilinearity, for
   every character. A mixture of such phases cannot be the indicator `P`, and a
   product-form limit would force vanishing connected correlations, contradicting
   `TraceTest`.
2. Require `correlation` to be multilinear in field vectors.
3. Tie the tokens' insertions, at least the identity and the trace, to specified lattice
   observables (the group's assessment describes such polynomial representatives).

The group's `AcceptanceSpec.lean` (in `yang-mills-group/YM`) avoids this hole by
quantifying over the submission's own `YM.Family` and `Spec.Final`. The price is that
those internal definitions then need human review.

## 2. Other findings

| # | Severity | Location | Finding |
|---|---|---|---|
| 2.1 | High (evidence) | `verification/verified-sources.sha256`, `verification/joint-check.log:5` | The submitter's logged verification used `PublicTheory.lean` with SHA-256 `3940e8dd…`. The shipped file, `challenge.sha256`, `SOURCES.sha256` and the group's import all give `94111ad2…`. The other 19 verified files match. The `3940e8dd…` version is not public, so the change is unknown. The group's 30 Oct Comparator record ran on the shipped file. It ran in non-isolated macOS dev mode, and its recorded paths are under `/Users/oai/Documents/Codex/…`, so the independence of that run is worth confirming. |
| 2.2 | High | `ChallengeSpec.lean:168–175` | `TraceTest` is just the r⁸·log²(1/r) law for the selected Euclidean two-point function. `excludes` follows from `shortDistance`; the submission's own `Wick.euclidean_excludes` (`YM/TraceExtension/Wick/Refute.lean:75`) uses only that law. The constant `3·dim 𝔤/π⁴` is fixed by rescaling the field. `amplitudePositive` is a fact about `g` alone. Nothing ties `centeredTrace` to a stress tensor or a lattice observable. The README and assessment acknowledge that generalized free fields are not excluded. |
| 2.3 | Medium | `ChallengeSpec.lean:135–143` | The Euclidean↔Wightman bridge (`analytic`, `root`, `boundary`) uses a Bochner integral, which Lean sets to 0 on non-integrable integrands. `continuation` also carries no growth or spatial-regularity hypothesis. For words whose Wightman function is 0 (for example words containing a zero vector), the Euclidean data is pinned only if integrability holds. Combined with non-multilinear `correlation`, `TraceTest.centered` is automatic when `centeredTrace = 0`. I did not need or complete an exploit of this, but `boundary` should assert integrability or tempered growth. |
| 2.4 | Low | `PublicTheory.lean:225`, `:288–307` | `onLabels` may depend on the translation part of a Poincaré element, which allows "twisted" translation covariance. Standard W2 lets the label representation depend on Λ only. |
| 2.5 | Low | `ChallengeSpec.lean:13–14` | `running` accepts any positive slope (not 2b₀) and places no constraint on subleading terms. |
| 2.6 | Low | `ChallengeSpec.lean:117–143` | No Euclidean invariance, reflection positivity or clustering is required of the Euclidean data directly, and none at all of the non-selected phases. This is what enables §1. |
| 2.7 | Info | `ChallengeSpec.lean:186–188` | The hierarchy may depend on the subsequence, so there is no uniqueness of the limit. This is acknowledged in the README. |
| 2.8 | Info | `PublicTheory.lean:99` | The field named `module` is fine. In Lean 4.32 `module` is a header-only keyword and is not in the global token table; the shipped `PublicTheory.lean` compiles with it. |

## 3. What checks out

- **Gauge group.** `GaugeGroup` / `IsSimple` (`PublicTheory.lean:25–45`): the Lie algebra
  is pinned exactly by `exp`, and simplicity means nonabelian with no proper nonzero
  ideals. Both are correct and satisfiable (SU(2)). Disconnected groups and reducible
  faithful representations are allowed by design.
- **Lattice.** The periodic lattice, plaquette orientation, Wilson energy
  `1 − Re tr/(n+1)`, normalized law, finite moments and the `mesh^{4n}` Riemann-sum
  smearing over `(−P/2, P/2]` are all standard. `Converges` takes the full UV limit at
  fixed volume, then the IR limit along the subsequence. `volume` on `Points n` is
  Lebesgue (`measureSpaceOfInnerProductSpace`).
- **Wightman axioms.** W0–W3 are a reasonable rendering:
  - `charFun` uses `exp(+i⟨x,t⟩)`, so with the forward-cone condition `U(τe_t) = e^{iHτ}`
    with `H ≥ 0`. This is consistent with the covariance `f ↦ f(Λ⁻¹(x−a))` and with
    `orderedTube` having imaginary parts increasing along the word.
  - Temperedness is stated as strong continuity (stronger than usual).
  - The cyclic domain is exactly the polynomial domain.
  - Adjoint, locality and unique vacuum are present.
- **OPE.** The formalization is coherent, uniform in positions, spectators and phases,
  with shared coefficients.
- **Smoothness.** `∞` means C^∞ (`WithTop ℕ∞`), and `TestFunction … ⊤` is smooth with
  compact support.

## 4. Mechanical checks performed

- **Build.** `lake build WilsonReference` compiles `PublicTheory`, `PublicWilson`,
  `ChallengeSpec` and `Challenge` on Lean 4.32.0 with the pinned Mathlib. The only
  warning is the expected `sorry` in `Challenge.lean:5`.
- **Trusted-surface inventory** (`AuditScripts/Inventory.lean`,
  `AuditScripts/Surface.lean`; output in `Audit/inventory.tsv`, `Audit/surface.txt`).
  The three trusted modules introduce:
  - 23 structures with 143 fields in total (largest: `Hierarchy` 23 fields,
    `PoincareAction` 19, `Reconstructed` 15);
  - 57 top-level definitions;
  - 1 relevant instance (the Borel measurable structure on `g.image`).

  Every one of them is reachable from `JointExistence`. The only unreached items are
  auto-generated recursors and the `BorelSpace` instance.
- **Hashes.** `verification/challenge.sha256` matches the shipped challenge and Lake
  files. All 9,507 entries of `SOURCES.sha256` verify.
- **Static scan** of all 9,477 project `.lean` files (excluding packages):
  - 0 `axiom`, `native_decide`, `implemented_by`/`extern`, `unsafe`, `opaque` or `csimp`;
  - no kernel or debug options;
  - one `sorry` (`Challenge.lean:6`);
  - the five line-start `admit` hits are field names or comments, not the tactic.
  - One custom elaborator, `vintage` (`YM/UVExtension/Orchard/Barrel.lean`), adds
    declarations through the kernel-checked `Lean.addDecl` and refuses unsafe ones.
- **`VerifyJoint.lean` design.** It checks:
  - equality of the challenge and solution theorem types;
  - byte-for-byte equality, in both type and value, of every reachable public
    declaration against the reference;
  - no project axioms and no unsafe or partial definitions.
  It then kernel-replays the reachable project declarations on a Mathlib-only base. The
  design is sound; its bundled log is for the old `PublicTheory` (2.1).
- **Mathlib semantics**, checked with Lean snippets on the pinned toolchain and Mathlib:
  `charFun`, `NormedSpace.exp`, `∞`, `TestFunction`, the measure on `Points n`, and
  `integral_undef`.

## 5. Reproducing

From a checkout of this branch with the pinned Mathlib cache (`lake exe cache get`):

```sh
lake build WilsonReference          # the four challenge files
lake build Audit                    # audit library: BlindFamily and Reduction
lake env lean AuditScripts/Inventory.lean
lake env lean AuditScripts/Surface.lean
```

`lake build Audit.Reduction.Main` reports which lemma files still contain `sorry`.

## 6. Status and open items

- **Formal reduction (`Audit/Reduction/`).** The shared definitions (`Defs.lean`), the
  regularity and trace lemmas (`Regular.lean`, `Trace.lean`) and the assembly
  (`Main.lean`: `wilson_clause_redundant`, `jointExistence_of_continuum`) compile. Eight
  `sorry`s remain, in six files:
  - `Haar.lean`: Haar probability measure on `g.image`;
  - `Law.lean`: the Wilson law is a probability measure;
  - `Riemann.lean`: lattice Riemann sums converge;
  - `Converges.lean`: the gauge-blind family converges;
  - `Recon.lean`: the `Reconstructed` clauses;
  - `OPE.lean`: the OPE clauses.

  Proofs for these are being written; this file will be updated when they land.
- **Definition-by-definition audit.** An item-by-item review of all ~200 trusted items,
  with adversarial checks on each finding, is in progress.
- **Not reproduced.** The submitter's `VerifyJoint.lean` replay and the full solution
  build (9,457 modules).
