# Trusted-definition audit of `YangMills.JointExistence`

Repository yang-mills-group/OpenAI-YM-20261028, Lean v4.32.0, Mathlib rev 81a5d257. Target: `JointExistence` (ChallengeSpec.lean:186-188).

Abbreviations: PT = PublicTheory.lean, PW = PublicWilson.lean, CS = ChallengeSpec.lean, RM = README.md.
- Probe files cited below are in `AuditScripts/Probes/`; their compile status is recorded in `AUDIT.md` §4. Log names (`*.log`) refer to the audit agents' run logs, which are not included.
- The three trusted files match `verification/challenge.sha256`. No repository file was modified for this report.

## 0. Bottom line

- **Coverage.** 173 items, as the reviewers enumerated them (some items bundle several structure fields). Final verdicts: 91 faithful, 64 caveat, 7 deviation, 8 loophole, 3 pitfall. Final severities: 8 critical (all one defect, D1), 1 high, 10 medium, 49 low, 105 info.
- **Findings.** 31 findings: 30 confirmed, 1 contested (`Reconstructed.boundary`), 0 rejected.
- **On the concern that the trusted files introduce a lot of definitions.** It is justified. 98 items carry real content; most of these are faithful Wightman, OPE and reconstruction definitions. The other 74 add no independent requirement:
  - 29 are redundant: aliases, data pinned by other fields, or clauses implied by other clauses. Some of these are argued rather than machine-checked; the table says which.
  - 38 are inert: the D1 construction discharges them once the continuum clauses hold. This is machine-checked. They are the whole lattice layer, `WilsonRegularity`, `Properties.wilson`, and the non-selected phase layer.
  - 7 make up the gauge-group layer and matter only through `dim g`. That number can itself be rescaled away (D3, machine-checked).
- **D1 (critical, kernel-checked).** `JointExistence` follows from `∀ g simple, ∃ C₀ T₀, Reconstructed ∧ OperatorProductExpansion ∧ TraceTest ∧ ZeroInvisible T₀`. The Wilson measure, plaquette action, β and Haar measure never enter. RM:11 ("Wilson origin") is not enforced.
- **D2 (high).** The "non-freeness" test is passed by a generalized free field (GFF). This is a paper argument, and RM:26 concedes the scope. Together with D1, a proof of `JointExistence` would certify no Yang–Mills content.
- **Recommended repair (F1).** Require a Wightman reconstruction for every character, not only the selected one. The detailed theorem already proves this (RM:20).

## 1. Coverage table

Legend:
- **Verdict:** faithful; caveat (correct, but a convention or scope note); deviation (differs from the intended or standard meaning); pitfall (a junk-value or Lean-semantics trap); loophole (lets `JointExistence` be met without the intended content).
- **Rating rule.** Items without a finding were rated at most caveat/low by both reviewers; the table gives the more cautious of the two ratings. For findings, the status comes from the skeptic votes: confirmed if a majority upheld, contested if the votes split evenly, rejected if a majority refuted. The final rating applies the skeptics' severity corrections and the follow-up settlements. `[x]` gives the reviewers' original rating where the final rating differs.
- **Role:** content; redundant (alias, pinned data, or implied clause); inert (discharged by the fixed D1 construction from the selected-phase data, so it adds nothing beyond `ZeroInvisible`); dim-only (affects the statement only through `finrank ℝ g.lieAlgebra`).
- **Finding:** `conf k/n` = confirmed by k of n skeptics; `contested 1-1`; `—` = no finding raised.

### PublicTheory.lean

#### gauge (PT:16-47)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| UnitaryRepresentation | caveat | info | dim-only | — | PT:20 is U(n+1) with the standard group law and product topology. Despite the name it is the ambient group, not a representation. |
| GaugeGroup.n | caveat | info | dim-only | — | PT:26 matrices are (n+1)×(n+1), so SU(N) has n = N−1. No ℕ-subtraction or zero denominator. |
| GaugeGroup.image | caveat | low | dim-only | — | PT:27 any subgroup in any faithful representation; disconnected and reducible cases are allowed. This only strengthens the claim. |
| GaugeGroup.imageClosed | faithful | info | dim-only | — | PT:28 closed implies compact, so the Haar probability of PW:41-43 exists. Its only role is to make `WilsonFamily g` nonempty. |
| GaugeGroup.lieAlgebra | faithful | info | dim-only | — | PT:29 uniquely fixed by `generates`; finrank ℝ = dim G. |
| GaugeGroup.generates | faithful | info | dim-only | — | PT:30-33 L(G) = {X : exp(tX) ∈ G for all real t}, with the genuine matrix exponential (probe: the ℚ-algebra branch is taken). |
| GaugeGroup.IsSimple | caveat | low | dim-only | — | PT:39-45 a simple real Lie algebra, broad class. Only the first conjunct (dim ≥ 1) is ever used. |

#### kinematics (PT:49-74)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| Axis | faithful | info | content | — | PT:51 `Fin 4`; it also indexes the lattice directions. |
| SpaceAxis | faithful | info | content | — | PT:52 `Fin 3`, embedded as {0,1,2} by `castSucc`. |
| timeAxis | caveat | info | content | — | PT:53 time is the last coordinate (index 3), used consistently in all three files. |
| Spacetime | caveat | low | content | — | PT:54 one Euclidean ℝ⁴ serves as Minkowski, momentum and Euclidean space. The spectral pairing is Euclidean, which is equivalent to the standard one under p⃗ ↦ −p⃗. |
| Space | faithful | info | content | — | PT:55 ℝ³ with L² norm and Lebesgue measure. |
| time | faithful | info | content | — | PT:57 last coordinate; continuous and linear. |
| spatial | faithful | info | content | — | PT:59-60 the first three coordinates as an L² vector. |
| forwardCone | faithful | info | content | — | PT:64 closed cone ‖x⃗‖ ≤ t. Closedness is required: an open cone would make W0 unsatisfiable. |
| minkowskiSquare | faithful | info | content | — | PT:66 t² − ‖x⃗‖², signature (+,−,−,−), time last. |
| spacelike | faithful | info | content | — | PT:68 the open set {m < 0}; excludes 0 and null vectors, so locality is not vacuous. |
| TestFunction | faithful | info | content | — | PT:70 Schwartz space 𝒮(ℝ⁴,ℂ). It shadows Mathlib's `_root_.TestFunction` (𝒟), which PW:73 uses on purpose. |
| conjugateTest | faithful | info | content | — | PT:73-74 pointwise conjugation with no reflection; correct for φ(f)* ⊇ φ†(f̄). |

#### fields (PT:76-163)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| HilbertSpace (4 fields) | caveat | info | content | — | PT:79-83 no separability field. Harmless: H is separable inside the challenge. |
| HilbertSpace.Operator | faithful | info | content | — | PT:91 bounded ℂ-linear operators; not used for the unbounded fields. |
| FieldLabels (3 fields) | caveat | low | content | — | PT:96-99 a bare ℂ-vector space, possibly infinite-dimensional. CS:31 and CS:122 force countable dimension. |
| FieldSystem.domain | caveat | info | content | — | PT:106 field-invariant by its type. With PT:130 it must equal D₀; this normalization loses nothing. |
| FieldSystem.vacuum | faithful | info | content | — | PT:107 Ω ∈ D. Its meaning comes from PT:128, 276-278 and 297-299. |
| FieldSystem.field | faithful | info | content | — | PT:108-109 bilinear in (label, test), with values in End(D). c-number fields are admitted, as in Streater–Wightman. |
| FieldSystem.vector | faithful | info | content | — | PT:115-118 the head of the list is the leftmost operator (rfl probe). |
| FieldSystem.vacuumExpectation | faithful | info | content | — | PT:121-124 ⟨Ω, φ(a₀)⋯φ(a_{n−1})Ω⟩; the ordering matches orderedTube (CS:95-96). |
| DomainAxioms.normalizedVacuum | faithful | info | content | — | PT:128 ‖Ω‖ = 1, which excludes H = 0. |
| DomainAxioms.denseDomain | faithful | info | content | — | PT:129 D is norm-dense. |
| DomainAxioms.cyclicVacuum | caveat | info | content | — | PT:130-131 D equals the span of field words: a stronger but lossless form of cyclicity. |
| DomainAxioms.tempered | caveat | info | content | — | PT:132-133 vector-valued continuity; equivalent to weak temperedness given PT:136-141. |
| FieldSystem.AdjointAxiom | faithful | info | content | — | PT:136-141 φ(ℓ,f)* ⊇ φ(ℓ†,f̄) on D. That ℓ ↦ ℓ† is an involution is derivable (Lean). |
| FieldSystem.SpacelikeSeparated | caveat | info | content | — | PT:145-146 closed supports with strict separation; an equivalent formulation. |
| FieldSystem.LocalCommutativity | caveat | low | content | — | PT:149-156 commutators only (bosonic). Stronger than general W3; suits gauge-invariant observables. |
| FieldSystem.Faithful | caveat | low | content | — | PT:159-161 injectivity of ℓ ↦ φ(ℓ,·). Not a Wightman axiom, and c-number fields satisfy it. |

#### spectrum (PT:165-206, 268-278)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| TranslationAction.operator | faithful | info | redundant | — | PT:170 pinned to the Poincaré translations by PT:261-262. |
| TranslationAction.identity | faithful | info | redundant | — | PT:171 derivable (proved, AuditScripts/Probes/w0_spectral.lean:216). |
| TranslationAction.add | faithful | info | redundant | — | PT:172-173 an exact representation; follows from the PoincareAction fields (argued). |
| TranslationAction.unitary | faithful | info | redundant | — | PT:174-175 isometry plus `add` gives unitarity; follows from PT:231-232 (argued). |
| TranslationAction.stronglyContinuous | faithful | info | redundant | — | PT:176-177 standard; follows from PT:233-234 (argued). |
| EnergyMomentumMeasure.projection | pitfall | info | redundant | conf 2/2 | PT:181 defined on every set; values on non-Borel sets are junk but never read (the only external use, PT:275, is at a Borel set). Borel values are fixed by U (AuditScripts/Probes/translationsW0_spectral.lean:69-86). |
| EnergyMomentumMeasure.empty | faithful | info | redundant | — | PT:182 follows by polarization (argued). |
| EnergyMomentumMeasure.univ | faithful | info | redundant | — | PT:183 implied by PT:271-273 at a = 0 (argued). |
| EnergyMomentumMeasure.intersection | faithful | info | redundant | — | PT:184-186 standard; redundant modulo the SNAG theorem, which is not in Mathlib (argued). |
| EnergyMomentumMeasure.selfAdjoint | faithful | info | redundant | — | PT:187-189 derivable (proved, w0_spectral.lean:205). |
| EnergyMomentumMeasure.countablyAdditive | faithful | info | redundant | — | PT:190-194 strong σ-additivity; redundant modulo SNAG (argued). |
| EnergyMomentumMeasure.diagonal | faithful | info | redundant | — | PT:195 pinned by PT:197-200 on Borel sets (probe_diagonal_unique). |
| EnergyMomentumMeasure.finite | faithful | info | content | — | PT:196 blocks the toReal ∞ = 0 junk value and makes charFun integrable. |
| EnergyMomentumMeasure.diagonalIdentity | faithful | info | content | — | PT:197-200 μ_ψ(B) = ⟨ψ,E(B)ψ⟩; ties the measure to U. |
| W0.spectralRepresentation | caveat | low | content | — | PT:271-273 E is the SNAG measure of U with the Euclidean pairing. The binder named `momentum` is really the translation. |
| W0.positiveEnergy | faithful | info | content | — | PT:274-275 the full spectrum condition (closed cone), stronger than H ≥ 0. |
| W0.uniqueVacuum | caveat | info | content | — | PT:276-278 translation-invariant vectors lie in ℂΩ. Ω's own invariance comes from W2. |

#### poincare (PT:208-319)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| ProperLorentz | faithful | info | content | — | PT:209-212 exactly SO⁺(1,3); the cone clause alone excludes PT. Not the spin cover. |
| PoincareCoordinates | faithful | info | content | — | PT:215 product topology, with no group law of its own. |
| PoincareAction.Symmetry, one, mul, topology | caveat | low | content | — | PT:220-223 free data, but PT:235-239 force it to be isomorphic to P₊↑ (not ISL(2,ℂ)). |
| PoincareAction.onStates | caveat | low | content | — | PT:224 with PT:228-234, a strongly continuous unitary representation of P₊↑. Integer spin only. |
| PoincareAction.onLabels | deviation | low [medium] | content | conf 2/2 | PT:225 translations may act on labels, with no continuity or finiteness condition. Neutralized inside JointExistence (follow-up 6). |
| PoincareAction.onTests | faithful | info | redundant | — | PT:226 pinned by PT:242-243. |
| PoincareAction.pureTranslation | faithful | info | redundant | — | PT:227 pinned to coordinates.symm(1,x) by PT:240-241. |
| PoincareAction.identity | faithful | info | redundant | — | PT:228 follows from composition plus injectivity of an isometry (argued). |
| PoincareAction.composition | faithful | info | content | — | PT:229-230 an exact homomorphism. |
| PoincareAction.unitary | faithful | info | content | — | PT:231-232 isometry; surjective by the group law, hence unitary. |
| PoincareAction.stronglyContinuous | faithful | info | content | — | PT:233-234 standard strong continuity. |
| PoincareAction.coordinates | faithful | info | content | — | PT:235 a homeomorphism onto all of L₊↑ × ℝ⁴. |
| PoincareAction.identityCoordinates | faithful | info | content | — | PT:236 needed because `One` is otherwise arbitrary. |
| PoincareAction.productCoordinates | faithful | info | content | — | PT:237-239 the semidirect law, i.e. composition of affine maps. |
| PoincareAction.translationCoordinates | faithful | info | content | — | PT:240-241 pins pureTranslation. |
| PoincareAction.pullback | faithful | info | content | — | PT:242-243 f(Λ⁻¹(x−a)), the Streater–Wightman convention. |
| PoincareAction.translationZero | faithful | info | redundant | — | PT:244 proved (AuditScripts/Probes/poincareW123_structure.lean:171-184). |
| PoincareAction.translationAdd | faithful | info | redundant | — | PT:245-246 proved (same probe). |
| WightmanTheory (fields, adjointLabel, translations, energyMomentum, poincare) | caveat | low | content | — | PT:255-260 a data bundle; the separate translation and spectral data are tied in only by PT:261-262 and W0. |
| WightmanTheory.translationCompatibility | faithful | info | content | — | PT:261-262 makes W0 a statement about the Poincaré translations; signs are consistent. |
| W1.domain | caveat | low | content | — | PT:283 packages DomainAxioms, with cyclicity in the strong form. |
| W1.adjoint | faithful | info | content | — | PT:284 standard hermiticity on D. |
| W2.labelIdentity | faithful | info | redundant | — | PT:288-289 derivable given Faithful (argued). |
| W2.labelComposition | caveat | low | redundant | — | PT:290-293 a homomorphism on the whole affine group, not just the Lorentz part. Derivable given Faithful (argued). |
| W2.domainInvariant | faithful | info | content | — | PT:294-296 standard. |
| W2.vacuumInvariant | faithful | info | content | — | PT:297-299 U(g)Ω = Ω for every g. |
| W2.fieldCovariance | deviation | low [medium] | content | conf 2/2 | PT:300-307 the Streater–Wightman law with S(Λ⁻¹) replaced by an arbitrary label representation of all of P₊↑. Neutralized inside JointExistence (follow-up 6). |
| W3.locality | caveat | low | content | — | PT:311 commutators only (bosonic). |
| WightmanTheory.Axioms | caveat | low | content | — | PT:315-319 W0 ∧ W1 ∧ W2 ∧ W3. Admits the trivial c-number theory, so non-triviality has to come from CS. |

### PublicWilson.lean

#### kinematics

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| Points | faithful | info | content | — | PW:10 (ℝ⁴)ⁿ with L² structure. Its volume is Lebesgue measure on ℝ^{4n}, and Points 0 has unit mass (probe). |

#### lattice (PW:11-57)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| Site | faithful | info | inert | — | PW:11 (ℤ/l)⁴ with l : ℕ+, so the ZMod 0 = ℤ junk case cannot occur. |
| Configuration | faithful | info | inert | — | PW:12 one group element per positive link, with the product Borel σ-algebra. |
| Directions | faithful | info | inert | — | PW:13 the six planes i < j. |
| MeasurableSpace instance on g.image | faithful | info | inert | — | PW:16 Borel σ-algebra of the subspace topology; there is no competing instance. |
| BorelSpace instance on g.image | faithful | info | inert | — | PW:17 an honest ⟨rfl⟩ witness, which Haar uniqueness needs. |
| plaquette | faithful | info | inert | — | PW:20-23 the standard ordered product U·U·U⁻¹·U⁻¹. |
| wilsonEnergy | caveat | low | inert | — | PW:25-27 the Wilson action Σ(1 − Re tr/(n+1)) in whatever representation the GaugeGroup carries. |
| wilsonLaw | faithful | info | inert | — | PW:29-33 Z⁻¹e^{−βS} times product Haar measure; a probability measure for every β (probe), so the normalizer has no junk branch. |
| WilsonFamily.period | caveat | low | inert | — | PW:36 integer box sides chosen by the prover. |
| WilsonFamily.denominator | caveat | low | inert | — | PW:37 a prover-chosen, possibly sparse spacing sequence; no universality over spacings. |
| WilsonFamily.periodStrict | faithful | info | inert | — | PW:38 forces L_p ≥ p+1. |
| WilsonFamily.denominatorStrict | faithful | info | inert | — | PW:39 forces mesh → 0. |
| WilsonFamily.beta | caveat | low [deviation, medium] | inert | conf 2/2 | PW:40 a free function of (N,p); its only constraint is CS:13-14, which is what RM:11 promises. Same issue as `running`. |
| WilsonFamily.haar | faithful | info | inert | — | PW:41 with PW:42-43, forced to be the unique Haar probability measure. |
| WilsonFamily.probability | faithful | info | inert | — | PW:42 the normalization. |
| WilsonFamily.invariantHaar | faithful | info | inert | — | PW:43 left Haar measure on a compact group. |
| WilsonFamily.Token | caveat | low [loophole, high] | inert | conf 3/3 | PW:44 a bare Type. It contributes to D1 only together with a free `insertion` (follow-up 1). |
| WilsonFamily.insertion | loophole | critical | inert | conf 3/3 | PW:45-46 an arbitrary function of (N, p, token, site, U). Link-blind insertions satisfy CS:12-22. Root cause A of D1. |
| WilsonFamily.mesh | faithful | info | inert | — | PW:50 1/D_N, with D_N ≥ 1. |
| WilsonFamily.place | faithful | info | inert | — | PW:51-52 injective onto the half-open centred box. |
| WilsonFamily.finiteMoment | faithful | low [caveat, medium] | inert | conf 2/2 | PW:54-57 an honest Wilson expectation, integrable because of CS:15. It loses its content only through `insertion` (follow-up 1). |

#### limit (PW:59-90)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| WilsonFamily.separated | faithful | info | content | — | PW:59-71 the open set of pairwise-distinct configurations; used by CS:126-134. |
| WilsonFamily.SeparatedTest | faithful | info | inert | — | PW:73 Mathlib's 𝒟(separated n, ℂ), C^∞ (⊤ : ℕ∞, not analytic). |
| WilsonFamily.suitable | faithful | info | inert | — | PW:75-77 support inside the open box; eventually true along any volume order. |
| WilsonFamily.smear | caveat | low | inert | — | PW:79-81 Riemann sum normalized to Lebesgue measure; no renormalization factors. |
| WilsonFamily.Converges | caveat | low [loophole, critical] | inert | conf 3/3 | PW:85-90 an honest iterated limit. Its critical consequence is recorded under D1 (follow-up 1). There is no junk-integral path, because of CS:129-130. |

### ChallengeSpec.lean

#### limit: WilsonRegularity (CS:11-22)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| WilsonRegularity.running | caveat | low [deviation, medium] | inert | conf 2/2 | CS:13-14 some positive slope, uniform in p. It is not the asymptotic-freedom value, but RM:11 promises only a positive slope. The exploit does not use this clause. |
| WilsonRegularity.continuous | faithful | info | inert | — | CS:15 rules out Bochner junk in PW:56. |
| WilsonRegularity.invariant | faithful | info | inert | — | CS:16-18 lattice gauge invariance, with orientation matching PW:20-23. |
| WilsonRegularity.localSupport | faithful | info [loophole, high] | inert | conf 3/3 | CS:19-22 an empty stencil is allowed, but constant insertions satisfy every stencil, so this clause is not a cause of D1 (follow-up 1). |

#### hierarchy (CS:24-80)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| Hierarchy.H | caveat | low | content | — | CS:25 any Hilbert space; it gets content only through Reconstructed and TraceTest. |
| Hierarchy.labels | caveat | low | content | — | CS:26 a bare label space that must be a directed union of the grade images. |
| Hierarchy.theory | deviation | critical (D1) [high] | content | conf 3/3 | CS:27 one Wightman theory, tied by CS:137-138 to the selected character only. RM:20 says the detailed theorem has one per character. Carrier of D1 cause B. |
| Hierarchy.Field (fieldAdd, fieldSpace, fieldFinite) | caveat | medium | content | conf 2/2 | CS:28-31 graded finite-dimensional spaces. The grade is a filtration level chosen by the prover, and the norm is never used. |
| Hierarchy.toLabel | caveat | low | content | — | CS:32 linear in each grade; no compatibility required between grades. |
| Hierarchy.project | caveat | low [loophole, medium] | inert | conf 3/3 | CS:33 an arbitrary map Token → Tag; `id` works (follow-up 1). |
| Hierarchy.Character (+4 instances) | loophole | critical (D1) | inert | conf 3/3 | CS:34-38 any compact metric space; non-selected characters need not be states. Carrier of D1 cause B. |
| Hierarchy.phaseMeasure | loophole | critical (D1) [medium] | inert | conf 3/3 | CS:39 only a full-support probability measure, not an extremal decomposition. Carrier of D1 cause B. |
| Hierarchy.selected | caveat | medium | content | conf 2/2 | CS:40 the only character tied to theory, continuation and TraceTest; its only link to the lattice is CS:133-134. |
| Hierarchy.correlation | pitfall | medium [loophole, critical] | content | conf 3/3 | CS:41 an arbitrary function, not multilinear, possibly nonzero on zero vectors. D1 cause C, needed only in combination with A and B (follow-up 1). |
| Hierarchy.continuation | caveat | low | content | — | CS:42 selected phase only; holomorphic in the times only, with no growth bound; fixed by `root`. |
| Hierarchy.Channel (finiteChannels) | caveat | low | content | — | CS:43-44 finite in each grade; channels can be added freely. |
| Hierarchy.actor | caveat | medium | content | conf 2/2 | CS:45 actors may be zero or dependent; a zero grade-0 actor is the extra channel used by D1. |
| Hierarchy.coefficient | deviation | medium | content | conf 2/2 | CS:46-47 not multilinear, covariant or measurable. Correctly independent of spectators, phase and degree. |
| Hierarchy.centeredTrace | deviation | medium | content | conf 2/2 | CS:48 just a vector of Field 4. It is not identified with the stress trace (RM:14), and its normalization is free. |
| Hierarchy.Tag | faithful | info | content | — | CS:55 Σ d, Field d. |
| Hierarchy.grouped | faithful | info | content | — | CS:58-61 the enumeration uses choice, which is harmless given CS:126-128. |
| Hierarchy.weight | caveat | low | content | — | CS:63 the sum of grade indices, not of true dimensions. |
| Hierarchy.Within | faithful | info | content | — | CS:65-66 the standard single-scale cluster shape. |
| Hierarchy.Clear | caveat | low | content | — | CS:67-68 no upper bound on spectator distance, so stronger than the compact-set version. |
| OperatorProductExpansion.coefficients | caveat | low | content | — | CS:71-73 ‖C‖ ≤ r^{j−w−ε}, uniformly; the ε absorbs logarithms. |
| OperatorProductExpansion.remainder | caveat | medium | content | conf 2/2 | CS:74-80 a faithful, uniform all-orders estimate in every phase, but generic (a GFF satisfies it) and blind to compensating phases. |

#### kinematics: aliases (CS:82-92)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| Hierarchy.OPEPoint | caveat | info | redundant | — | CS:83 reducibly equal to Spacetime (rfl). Its docstring "used by the OPE estimates" is inaccurate. |
| Hierarchy.OPEPoints | faithful | info | redundant | — | CS:86 reducibly equal to Points n (rfl). |
| Hierarchy.OPEComplexTimes | caveat | low | redundant | — | CS:89 Fin n → ℂ: only the times are complexified (time-slice holomorphy). |
| Hierarchy.OPESpacePoints | caveat | low | redundant | — | CS:92 real spatial points, with no regularity required in them. |

#### reconstruction (CS:94-143)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| Hierarchy.orderedTube | caveat | info | content | — | CS:95-96 the real-spatial slice of the forward tube; orientation consistent with W0/W2. |
| Hierarchy.complexShift | caveat | info | content | — | CS:99-102 radial approach in the times only; lands in the tube. |
| Hierarchy.imaginaryTimes | faithful | info | content | — | CS:105-106 z = iτ: the Osterwalder–Schrader identification. |
| Hierarchy.spatialPoints | faithful | info | content | — | CS:109-110 uses PT:59-60. |
| Hierarchy.tensorTest | faithful | info | content | — | CS:113-115 the product test; equals 1 at n = 0. |
| Reconstructed.axioms | caveat | low | content | — | CS:118 W0-W3 for the selected theory only; admits c-number theories. |
| Reconstructed.faithful | caveat | low | content | — | CS:119 a non-redundancy condition; allows c-number fields. |
| Reconstructed.injective | caveat | low | content | — | CS:120 per grade only, so the same field may sit in every grade. |
| Reconstructed.acts | caveat | low | content | — | CS:121 given faithful and covers, it only says labels ≠ 0. |
| Reconstructed.covers | deviation | low | content | conf 2/2 | CS:122 each label lies in one grade image, which forces a cumulative (filtration) grading. |
| Reconstructed.represents | caveat | low [medium] | inert | conf 2/2 | CS:123 surjectivity of an arbitrary map; `id` satisfies it. |
| Reconstructed.normalized | faithful | info | inert | — | CS:124 a probability measure. |
| Reconstructed.fullSupport | caveat | low | inert | — | CS:125 blocks zero-weight phantom phases, but not compensating phases. |
| Reconstructed.permutation | faithful | info | content | — | CS:126-128 bosonic symmetry on separated configurations, in every phase. |
| Reconstructed.smooth | caveat | info | content | — | CS:129-130 C^∞ (not analytic) on the separated set. It is also what keeps the PW:90 integral honest. |
| Reconstructed.characterContinuity | caveat | low | inert | — | CS:131-132 vacuous when the character space is finite. |
| Reconstructed.mixture | loophole | critical | inert | conf 3/3 | CS:133-134 the average does not tie the selected phase to the Wilson slot; an anti-phase 2W − S absorbs any difference (Lean). Root cause B of D1. |
| Reconstructed.analytic | caveat | low | content | — | CS:135-136 time holomorphy for each fixed spatial configuration; no growth bound. |
| Reconstructed.root | faithful | info | content | — | CS:137-138 the OS relation in the correct orientation, for the selected phase only. |
| Reconstructed.boundary | pitfall | medium | content | contested 1-1 | CS:139-143 Bochner junk lets zero-label words with n ≥ 2 escape; n = 1 is rigid (follow-up 3). |

#### trace (CS:145-188)

| Item | Verdict | Sev. | Role | Finding | Justification |
|---|---|---|---|---|---|
| Hierarchy.timePair | faithful | info | content | — | CS:146-148 the points (0,0,0,∓r/2): separated and ordered for r > 0. |
| Hierarchy.traceTwo | caveat | low | content | — | CS:149 the selected-phase Euclidean 2-point function of ⟨4, centeredTrace⟩, tied to the Wightman data only through CS:135-143. |
| Mode (6 fields) | caveat | info | redundant | — | CS:152-158 broader than polynomial numerators. Logically idle, because `excludes` follows from `shortDistance` (argued). |
| Mode.kernel | faithful | info | redundant | — | CS:159-161 the mass-shell integrand; its only junk value is at E = 0, a null set. |
| Track | faithful | info | redundant | — | CS:162-164 a finite product of propagators. |
| wickProfile | faithful | info | redundant | — | CS:165-166 finite combinations, which expand as r^a (log r)^b with b ≥ 0. |
| TraceTest.centered | caveat | low | content | — | CS:169-171 ⟨Ω,Θ(f)Ω⟩ = 0. It holds automatically when centeredTrace = 0 (AuditScripts/Probes/poincareW123_labels.lean:129-136); see `boundary`. |
| TraceTest.amplitudePositive | caveat | low | redundant | — | CS:172 mentions no hierarchy data and follows from IsSimple (Lean, amplitude_pos). |
| TraceTest.shortDistance | loophole | medium [caveat] | content | conf 2/2 | CS:173-174 the correct one-loop constant, but the field's normalization is free: any nonzero complex constant can be rescaled to 3·dim g/π⁴ (follow-up 4, Lean). |
| TraceTest.excludes | caveat | low | redundant | — | CS:175 follows from shortDistance and amplitudePositive (argued, not machine-checked). |
| Properties.wilson | loophole | critical | inert | conf 3/3 | CS:178 reads only `correlation none` and is met by a gauge-blind family. A consequence of D1. |
| Properties.reconstruction | loophole | critical (D1) [high] | content | conf 3/3 | CS:179 reconstructs the selected character only. No defect separate from `mixture`. |
| Properties.ope | caveat | medium | content | conf 2/2 | CS:180 one coefficient system in every phase; generic, and it does not block D1. |
| Properties.nonfree | deviation | high | content | conf 3/3 | CS:181 for simple g it is equivalent to centered ∧ shortDistance; a GFF passes (RM:26; follow-up 2). |
| JointExistence | loophole | critical | statement | conf 3/3 | CS:186-188 the quantifier order matches RM:9, but the statement is implied by the continuum clauses plus ZeroInvisible (D1, Lean). |

## 2. Confirmed findings, by final severity

### 2.1 Critical

**D1. The lattice clause is inert (kernel-checked).**

*Items.*
- Root cause A: `WilsonFamily.insertion` (PW:45-46).
- Root cause B: `Reconstructed.mixture` (CS:133-134). Its carriers are `Hierarchy.theory` (CS:27), `Hierarchy.Character` (CS:34-38), `Hierarchy.phaseMeasure` (CS:39) and `Properties.reconstruction` (CS:179).
- Cause C: `Hierarchy.correlation` (CS:41), which is medium on its own.
- Consequences: `Properties.wilson` (CS:178) and `JointExistence` (CS:186-188).

*What is wrong.*
- **A.** Insertions are data the prover chooses. Link-blind insertions satisfy every clause of `WilsonRegularity` (CS:15-22), for any stencil. Every finite moment is then a product of constants, whatever β, the Haar measure and the plaquette action are, and `Converges` (PW:85-90) reduces to Riemann sums.
- **B.** `Properties.wilson` reads only `correlation none`. Only the selected phase carries the Wightman theory, `root`/`boundary` (CS:137-143) and `traceTwo` (CS:149). The sole link between them is the average in `mixture`, over a character space the prover chooses. A second character with correlations 2·W − S makes that average equal to any lattice limit W.
- **C.** `correlation` and `coefficient` need not be multilinear. So W can be `allZero`, which equals 1 on the all-zero-tag word. One extra grade-0 channel, with a zero actor and coefficient `allZero a`, then satisfies the shared OPE, which ranges over every phase including `none` (CS:74-80). A ZeroInvisible selected phase cannot see that channel.

*Evidence.*
- `YMAudit.jointExistence_of_continuum` (Audit/Reduction/Main.lean:38-44) was re-run verbatim in AuditScripts/Probes/rebaseline_jointchain.lean: EXIT 0, axioms propext, Classical.choice and Quot.sound only (`rebaseline_jointchain_run1.log`).
- Statement proved: `(∀ g, g.IsSimple → ∃ C₀ T₀, T₀.Reconstructed ∧ T₀.OperatorProductExpansion ∧ T₀.TraceTest ∧ ZeroInvisible T₀) → JointExistence`.
- Witness: C = `blindFamily` (Audit/Reduction/Defs.lean:30-41), q = id, and T = `reduced T₀` (Defs.lean:89-105), which does not depend on p.
- Pieces also checked independently:
  - `lattice_clauses_without_lattice` (AuditScripts/Probes/wilsonlimit_converges.lean:378);
  - `antiPhase_ope` and `antiPhase_mixture` (AuditScripts/Probes/hierope_antiphase.lean);
  - `decouple_reconstructed` (AuditScripts/Probes/bridge_decouple.lean:156).

*Why it matters for JointExistence.*
- JointExistence lies between "every simple g has a continuum hierarchy with Reconstructed, OPE and TraceTest" and the same statement with ZeroInvisible added. The lower bound is trivial; the upper bound is the theorem above.
- ZeroInvisible holds in every multilinear model. It is not derivable from Reconstructed for n ≥ 2 (follow-up 3).
- So none of these can change what has to be proved: the lattice measure, the plaquette action, β, the Haar measure, finiteMoment, smear, Converges, WilsonRegularity, and the non-selected phase layer.
- RM:11 ("Wilson origin") is not enforced. The gauge group enters only through dim g (CS:172-174), and D3 shows even that can be rescaled away.

*Fix.*
- **F1 (recommended; blocks the reduction).** Require every character to be reconstructed. For each `i : Character`, require a Wightman theory satisfying Axioms and Faithful, with a continuation whose `analytic`, `root` and `boundary` clauses (CS:135-143) hold for `correlation (some i)`.
  - Lean check: AuditScripts/Probes/reconbridge_perphase.lean, standard axioms (`perPhase_zero_word`, `antiPhase_has_no_perPhase_data`). Per-character data forces a constant zero-word one-point correlation to be 0, so the anti-phase, whose value there is 2, is excluded.
  - A standard-math argument, not in Lean, extends this to every link-blind (product) Wilson limit. It also closes the GFF route of D2.
  - The detailed theorem already has this data: YM/EveryPhase/Pack.lean:122, YM/EveryPhase/Extension.lean:52, HeadlineSpec.lean:79, Construction.lean:27,39. The public proof can copy `publicReconstruction` (HierarchyBridge.lean:79-133) once per character, and Solution.lean need not change.
- **F2 (complementary).** Require `correlation`, `coefficient` and `continuation` to be multilinear in the field vectors.
  - This needs a `Module ℂ` structure on `WilsonFamily.Token` (PW:44), which changes a trusted signature.
  - It blocks the compiled reduction. One corner, an extra non-identity grade-0 field, is unsettled.
- **Not sufficient on their own:**
  - Fixing insertions to translates of fixed nonconstant lattice operators. Bounded plaquette insertions concentrate as β_N → ∞ under CS:13-14 and reproduce `allZero` (argued, not formalized).
  - A stronger `localSupport`: constant insertions satisfy every stencil.
  - Identifying `centeredTrace` with a lattice observable.

### 2.2 High

**D2. `Properties.nonfree` is passed by generalized free fields.** Location: CS:168-175 and CS:181.

*What is wrong.* For simple g, TraceTest is equivalent to `centered ∧ shortDistance`:
- `amplitudePositive` follows from IsSimple (Lean).
- `excludes` follows from `shortDistance`, because every `wickProfile` is a finite sum of (log r)^b times Laurent series with b ≥ 0 (argued).

So the whole test is one two-point asymptotic for a grade-4 field the statement does not identify. A scalar GFF with ρ(s) = (dim g/16π²)·s²/log²s for s ≥ s₀ > 1 passes it. Follow-up 2 argues, on paper with numerical checks, that the same GFF also satisfies Reconstructed and the OPE.

*Why it matters.* RM:14 presents the clause as a non-freeness test, but it certifies neither interaction nor non-Gaussianity. Combined with D1, JointExistence would follow from a GFF hierarchy with no gauge or lattice content. Follow-up 2 rates this combination critical; the GFF facts are standard mathematics but not formalized. RM:26 does put general exclusion of continuous-mass GFFs out of scope.

*Fix.* F1 is the effective fix, because it forces the selected phase to be a component of a genuine Wilson limit. If the clause is meant to certify interaction on its own, it needs a condition that GFFs and their Wick polynomials fail; no follow-up designed one. Otherwise RM:14 should describe it as a short-distance normalization check.

### 2.3 Medium

**D3. The gauge-group constant is pure normalization (machine-checked).** Items: `TraceTest.shortDistance` (CS:173-174) and `Hierarchy.centeredTrace` (CS:48).

*What is wrong.* `centeredTrace` is any vector of Field 4. The trusted statement does not identify it with the stress trace; only the detailed theorem does (RM:14). Nothing fixes the normalization of `toLabel`, and nothing requires the trace label to be Hermitian. Scaling every label by k ∈ ℂ changes the data as follows:
- n-point correlations and continuations are multiplied by kⁿ;
- OPE coefficients are adjusted to match;
- Reconstructed, the OPE, `centered`, `excludes` and ZeroInvisible all survive;
- `traceTwo` is multiplied by k².

*Evidence.* AuditScripts/Probes/inventory_crossgroup.lean, run 2, EXIT 0, standard axioms only (`inventory_crossgroup_run2.log`):
- `cross_group` (line 1273);
- `jointExistence_of_single` (line 1282): any nonzero L ∈ ℂ suffices;
- `jointExistence_of_one_group` (line 1295);
- `perGroup_of_any_constant` (line 1365): on a genuine Wilson family, without ZeroInvisible.

*Why it matters.* Outside the inert lattice layer, g appears only through `finrank ℝ g.lieAlgebra` (CS:172-174), and that number can be absorbed into the rescaling. JointExistence therefore cannot tell SU(2) from E8. The advertised positive coefficient is not tested either: a negative or non-real L works as well.

*Fix.* Pin the normalization in the public statement. For example: add a stress-tensor label family whose time components integrate to the generators of the W0 translations (a Ward identity), and take `centeredTrace` to be its centered trace. At a minimum, require `toLabel 4 centeredTrace ≠ 0` and that it be fixed by `adjointLabel`; Hermiticity alone fixes only the sign of the constant.

**Other medium findings.**

| Finding | Location | What is wrong | Why it matters for JointExistence | Fix |
|---|---|---|---|---|
| Hierarchy.correlation (pitfall) | CS:41 | An arbitrary function of (phase, tags, points): not multilinear, may be nonzero on zero vectors, and has no covariance or positivity outside the selected phase. | Cause C of D1: it lets `none` be `allZero`. | F2. |
| Hierarchy.coefficient (deviation) | CS:46-47 | Not multilinear in the cluster vectors, not covariant, not measurable. It is correctly independent of spectators, phase and degree. | The nonlinear coefficient `allZero a` closes the OPE step of D1, and the OPE is weaker than the standard one. | F2; translation covariance as well, if intended. |
| Hierarchy.actor (caveat) | CS:45 | Actors need not be nonzero or linearly independent. | A zero grade-0 actor serves as the identity channel for nonlinear phases while staying invisible to a linear selected phase (D1). | F2, or require nonzero, linearly independent actors in each grade. |
| Hierarchy.selected (caveat) | CS:40 | The only character tied to theory, continuation and TraceTest; its only lattice link is `mixture` (CS:133-134). | All continuum content sits in a phase that need not be a component of the Wilson limit (D1-B). | F1. |
| Hierarchy.Field (caveat) | CS:28-31 | CS:120 and CS:122 force cumulative grades, so the grade is a filtration level chosen by the prover. The trusted statement never uses the norm instances. | "Grade-four field" (RM:14) means level ≤ 4, and `weight` (CS:63) counts grade indices, so the OPE exponents use upper bounds. | Document grade as a filtration level; drop the unused norms or use them in the OPE bound. |
| OPE.remainder and Properties.ope (caveat) | CS:74-80, CS:180 | A faithful, uniform all-orders estimate with one coefficient system in every phase. But it is generic (a GFF's Wick/Taylor expansion satisfies it), and once one channel is added it cannot detect compensating phases. | Adds no Yang–Mills specificity and does not prevent D1. | F1 and F2. |

### 2.4 Low and info

| Finding | Location | Final [orig.] | What is wrong | Why it matters | Fix |
|---|---|---|---|---|---|
| PoincareAction.onLabels and W2.fieldCovariance | PT:225, PT:300-307 | deviation, low [medium] | Translations may act on labels, and the label representation need not be continuous, finite-dimensional or factor through the Lorentz part. So W2 on its own does not give translation-invariant Wightman functions; c-number labels x^μ·1 are an example. | Neutralized inside JointExistence: covers plus labelComposition kill eigencharacter actions (Lean: orbit_countable), and OPE.remainder kills unipotent ones (follow-up 6, partly argued). | Require `onLabels (pureTranslation a) = id`, and local finiteness. |
| Reconstructed.covers | CS:122 | deviation, low | Each label lies in a single grade image, which forces a cumulative grading. | Grade means filtration level, and `weight` depends on which representative is chosen. | Document this, or state the filtration explicitly. |
| WilsonFamily.Token, Hierarchy.project, Reconstructed.represents | PW:44, CS:33, CS:123 | caveat, low [loophole high; loophole medium; caveat medium] | A bare token type and an arbitrary surjection onto tags. Nothing ties a token to a field except the `none` limit. | D1 uses them only together with free insertions; Token := Tag with project := id works. | Covered by F1. F2 needs a Module structure on Token. |
| WilsonRegularity.running and WilsonFamily.beta | CS:13-14, PW:40 | caveat, low [deviation, medium] | Any positive slope is accepted, plus an o(log a⁻¹) drift uniform in p. This is not the asymptotic-freedom slope, but RM:11 promises only a positive slope. | Unused by D1, since β cancels for link-blind insertions. Even with genuine insertions it does not force the Yang–Mills line of constant physics. | If asymptotic freedom is intended, pin the slope to the group's one-loop value. |
| WilsonFamily.Converges | PW:85-90 | caveat, low [loophole, critical] | An honest iterated limit that constrains only the unselected function. | Its critical effect is D1, through `insertion`. CS:129-130 rules out a junk-integral path. | None beyond D1. |
| WilsonFamily.finiteMoment | PW:54-57 | faithful, low [caveat, medium] | A correct Wilson expectation, integrable because of CS:15. | It loses its content only through free insertions (D1-A). | None. |
| WilsonRegularity.localSupport | CS:19-22 | faithful, info [loophole, high] | An empty stencil is allowed, and insertions need not read the links. | Not a cause: constant insertions satisfy every stencil. | None; a stronger stencil would not fix D1. |
| EnergyMomentumMeasure.projection | PT:181 | pitfall, info | Defined on every set; values on non-Borel sets are junk. | Never read: the only external use (PT:275) is at a Borel set. | Optional: index it by measurable sets. |

## 3. Contested findings

**`Reconstructed.boundary` (CS:139-143): pitfall, medium. Votes: 1 upheld, 1 refuted.**
- **Upheld.** The Bochner integral returns 0 when the integrand is not integrable (`integral_undef`, Mathlib MeasureTheory/Integral/Bochner/Basic.lean:202). A word containing a zero-label tag has vacuum expectation 0, so `boundary` can hold whatever its correlation is. The bridge therefore constrains only words whose Wightman functions are not identically zero.
- **Refuted.** The background facts are right, but the mechanism offered does not work. `analytic` plus the smooth Euclidean values fix a measurable continuation, compactly supported product tests make the integrals genuine, and dense blow-ups would break analyticity (Baire). So the junk value can only make the clause harder to satisfy.
- **Resolution (follow-up 3).** Both sides are partly right, and the split is by arity.
  - **n = 1.** Height 0 is admissible, so the integration surface does not move with r. A Baire–Montel argument then forces the correlation to vanish. The refuting side is right here.
  - **n ≥ 2.** There is an explicit smooth, symmetric, nonzero S on a zero-label 2-word. An example is the word read by `traceTwo` when centeredTrace = 0. S satisfies root, analytic, smooth, permutation and boundary, because the set where the integrand fails to be integrable becomes dense only as r → 0. The upholding side is right here, with that corrected mechanism.
  - The Lean facts compile: `ve_eq_zero`, `boundary_of_junk` and `one_point_integral_zero` in AuditScripts/Probes/reconbridge_zerojunk.lean (`zerojunk_run1.log`). The analytic estimates are on paper only.
  - Consequences:
    - ZeroInvisible does not follow from Reconstructed.
    - `TraceTest.centered` can be vacuous, by taking centeredTrace = 0.
    - An exploit with H = ℂ still appears to be blocked by an OPE rank inequality; the last step of that argument is checked only numerically.
  - Fix: require the boundary integrand to be integrable for small r, or impose multilinearity (F2), or require `toLabel 4 centeredTrace ≠ 0`. The rating stays pitfall/medium.

## 4. Follow-up checks

1. **The Wilson clause is redundant (loophole, critical; kernel-checked).**
   - The ten Audit/Reduction sources contain no `sorry`, `admit` or `axiom`. A verbatim concatenation (AuditScripts/Probes/rebaseline_jointchain.lean) compiles with EXIT 0 and standard axioms only.
   - The compiled `.olean` files for Converges, Haar, Law, OPE, Recon and Riemann are older than their sources, and Main was built against them. The probes import only ChallengeSpec and Defs, so they are unaffected. Earlier notes saying sorries remain are out of date.
   - The hypothesis is exactly as stated in D1, with no hidden hypotheses; q = id and T does not depend on p.
   - Settled ratings, integrated above: insertion, mixture, Properties.wilson and JointExistence critical; Character, phaseMeasure and Properties.reconstruction recorded under mixture; correlation pitfall/medium; Token, project, represents, running and Converges caveat/low; finiteMoment faithful/low; localSupport faithful/info.
   - Not established: whether causes A and B, without C, admit some other witness.
2. **A GFF witness works on paper (loophole, critical in combination with D1).**
   - Density σ(m) = c·m⁵/log²m for m ≥ m₀ > 1. Then r⁸ log²(1/r) S(r) → 96c/π², and c = dim g/(32π²) hits the target; equivalently ρ(s) = (dim g/16π²) s²/log²s. Numerically the ratio to the target is 0.81 at r = e⁻¹⁶ and 0.947 at e⁻⁶⁴.
   - Clause by clause:
     - OPE: Wick plus Taylor expansion, using ‖∂^β S(z)‖ ≤ C‖z‖^{−8−#β}, uniformly over spectators.
     - Faithful and injective: by a symmetric-polynomial argument.
     - W0-W3: on the Fock space.
     - analytic, root and boundary: via the forward tube and dominated convergence.
     - TraceTest: `excludes` follows from `shortDistance`.
   - New Lean fact: every witness must contain an identity field in Field 0 (AuditScripts/Probes/gffgap_emptycluster.lean: `empty_coeff_zero`, `empty_cluster_exact`, `identity_channel_needed`).
   - Density corrections: μ⁴/log²μ is right only as a density against d(μ²), and m⁶/log²m against dm is wrong.
   - A countable tower of discrete-mass free fields also works, but is no easier to build.
   - Gap: the GFF facts are standard but not formalized. Scripts: `gff_check.py` and `gff_disc.py`.
3. **`boundary` on zero-label words (pitfall, medium).** Forced to vanish for n = 1, free for n ≥ 2; details in Section 3.
4. **Inventory and cross-group transfer (loophole, medium; machine-checked).**
   - Classification: redundant, inert under D1, dim-only, or real content. This is the Role column.
   - `cross_group`, `jointExistence_of_one_group`, `jointExistence_of_single` and `perGroup_of_any_constant` are proved (D3).
   - dim su(2) = 3 is checked (`lieAlgebra_finrank`, line 1423), with one gap. Its instantiation at `su2` relies on private lemmas in YM/Examples/SU2.lean:38-69, which could not be loaded.
   - The suggested "quadratic hypothesis" is false as literally stated, because r = 0 is never read. For r > 0 it is undecided, and the rescaling argument makes it moot.
5. **Repairs.**
   - F1, per-character reconstruction, blocks the reduction (Lean probe plus a standard-math extension), and the detailed theorem already proves it.
   - F2, multilinearity, blocks the compiled reduction and the c-number route, except for the grade-0 corner.
   - Fixed, normalized lattice insertions alone do not block it: as β_N → ∞, bounded insertions concentrate and reproduce `allZero`.
   - Identifying centeredTrace with a lattice observable alone does not block it either.
6. **Translation action on labels (deviation, low).**
   - Taken alone, PT allows a Faithful W0-W3 theory with c-number labels x^μ·1 whose vacuum expectations are not translation invariant.
   - Inside JointExistence this is neutralized:
     - CS:122 with CS:31 gives labels of rank at most ℵ₀ (Lean, AuditScripts/Probes/labelope_orbit.lean:27).
     - `conj_translation`, `eigen_transport` and `orbit_countable` (lines 61, 77, 97) show that every eigencharacter has a countable Lorentz orbit, which forces it to be trivial.
     - Unipotent actions are killed by `remainder`: through uniformity in the centre o for operator-valued bottoms, and through spectators at unbounded distance (Clear) followed by TraceTest for c-number bottoms.
   - Not formalized: Reeh–Schlieder separation, cluster decomposition, and uniqueness of boundary values. The sub-case where the trace label itself carries a unipotent action was not fully closed.
   - No exploiting hierarchy was found, so the severity drops from medium to low.
