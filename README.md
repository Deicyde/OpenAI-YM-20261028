# Wilson Yang–Mills construction

Project license: [Apache-2.0](LICENSE). [Source attributions](NOTICE) · [Third-party library licenses](THIRD_PARTY.md)

## The public challenge

[YangMills.jointExistence](Solution.lean) proves [JointExistence](ChallengeSpec.lean). The reference [Challenge.lean](Challenge.lean) has a Mathlib-only import closure. Its starting point is an earlier challenge at revision eea94292e31734d46498be7836d7e8fa50ca8cd2.

For each closed matrix subgroup with nonabelian simple real Lie algebra, choose one Wilson lattice family. For every strictly increasing sequence of volumes, it has a subsequence and a continuum hierarchy with the following properties.

- **Wilson origin.** Finite moments integrate products of local insertions against the normalized exponential of the plaquette action on the given group, with product Haar measure. For each insertion a finite set of offsets in lattice units controls every measurement, at every spacing and volume. Changing links outside that patch leaves the insertion unchanged. The ratio of the bare action coefficient to the logarithm of inverse lattice spacing tends to a positive slope, uniformly in the volume. Separated test-function moments have the full mesh limit at suitable fixed volumes, then the asserted volume limit. [Lattice and limits](PublicWilson.lean) · [Wilson bridge](WilsonBridge.lean)
- **Wightman reconstruction.** The selected phase has a normalized cyclic vacuum, faithful tempered fields on a common dense domain, positive energy, a unique translation-invariant vacuum up to scalar, covariance and spacelike locality. The symmetry coordinates cover every proper orthochronous affine Poincaré transformation and determine the inverse pullback on test functions. Analytic continuation recovers the selected Euclidean hierarchy at ordered imaginary times and its Wightman vacuum moments on product tests. Integrating the character correlations gives the unselected Wilson limit. The character measure has full support and the separated correlations vary continuously with the character. [W0–W3](PublicTheory.lean) · [Reconstruction bridge](HierarchyBridge.lean)
- **All-orders separated OPE.** For each finite cluster and collection of separated spectators, use a single system of coefficients at every truncation degree and in every phase. Both the full word and each term with the cluster replaced by a local insertion are reads of the same hierarchy. The bounds are uniform at all sufficiently small radii for the specified cluster size and separation constants. Permutation symmetry and smoothness hold off the collision diagonals. [Public estimates](ChallengeSpec.lean) · [Derivation of the compact-set bounds](verification/CompactCheck.lean)
- **Non-freeness test.** A centered grade-four field has a two-point function with a positive short-distance coefficient of three times the real Lie-algebra dimension divided by π⁴, after multiplication by r⁸ log²(1/r). No finite sum of the specified mass-shell Wick profiles agrees with it at all sufficiently small radii. The detailed theorem identifies this field as the physical centered stress trace and supplies the distributional Wick and Maxwell tests. [Trace bridge](TraceBridge.lean)

[The SU(2) specialization](ConcreteSU2.lean) uses the defining representation and the included proof of simplicity.

## The detailed construction theorem

[YangMills.constructed](Construction.lean) quantifies over each positive blocking-kernel penalty. It chooses the family once, then refines each requested mesh/volume order. Each refinement has one table, one selected Wightman reconstruction, a reconstruction for every character, one OPE reader and a set of contact devices using that reader’s field basis. The public theorem is a projection of this result.

- The reader also satisfies integrated single-center estimates and admissible nested OPE estimates. The centered stress trace has countertests to finite Wick-polynomial correlators and to Maxwell Fock realizations obeying the stated physical-wave, vacuum, translation and locality conditions, including the specified invariant-sector test. [Exact statements](YM/Nonperturbative/HeadlineSpec.lean)
- The Euclidean contact construction produces continuous distributions on compact smooth tests, at every arity and in every phase. Their restriction to separated configurations agrees with this table’s ordinary correlations. The detailed theorem also retains the collision-resolution estimates, the field-basis identity and the admissible thresholds. This supplies an extension for the constructed prescription. Uniqueness over other contact prescriptions and raw cutoff convergence on collision diagonals are outside the claim. [Restriction proof](ContactBridge.lean) · [Full contact specification](YM/Contacts/Solstice/Result.lean)
- The same witnesses retain the leading position-space test comparison in the constructed moving frames. [Continuum theorem](YM/Nonperturbative/Continuum.lean) · [Position-test statement](YM/Pert/Position/Four.lean)

The volume limit allows refinement. The Wightman spectrum condition and uniqueness of the vacuum are the spectral conclusions in the public challenge. A positive mass gap, general exclusion of continuous-mass generalized free fields and all-orders MS-bar matching are outside its scope.

## Verification

The archive includes all YM project sources. A first build requires Git, Lean 4.32.0 (or elan to install it), and access to the nine public repositories pinned in the Lake manifest, or a populated dependency cache. From the extracted directory run

```sh
lake exe cache get
lake build WilsonReference WilsonConstruction
lake env lean -j1 -DmaxHeartbeats=0 -DmaxRecDepth=4096 VerifyJoint.lean
lake env lean -j1 -DmaxHeartbeats=0 verification/Usage.lean
lake env lean -j1 verification/CompactCheck.lean
```

[VerifyJoint.lean](VerifyJoint.lean) imports the solution and loads the reference in a separate environment. It checks the exact theorem type, compares the reachable public definitions, audits the permitted axioms, and replays the reachable project declarations in a kernel environment that initially contains only external libraries. The only placeholder in the new files is the reference theorem in Challenge.lean. Solution.lean imports the definitions and the construction. The reference proof is absent from its imports.

[Verification log](verification/joint-check.log) · [Headline roots](verification/joint-headlines.txt) · [Frozen reference source hashes](verification/challenge.sha256) · [Standard Comparator configuration](comparator.json)

Stock Lake resolved the reference, solution and SU(2) import graphs from an extracted copy using the pinned external packages. The reference has zero YM implementation imports. [Lake import check](verification/archive-graph.log) · [Weakened-statement and unproved-axiom controls](verification/negative-controls.log)

[The compact-set check](verification/compact-check.log) derives a uniform norm bound on the complete degree-j coefficient vector and the remainder estimate over every compact separated cluster and spectator set. It uses only the public OPE definition.

The public reference was built with only the pinned external libraries on the search path. The solution build re-elaborated all new modules and reused compiled modules of the previously checked Wilson release. The pinned Lean kernel replayed 100,168 project declarations for the 17 advertised results and found only the standard axioms of propositional extensionality, classical choice and quotient soundness. The standalone Comparator executable was not run. [Earlier build record](verification/build.log)

## Source coverage

The 17 audited theorems reach 100,168 of 250,319 imported project declarations. The tables flag the other 150,151. The 9,458 pre-existing YM modules were matched to their original build inputs. Nine modules carry source credits. Of the eight covered by the recorded credited-source recompile, seven had byte-identical compiled files. In the remaining module, the imports and all 149 kernel declarations, including their types and bodies, matched. [Build-input comparison](verification/source-match.log) · [Credited source checks](verification/attributions.log)

[Declaration usage](verification/declaration-usage.tsv) lists the imported project declarations, whether a headline’s elaborated type or proof reaches each one, and a dependency path for reached declarations. [Module usage](verification/module-usage.tsv) gives the counts by module. These counts include declarations generated by Lean. Independent corollaries, helper lemmas used only during elaboration and import-only files can appear outside the proof terms. [Usage check](verification/Usage.lean)

[SOURCES.sha256](SOURCES.sha256) covers the files in this source distribution, excluding the manifest itself.
