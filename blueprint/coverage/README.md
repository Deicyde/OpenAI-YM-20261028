# Coverage contract

| Area | Coverage | Evidence |
| --- | --- | --- |
| PublicTheory.lean: compact simple matrix gauge groups | `DECOMPOSED` | [Compact simple matrix gauge groups](../roadmap/gauge-groups/README.md): the matrix gauge group and the simplicity of its Lie algebra. |
| PublicTheory.lean: spacetime and test functions | `DECOMPOSED` | [Spacetime and space](../roadmap/spacetime/spacetime-coordinates.md), [Minkowski square](../roadmap/spacetime/minkowski-square.md), [Closed forward light cone](../roadmap/spacetime/forward-light-cone.md), [Spacelike vectors](../roadmap/spacetime/spacelike-vectors.md), [Schwartz test functions](../roadmap/spacetime/schwartz-test-functions.md) and [Complex conjugate of a test function](../roadmap/spacetime/conjugate-test-function.md). |
| PublicTheory.lean: basic quantum-field structures | `DECOMPOSED` | [Hilbert space and bounded operators](../roadmap/wightman/hilbert-space.md), [Field labels](../roadmap/wightman/field-labels.md), [Field system](../roadmap/wightman/field-system.md), [Vectors generated from the vacuum](../roadmap/wightman/field-vectors.md), [Vacuum expectation values](../roadmap/wightman/vacuum-expectation-values.md), [Domain axioms](../roadmap/wightman/domain-axioms.md), [Adjoint axiom](../roadmap/wightman/adjoint-axiom.md), [Spacelike separated Schwartz test functions](../roadmap/spacetime/spacelike-separated-tests.md), [Local commutativity](../roadmap/wightman/local-commutativity.md) and [Faithful field system](../roadmap/wightman/faithful-fields.md). |
| PublicTheory.lean: translations, spectrum and Poincaré covariance | `DECOMPOSED` | [Translation representation](../roadmap/wightman/translation-representation.md), [Energy–momentum measure](../roadmap/wightman/energy-momentum-measure.md), [Proper orthochronous Lorentz transformations and Poincaré coordinates](../roadmap/spacetime/lorentz-and-poincare.md) and [Poincaré action](../roadmap/wightman/poincare-action.md). |
| PublicTheory.lean: Wightman axioms W0–W3 | `DECOMPOSED` | [Wightman theory data](../roadmap/wightman/wightman-theory.md), [Axiom W0](../roadmap/wightman/axiom-w0.md), [Axiom W1](../roadmap/wightman/axiom-w1.md), [Axiom W2](../roadmap/wightman/axiom-w2.md), [Axiom W3](../roadmap/wightman/axiom-w3.md) and [The Wightman axioms](../roadmap/wightman/wightman-axioms.md). |
| PublicWilson.lean: periodic lattice, Wilson action and Wilson measure | `DECOMPOSED` | [Periodic lattice](../roadmap/wilson-lattice/periodic-lattice.md), [Link configurations](../roadmap/wilson-lattice/link-configurations.md), [Plaquette](../roadmap/wilson-lattice/plaquette.md), [Wilson action](../roadmap/wilson-lattice/wilson-action.md) and [Wilson measure](../roadmap/wilson-lattice/wilson-measure.md); the two unnamed instances that give the gauge group its Borel σ-algebra are [supporting entries](../sources/public-wilson.md#supporting-entries) of the ledger. |
| PublicWilson.lean: point configurations and separated test functions | `DECOMPOSED` | [Configurations of n points](../roadmap/spacetime/point-configurations.md), [Separated configurations](../roadmap/spacetime/separated-configurations.md) and [Test functions on separated configurations](../roadmap/spacetime/separated-test-functions.md). |
| PublicWilson.lean: Wilson families and the ordered continuum limit | `DECOMPOSED` | [Wilson family](../roadmap/wilson-lattice/wilson-family.md), [Lattice spacing and positions of sites](../roadmap/wilson-lattice/lattice-spacing-and-positions.md), [Finite lattice moments](../roadmap/wilson-lattice/finite-moments.md), [Tests suited to a volume](../roadmap/wilson-lattice/suitable-tests.md), [Smeared lattice moments](../roadmap/wilson-lattice/smeared-moments.md) and [Ordered continuum limit](../roadmap/wilson-lattice/ordered-continuum-limit.md). |
| ChallengeSpec.lean: regularity of a Wilson family | `DECOMPOSED` | [Regularity of a Wilson family](../roadmap/wilson-lattice/wilson-regularity.md): logarithmic running of the couplings, continuity, gauge invariance and a fixed stencil for each insertion. |
| ChallengeSpec.lean: continuum hierarchy and reconstruction | `DECOMPOSED` | [Continuum hierarchy and Wightman reconstruction](../roadmap/continuum-hierarchy/README.md): the hierarchy, the variables of its analytic continuation and the reconstruction conditions. |
| ChallengeSpec.lean: operator product expansion | `DECOMPOSED` | [All-orders separated operator product expansion](../roadmap/operator-product-expansion/README.md): clusters and spectators, the weight of a cluster, joint correlations and the coefficient and remainder bounds. |
| ChallengeSpec.lean: non-freeness test | `DECOMPOSED` | [Non-freeness test](../roadmap/non-freeness/README.md): the trace two-point function, mass-shell modes, Wick profiles and the trace test. |
| ChallengeSpec.lean: four properties and joint existence | `DECOMPOSED` | [The four properties of a hierarchy](../roadmap/challenge/hierarchy-properties.md) and the [joint existence statement](../roadmap/challenge/joint-existence.md). |
| Solution.lean: the main theorem | `DECOMPOSED` | [The main theorem](../roadmap/challenge/challenge-theorem.md) asserts the joint existence statement; the [Solution.lean ledger](../sources/solution.md#the-main-theorem) records its proof and the declarations the proof uses. |
| YM/EveryPhase: reconstruction for every phase (Armstrong's unit V.3) | `MAPPED` | The chapter on reconstruction for every phase is being written from Armstrong's outline of unit V.3 and the modules of YM/EveryPhase. |
| The detailed construction and Armstrong's other thirty-one units | `DEFERRED` | Mapped in later versions of this book, one unit at a time, in the order of [Armstrong's informalization](../sources/armstrong.md): Construction.lean, the bridge and contact files, ConcreteSU2.lean and the other modules under YM/. |
| Challenge.lean | `OUT` | It restates the main theorem with the proof `sorry`, for comparison with Solution.lean; this project leaves it out of its checkout so that the theorem's name resolves to its proof. See the [Solution.lean ledger](../sources/solution.md#the-challenge-file). |
| Verification files: Verify.lean, VerifyJoint.lean and verification/ | `OUT` | Tools and records that check the proof against the challenge statement; they state no mathematics of the proof. |
| Mathlib (imported dependency) | `OUT` | Imported at the pinned commit 81a5d257c8e4 and not inventoried; the [Lean-side notes](../sources/lean-notes.md) record the Mathlib definitions the statements use. |

<!-- AUTHORING NOTES — these comments are not published.

     Keep one row per independently claimed area. Use MAPPED while the area
     still needs a terminal disposition. Use INVENTORIED for exact source
     accounting, with evidence that reaches a catalog: module inventory record.
     Use DECOMPOSED only for source-grounded declaration articles, with evidence
     that reaches those articles directly or through their containing roadmap
     scope. Use DEFERRED with a concrete later milestone, or OUT with a reason
     for exclusion.

     INVENTORIED is terminal for the inventory axis, but a module inventory is
     not mathematical exposition or a formalization target. DECOMPOSED is the
     separate claim that the source has declaration-bearing mathematical
     articles; an import list, Lean-status table, or declaration ledger alone
     does not support it.

     When both axes matter, give them distinct Area labels and rows, such as
     "Repository inventory / Algebra" and "Mathematical exposition / Algebra".
     Duplicate exact Area labels are invalid. A broad INVENTORIED row may link a
     containing scope while finer exposition rows evolve independently.

     Only the visible table above is the contract. A table written inside these
     notes, or inside a fenced or indented block, is ignored rather than trusted.
     Keep notes below the table: a comment between rows ends the table for every
     renderer, so rows under it would not be published. Leave a blank line above
     the table too, since a paragraph running into the header publishes no table.

     Evidence must say something a reader can act on, judged on what it renders
     as rather than on the Markdown source. A bare TODO, a lone code span, an
     empty link such as [ ](notes.md), text a browser hides, and a marker such as
     "TBD - pick a milestone" are rejected. A status word that opens a real
     sentence is fine. Every local link in an INVENTORIED or DECOMPOSED cell
     must resolve, fragments included.

     Reaching a terminal disposition on every row means no row is still MAPPED.
     It does not mean the rows cover the source exhaustively; that judgement is
     yours, so choose areas that genuinely span what the project claims.
-->
