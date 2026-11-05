import YM.OPE.Single
import YM.OPE.Trees.Manifest
/-!
# All fixed-horizon demands at once (the subpower version including factorization)

A joint strengthened existence theorem on the Wilson constructions of
`Spec.CLOSED`, with *no* hypothesis added. Gives one prescription by
biorthogonal fields & positive-clearance separated detectors (unselected), an
anisotropic fixed basis choice. No equivariance of the detector or splitting
is asserted. This does not change the model, its normalization, real and
continuous rotations of the physical theory. Fields are of any specified
filtration levels. `C.path.levels.clock.kernel.penalty` chosen before certificates; Family makes
and extraction and Stress/Wightman etc. remain those of Final. The unselected
data and all the character phases tested simultaneously. Operator norm bound
explicitly on the true ground algebra.

For every finite labelled vertex set `I`, `Arboreal I` is a cluster tree with
root internal and arbitrary children valences. `v` supplies labels of all its
leaves (values on internal nodes ignored); `q` is any exterior word (uses the
arbitrary naming scheme `J`, and the API has `worded`,`perm_observe`,... to
express as lists too). Real space `E4` times unrestricted; these are Euclidean
products. All thresholds are AFTER choosing these fixed data. `Convoy` uses
compact shapes M-upper, δ-clear (declared subtree clearances), including
all nongeneric points within the given geometries. Only size conditions besides
these are positive collapsing scales with child scale at most parent scale.
Root scale r shrinks with ε-loss currently. No powers of spectator norm etc.
hidden by selection. Common tails for any finite number of estimates.

The bounds in this file are in an arbitrarily-small power-loss version. They
**do NOT have logarithmic powers** in place of ε-losses here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Finset Arboreal
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
    (P: Prescription U.sector.derivatives)
structure AllShapes : Prop extends SingleSubpower U P where
    direct_and_nest {I: Type}[Fintype I] (s:Arboreal I) (v:I→ C.book.Token) (w:Mode U.sector.derivatives) (D:I→ℕ) (M δ ε:ℝ) :
        0 ≤ M→ 0 < δ → 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x:I→ E4) (t:I→ℝ),
           t s.root=r → s.Convoy M δ t x → s.ValueRate U P w v D ε x t
    discounted {I J:Type}[Fintype I][Fintype J] (s:Arboreal I)(v:I→ C.book.Token)(q:J→ C.book.Token) (n:ℕ) (M δ ε c:ℝ) :
        0 ≤ M → 0 < δ → 0 < ε → 0 < c → ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x:I→ E4)(t:I→ℝ)(y:J→ E4),
           t s.root=r → s.Convoy M δ t x → ClearOf (x s.root) y c → s.TestedRate U P v q n ε x t y

lemma Services.everything (h:Services C F S)(hp:P.Coherent) : AllShapes U P:=
    ⟨one_radius U hp h,fun s v w D _ _ _ => s.sample U v w D hp h, fun s v q n _ _ _ _=> s.session U v q n hp h⟩

/-- Public all-horizons, all-character, all-fixed finite trees
existence (SUBPOWER cost). -/
theorem subpower (G:Gauge)(h:G.Simple){b:ℝ}(hb:0<b) (f:Extraction.Order) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b∧ ∃ (g:Extraction.Order)(S:Table C.book), Services C (f.refine g) S ∧ ∃ (U:Spec.Final C (f.refine g) S) (P: Prescription U.sector.derivatives), AllShapes U P:=by
    obtain ⟨C,hC,g,S,hV,⟨U⟩⟩:= through_final h hb f; obtain ⟨p,hp⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
    exact ⟨C,hC,g,S,hV,U,p,hV.everything U p hp⟩
end YM.OPE
