import YM.Push.LOOP_COEFFICIENT.Contraction
import YM.Push.LOOP_COEFFICIENT.History.Approvals

/-!
# Allocating the loop paths in descending order without changing any supplied classical fields
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Hist
open Function Matrix Set Filter Lattice Laurent RG Precision Wilson Tree Exterior Bloch Bid Supply Block Producer Gauge
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {p q : Clip} {σ C Λ : ℝ} {n c f : Side} {St : StepData c f}
variable {a : Levels G} {B : Horizon a} {S : Sheet G} {R : Rolls S} {cost : PostCost R} {O : ChartRatio G}
  {N i m : ℕ}

def erase (U : PathData G) : PathData G := { U with loop i := { U.loop i with coeff := 0 } }
structure Saves (U T : PathData G) : Prop where
  row : U.row = T.row
  cubic : U.cubic = T.cubic
  quartic : U.quartic = T.quartic

lemma renew_ok (E : Row (TypeFace 2) (TypeFace 2)) (U : PathData G) : Saves (renew E U) U := ⟨rfl,rfl,rfl⟩





abbrev Profile (G : Gauge) := ℕ → ℕ → PathData G
variable {F : Profile G}
abbrev Fits (B : Horizon a) (N m) (T : PathData G) (Λ : ℝ) := Attached (B.H N m) T ∧ T.Bounds (a.params m).clip (a.params m).width (a.params m).paths Λ
def Resource (B : Horizon a) (F : Profile G) := ∀ N m,m≤N → ∃ Λ, Fits B N m (F N m) Λ
def node (B : Horizon a) (F : Profile G) (N m) (T : PathData G) := Saves T (F N m) ∧ Fits B N m T (a.clock.loopCap m)
def edge (B : Horizon a) (O : ChartRatio G) (cost : PostCost R) (N m) (up down : PathData G) (α : ℝ) :=
    |α + G.slopeConstant * Real.log (a.S.block m).val|+1 ≤ (a.params (m+1)).drift ∧ certified B O cost N m up down α
structure Partial (B : Horizon a) (O : ChartRatio G) (cost : PostCost R) (F : Profile G) (U : ℕ → PathData G) (α : ℕ → ℝ) (N m : ℕ) : Prop where
  top : U N = erase (F N N)
  vertices j : m ≤ j → j ≤ N → node B F N j (U j)
  links j : m ≤ j → j < N → edge B O cost N j (U (j+1)) (U j) (α j)

lemma advance (hr : Resource B F) (hb : Permitted a B O cost) {U α} (hu : Partial B O cost F U α N (m+1)) (hm : m<N) : ∃ U α, Partial B O cost F U α N m := by
  obtain ⟨_,hA,hB⟩ := hu.vertices _ (by rfl) hm
  obtain ⟨Λ,ht,hw⟩ := hr N m hm.le
  obtain ⟨v,X,hv,H⟩ := hb N m hm hA hB; obtain ⟨ht',hw',h⟩ := H ht hw
  refine ⟨Function.update U m (renew X (F N m)), Function.update α m v,by simpa [hm.ne.symm] using! hu.top,fun j hj he => ?_,fun j hj hN => ?_⟩
  · rcases hj.eq_or_lt with rfl|hj; · simpa using! (show node B F N m _ from ⟨renew_ok _ _,ht',hw'⟩)
    simpa [hj.ne.symm] using hu.vertices j hj he
  rcases hj.eq_or_lt with rfl|hj; · simpa using! (show edge B O cost N m (U (m+1)) _ _ from ⟨hv,h⟩)
  simpa [hj.ne.symm,show j+1≠m by omega] using! hu.links j hj hN

end YM.Push.Loops.Hist
