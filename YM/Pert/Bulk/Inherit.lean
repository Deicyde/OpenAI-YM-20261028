import YM.Pert.Bulk.Projected

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch Function Precision Filter Stationary Matrix
open scoped ENNReal Topology Classical BigOperators
variable {α β γ : Type} {L c f n : Side} [Fintype β]
lemma applies_bind {K : Kernel α β} {U:Kernel β γ} {σ p θ q:ℝ} {L':Side}
    (hk:RowCost σ L K p)(hu:RowCost θ L' U q)(hσ:0≤σ)(hθ:0≤θ)
    {A : Matrix (Co f α) (Co c β) ℝ} {B : Matrix (Co c β) (Co n γ) ℝ}
    (hf:Matches K A)(hc:Matches U B) : Matches (bind K U) (A * B) := by
  intro x y
  rw [Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [← applies_once hk hu hσ hθ hf hc x y]
  change (∑' z, if wrap n z=y.1 then _ else 0)=_
  have e z : (if wrap n z=y.1 then bind K U x (z,y.2) else 0)=∑ j,if wrap n z=y.1 then tagged K U j x (z,y.2) else 0 := by split <;> simp [*,bind_apply]
  rw [tsum_congr e,Summable.tsum_finsetSum ?_];rfl
  intro j _
  have hv := ((produce_any hk hu hσ hθ x j y.2).of_norm (f:= fun z=>K x (z.1,j)*U (z.1,j) (z.2,y.2))).prod_symm.prod.indicator (s:={z|wrap n z=y.1})
  exact hv.congr (fun z=>(Set.indicator_apply ..).trans (by rfl)) 
variable (g : Ratio c f) (V : Towers g.count) (H H' : Bed)
def carrier := H.inverse.acts f* installed g V.T * H'.metric.acts c
lemma matches_response {a b σ p u q : ℝ} (hg:V.T.strip a q) (hH:H.covered a p)(hH':H'.covered b u) (hs:0≤σ)(ha:σ≤a)(hs':0≤b)(hp:0≤p)(hq:0≤q) : Matches (response V H H') (carrier g V H H') := by
   have hR := cross_row (L:=g.count) hg hs ha
   have h := row_left (L:=g.count) hH.2.2.1 ha hR hs hp (by positivity)
   refine applies_bind (K:=bind (plain H.inverse) (install V.T)) h (plain0 hH'.2.1 le_rfl).1 hs hs' (?_:Matches _ (_*_)) (matches_plain _)
   exact applies_bind (plain0 hH.2.2.1 ha).1 hR hs hs (matches_plain _) (matches_install _)

variable {S : StepData c f} {K : Towers S.patch.L}
lemma inherited_precision (h : Towers.Diagonal S H H' K) {p p':Clip}{η D η' D':ℝ} (h1:Floor H p f η D)(h2:Floor H' p' c η' D') : carrier S.ratio K H H' * Exterior.d 1 c= Exterior.d 1 f * installed S.ratio K.A0 := by
   unfold carrier
   rw [Matrix.mul_assoc, h2.same,Matrix.mul_assoc _ _ (H'.diagonal.acts c * _),←Matrix.mul_assoc (installed S.ratio _), h.stays,← h1.same,← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp h1.inverse,Matrix.one_mul]
end YM.Pert.Bulk
