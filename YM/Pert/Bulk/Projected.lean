import YM.Pert.Bulk.NullPair

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Pert.Bulk
open Lattice Laurent RG Bloch Function Precision Filter Stationary Matrix
open scoped ENNReal Topology Classical BigOperators
variable {α β γ : Type} {L c f n : Side} [Fintype β]

def display (K: Kernel α β) (n : Side) (x:Market α) (y:Co n β) := ∑' z, if wrap n z=y.1 then K x (z,y.2) else 0
def Matches (K: Kernel α β) (A : Matrix (Co f α) (Co c β) ℝ) : Prop := ∀ (x:Market α) (y:Co c β), display K c x y = A (wrap f x.1,x.2) y
lemma matches_plain (R : Row α β) : Matches (plain R) (R.acts c) := by
  intro x y
  rw [display,← (Equiv.addRight x.1).tsum_eq (fun z=> if wrap c z=y.1 then plain R x (z,y.2) else 0)]
  apply tsum_congr ; intro z
  dsimp [plain]; simp [eq_comm]; rw [add_comm]
lemma matches_install {g:Ratio c f} (T:Cross g.count α β) : Matches (install T) (installed g T) := by
  intro x y
  let z := rent g.count x.1
  let l := wrap g.count x.1
  have he : wrap f x.1 = g.assemble (wrap c z,l) := by
     conv_lhs => rw [rent_balance g.count x.1,map_add]
     rw [Ratio.assemble,g.embed_wrap,add_comm]
  change display (install T) c x y = T.acts c (splitCo g α (wrap f x.1,x.2)) (id y)
  rw [split_co,he,g.assemble_parent,g.assemble_res]
  change (∑' v, if wrap c v=y.1 then install T x (v,y.2) else 0)=_
  rw [← (Equiv.addRight z).tsum_eq (fun v=> if wrap c v=y.1 then install T x (v,y.2) else 0)]
  apply tsum_congr ; intro v
  unfold install
  change (if wrap c (v+z)=y.1 then _ else 0)=(if y.1=wrap c z+wrap c v then T (l,x.2) y.2 v else 0)
  simp [z,l,map_add,eq_comm,add_comm]

lemma cost_any [Fintype β] {σ p:ℝ} {K : Kernel α β} (hk:RowCost σ L K p)(hσ:0≤σ)(v:Market α): Summable (K v) := by
   apply summable_from_receipt (w:=fun z=>σ*delta L v.1 z.1) (fun _=>mul_nonneg hσ (delta_nonneg ..))
   exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by finiteness) (by finiteness)) (convert_market (fun w=>bill _ _) _ (hk v))
omit [Fintype β] in
lemma produce_any {K:Kernel α β}{U:Kernel β γ}{σ p θ q:ℝ}{L':Side}(hk:RowCost σ L K p)(hu:RowCost θ L' U q) (hσ:0≤σ)(hθ:0≤θ) (x:Market α)(i:β)(j:γ):
  Summable fun w:Cover × Cover => |K x (w.1,i)*U (w.1,i) (w.2,j)| := by
  suffices ∑'k,∑'y,bill (K x (k,i)) (σ*delta L x.1 k)*bill (U (k,i) (y,j)) (θ*delta L' k y) ≠⊤ by
    convert summable_from_receipt (f:=fun w:Cover×_=>K x (w.1,i)*U (w.1,i) (w.2,j)) (w:=fun _=>0) (fun _=>le_rfl) ?_ |>.norm using 1
    · ext w; rw [Real.norm_eq_abs]
    rw [ENNReal.tsum_prod (f:=fun k y=>bill (K x (k,i)*U (k,i) (y,j)) 0)]; exact ne_top_of_le_ne_top this (ENNReal.tsum_le_tsum fun k=>ENNReal.tsum_le_tsum fun y=>bill_mul _ _ _ _ _ (add_nonneg (mul_nonneg hσ (delta_nonneg ..)) (mul_nonneg hθ (delta_nonneg ..))))
  simp_rw [ENNReal.tsum_mul_left]
  exact ne_top_of_le_ne_top (show ENNReal.ofReal p*ENNReal.ofReal q≠⊤ from by finiteness) ((ENNReal.tsum_le_tsum (g:=fun k=>_ *ENNReal.ofReal q) (fun k=>mul_le_mul_right (hu _ j) _)).trans (by rw [ENNReal.tsum_mul_right]; exact mul_le_mul_left (hk ..) _))

omit [Fintype β] in
lemma applies_once {K : Kernel α β} {U:Kernel β γ} {σ p θ q:ℝ} {L':Side}
    (hk:RowCost σ L K p)(hu:RowCost θ L' U q)(hσ:0≤σ)(hθ:0≤θ)
    {A : Matrix (Co f α) (Co c β) ℝ} {B : Matrix (Co c β) (Co n γ) ℝ}
    (hf:Matches K A)(hc:Matches U B) (x:Market α)(y:Co n γ)(j:β) : display (tagged K U j) n x y= ∑ l : Site c,A (wrap f x.1,x.2) (l,j)*B (l,j) y := by
  have ht (k:_) : Summable fun w:Cover×Cover => if wrap n w.2 = y.1 then K x (w.1,k)*U (w.1,k) (w.2,y.2) else 0 := by
      apply Summable.of_norm_bounded (produce_any hk hu hσ hθ x k y.2)
      intro w; split <;> simp [mul_nonneg]
  have he : display (tagged K U j) n x y = ∑' w:Cover×Cover, if wrap n w.2 = y.1 then K x (w.1,j)*U (w.1,j) (w.2,y.2) else 0 := by
      unfold display tagged
      replace hv v : (if wrap n v=y.1 then ∑' z,K x (z,j)*U (z,j) (v,y.2) else 0)=(∑'z,if wrap n v=y.1 then K x (z,j)*U (z,j) (v,y.2) else 0) := by split <;> simp_all
      rw [tsum_congr hv, (Equiv.prodComm Cover Cover).tsum_eq (f:=fun w:Cover×Cover=> if wrap n w.2 = y.1 then K x (w.1,j)*U (w.1,j) (w.2,y.2) else 0) |>.symm]
      convert (ht ..).prod_symm.tsum_prod.symm using 2 <;> rfl
  have hK : Summable (fun z=>K x (z,j)) := summable_from_receipt (fun _=>mul_nonneg hσ (delta_nonneg ..)) (ne_top_of_le_ne_top (by finiteness) (hk x j))
  calc
   display _ n _ _ = ∑'z, K x (z,j)*display U n (z,j) y := by
               rw [he,(ht ..).tsum_prod]; apply tsum_congr ; intro z; rw [display,← tsum_mul_left]; apply tsum_congr; intro w; split <;> simp [mul_nonneg]
   _ = ∑'z, K x (z,j)*B (wrap c z,j) y := tsum_congr (fun z => congr_arg (_* ·) (hc _ _))
   _ = _ := by
      have he' z : B (wrap c z,j) y = ∑ l : Site c, if wrap c z=l then B (l,j) y else 0 := by simp
      rw [tsum_congr (g:=fun z=>∑ l : Site c,(if wrap c z=l then K x (z,j) else 0)*B (l,j) y) (fun z=>?_)]
      swap; · rw [he',Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _;split <;> simp
      rw [Summable.tsum_finsetSum ?_]; simp_rw [tsum_mul_right, ← show ∀ l,display K c x (l,j)=_ from fun l=>hf x (l,j)]; rfl
      intro a _; apply Summable.mul_right
      exact (hK.indicator {z|wrap c z=a}).congr (fun z=> Set.indicator_apply ..)

end YM.Pert.Bulk
