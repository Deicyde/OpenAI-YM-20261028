import YM.Pert.Lattice.Precision
import YM.Work.F03.Flat
/-! Quadratic and higher Wilson vertices at the identity orbit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice Function Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side}
abbrev Potential (G : Gauge) (n : Side) := ↥(LinkP G n)

def positiveLinks (a : Potential G n) : Orb.Links n → G.El := fun l => G.lieExp (a.val l)
def plaquette (a : Potential G n) (x : Site n) (i j : Axis) : G.El :=
  let u := positiveLinks a
  u (x,i) * u (x+step i,j) * (u (x+step j,i))⁻¹ * (u (x,j))⁻¹

@[simp] lemma pos_flat (l : Orb.Links n) : positiveLinks (0 : Potential G n) l = 1 := G.mat_lieExp_zero
@[simp] lemma plaquette_flat (x : Site n) (i j : Axis) : plaquette (0 : Potential G n) x i j = 1 := by simp [plaquette]
def takeLink (l : Orb.Links n) : Potential G n →ₗ[ℝ] G.Color := (LinearMap.proj (R:=ℝ) l).comp (LinkP G n).subtype
def takeDiv (x : Site n) : Potential G n →ₗ[ℝ] G.Color := (LinearMap.proj (R:=ℝ) x).comp ((Mean G n).subtype ∘ₗ dLin)
lemma pos_mDiff (l : Orb.Links n) : ContDiff ℝ ω (fun a : Potential G n => G.mat (positiveLinks a l)) :=
  G.exp_jet.comp ((takeLink l).toContinuousLinearMap.contDiff)
lemma pInv_mDiff (l : Orb.Links n) : ContDiff ℝ ω (fun a : Potential G n => G.mat (positiveLinks a l)⁻¹) :=
  (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (pos_mDiff _)
lemma pos_sqDiff (x : Site n) (i j : Axis) : ContDiff ℝ ω (fun a : Potential G n => G.mat (plaquette a x i j)) := by
  simp only [plaquette,G.mat_mul]
  exact (((pos_mDiff _).mul (pos_mDiff _)).mul (pInv_mDiff _)).mul (pInv_mDiff _)

lemma line_diff (v : G.Color) : HasDerivAt (fun r : ℝ => G.mat (G.lieExp (r • v))) (G.colorMat v) 0 := by
  refine HasFDerivAt.comp_hasDerivAt (f:=fun r=>r • v) (l:=fun v'=>G.mat (G.lieExp v')) (l':=G.colorMat.toContinuousLinearMap) _ ?_ ?_
  · rw [zero_smul]; exact G.expDiff_zero
  simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v
lemma link_diff (l : Orb.Links n) (v : Potential G n) : HasDerivAt (fun r : ℝ => G.mat (positiveLinks (r • v) l)) (G.colorMat (v.val l)) 0 := line_diff _
lemma inv_diff (l : Orb.Links n) (v : Potential G n) : HasDerivAt (fun r : ℝ => G.mat ((positiveLinks (r • v) l)⁻¹)) (-G.colorMat (v.val l)) 0 := G.colorMat_skew _ ▸ (link_diff l v).star
lemma plaq_diff (x : Site n) (i j : Axis) (v : Potential G n) : HasDerivAt (fun r : ℝ => G.mat (plaquette (r • v) x i j)) (G.colorMat (curL x i j v)) 0 := by
  have ht := (((link_diff (x,i) v).mul (link_diff (x+step i,j) v)).mul (inv_diff (x+step j,i) v)).mul (inv_diff (x,j) v)
  simp only [plaquette,G.mat_mul]
  convert! ht using 1
  · change G.colorMat (cur v.val x i j)=_
    simp only [cur,map_sub,map_add,zero_smul,pos_flat,inv_one,G.mat_one,Pi.mul_apply,mul_one,one_mul]
    abel
lemma price_limit (x : Site n) (i j : Axis) (v : Potential G n) : Tendsto (fun r : ℝ => G.price (plaquette (r • v) x i j)/r^2) (𝓝[≠] 0) (𝓝 (‖curL x i j v‖^2/2)) := Work.F03.price_limit (by simp) (plaq_diff ..)

def wilson (a : Potential G n) : ℝ := (∑ x : Site n, ∑ i : Axis, ∑ j : Axis, if i<j then G.price (plaquette a x i j) else 0)/2
def fixing (a : Potential G n) : ℝ := (∑ x : Site n, ‖takeDiv x a‖^2)/4
def action (G : Gauge) (n : Side) (a : Potential G n) : ℝ := wilson a + fixing a

lemma limit_action (a : Potential G n) : Tendsto (fun r : ℝ => action G n (r • a) /r^2) (𝓝[≠]0) (𝓝 (form a a/2)) := by
  unfold form; simp_rw [real_inner_self_eq_norm_sq]
  have hw (r : ℝ) : wilson (r • a)/r^2 = (∑ x : Site n, ∑ i : Axis, ∑ j : Axis, if i<j then G.price (plaquette (r • a) x i j)/r^2 else 0)/2 := by simp [wilson,div_right_comm _ (2:ℝ),Finset.sum_div,ite_div]
  have H : Tendsto (fun r:ℝ => wilson (r • a)/r^2) (𝓝[≠]0) (𝓝 ((∑ x : Site n, ∑ i : Axis, ∑ j : Axis, if i<j then ‖curL x i j a‖^2 else 0)/2/2)) := by
    simp only [Finset.sum_div,ite_div,zero_div,hw]
    refine tendsto_finsetSum _ (fun x _ => tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => dite (i<j) (fun h => by simp only [if_pos h]; exact (price_limit x i j a).div_const _) (fun h => by simp [if_neg h]))))
  have he {r : ℝ} (hr : r≠0) : fixing (r • a) / r^2 = fixing a := by simp only [fixing,div_right_comm _ (4:ℝ),Finset.sum_div,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_div_cancel_left₀ _ (pow_ne_zero _ hr)]
  have hF : Tendsto (fun r : ℝ => fixing (r • a) /r^2) (𝓝[≠]0) (𝓝 (fixing a)) := (tendsto_const_nhds (x:=fixing a)).congr' ((show ∀ᶠ x in 𝓝[≠](0:ℝ), x ≠ 0 from self_mem_nhdsWithin).mono (fun r hr => (he hr).symm))
  simp only [action,add_div]; convert! H.add hF using 2
  change _ = _ + fixing a
  rw [fixing]; simp_rw [show ∀ x, takeDiv x a = (dLin a).val x from fun _ => rfl]; ring
lemma diff_action : ContDiffAt ℝ ω (action G n) 0 := by
  have hF (x : Site n) : ContDiff ℝ ω (fun a : Potential G n => ‖takeDiv x a‖^2) := (contDiff_norm_sq ℝ).comp ((takeDiv x).toContinuousLinearMap.contDiff)
  apply ContDiffAt.add
  · unfold wilson; refine (ContDiffAt.sum (fun x _ => ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ?_)))).div_const _
    split
    · exact Work.F03.price_smooth (pos_sqDiff ..).contDiffAt
    exact contDiffAt_const
  exact (ContDiffAt.sum (fun x _ => (hF x).contDiffAt)).div_const _
lemma jets_action : action G n 0=0 ∧ fderiv ℝ (action G n) 0=0 ∧ ∀ v w : Potential G n, iteratedFDeriv ℝ 2 (action G n) 0 ![v,w]=form v w := Work.F03.hessian_of_limit (diff_action.of_le (by exact le_top)) limit_action form_add form_symm
end YM.Pert.Orb
