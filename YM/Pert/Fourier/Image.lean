import YM.Pert.Fourier.Return
/-! Image line at distances tending to infinity in physical units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Lattice Filter Topology Full Function Set
open scoped BigOperators Classical RealInnerProductSpace

lemma corona_wide_price (D : List Axis) : ∃ C>0,∀ {n : Side} (z : Site n) (s h : ℝ), s>0 → h>0 → h*s≤1/2 → 0< ‖incVec h (Lattice.lift z)‖ → mesh n * ((D.length+4:ℕ):ℝ)≤h*s →
    ‖corona h s D z‖ ≤ C/s * (turn * ‖incVec h (Lattice.lift z)‖⁻¹)^(D.length+3) := by
  obtain ⟨E,hE,H⟩ := ctrl D (D.length+3)
  refine ⟨E/turn^4,by positivity,fun {n} z s h hs hh hw hr hN=>?_⟩
  let T:=mesh n/(h*s);let c:ℝ:=((n.val:ℝ)*h)⁻¹;let R:=‖incVec h (Lattice.lift z)‖
  obtain ⟨k,hk⟩ := signal z h hh
  have hx : T*s=turn*c := by unfold c T mesh; field_simp
  have hp := (H (mul_pos hh hs) (t:=h*s) (n:=n) (hw.trans (by norm_num)) (by push_cast at *; nlinarith only [hN,hw,mesh_pos (n:=n)]) (by push_cast at hN ⊢; linarith only [hN]) k z).1
  let L:ℂ := ∑ p, char p z*ringM D (h*s) p
  convert! convert_one hh hs hr hE L c rfl D.length hx k z hk hp (corona_expand h s hh hs D z) using 1
  unfold turn; rw [div_eq_mul_inv (2*_ : ℝ) R]; ring

variable (n c : ℕ→Side) (h : ℕ→ℝ) (D : List Axis) (x : ∀ i, Site (n i))
lemma joint_far (hc : ∀ i, (c i).val=((n i).val:ℝ)* h i) (hh : ∀ i, 0<h i) (hv : Tendsto (fun i=>(c i).val) atTop atTop) (he : Tendsto h atTop (𝓝 0))
    (hf : Tendsto (fun i=>‖incVec (h i) (Lattice.lift (x i))‖) atTop atTop) : Tendsto (fun i=>joint (h i) D (x i)) atTop (𝓝 0) := by
  apply wrap_tube (cash:=fun i s=>piece (h i) s D (x i)) (graph:=fun _=>0) (D.length+1) _ (initial_estimate n c h D x hc hh hv he ⟨1,by norm_num,hf.eventually (eventually_ge_atTop 1)⟩) ⟨0,le_rfl,0,le_rfl,fun s hs=>by simp⟩
  intro s hs
  change Tendsto (fun i=> corona (h i) s D (x i)) atTop (𝓝 (0-0))
  rw [sub_self,tendsto_zero_iff_norm_tendsto_zero]; obtain ⟨C,hC,H⟩ := corona_wide_price D
  let m (i : ℕ) := ‖incVec (h i) (Lattice.lift (x i))‖
  let k:=D.length+3
  have ht : Tendsto (fun i=> C/s * (turn * (m i)⁻¹)^k) atTop (𝓝 (C/s * (turn*(0:ℝ))^k)) := (((tendsto_inv_atTop_zero.comp hf).const_mul turn).pow _).const_mul _
  simpa [k] using squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) (show ∀ᶠ i in atTop, _ ≤ C/s * (turn * (m i)⁻¹)^k from ((hbound _ he s|>.and (mesh_light n c h D hc hv s hs)).and (hf.eventually (eventually_gt_atTop 0))).mono (fun i hi=> H _ _ _ hs (hh _) hi.1.1 hi.2 hi.1.2)) (by rwa [mul_zero, zero_pow (by omega : k≠0),mul_zero] at ht)
end YM.Pert.Band
