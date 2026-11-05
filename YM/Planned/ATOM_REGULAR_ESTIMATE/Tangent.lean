import YM.Planned.ATOM_REGULAR_ESTIMATE.Substitution

/-! Identify the tangent of the planted surface using the actual
path (`SolvesLink`) and build the leading homogeneous correction in radial
and gauge data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Flat
open Function Tensor MeasureTheory Filter Lattice Wilson RG Source Labels Source.Drops Gauge Next.Foundations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {d k : ℕ}

lemma truly (H : Hol G) (o : Site n) : visible H o =ᶠ[𝓝 (0:Perturb G d)] increment 1 ∘ surface H o := by
  have hh (i : Edge (Site n)) : ∀ᶠ x in 𝓝 (0:Perturb G d), visible H o x i = G.lieExp (surface H o x i) := by
    have hp := visible_mat (d:=d) H o i
    have hh : ContinuousAt (fun x => visible H o x i) (0:Perturb G d) :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr hp.1.continuousAt
    have ht : Tendsto (fun x => visible H o x i) (𝓝 (0:Perturb G d)) (𝓝 1) := hp.2 ▸ hh
    filter_upwards [ht.eventually G.plog_right] with x hx; exact hx.symm
  filter_upwards [eventually_all.mpr hh] with x hx
  funext i; simp only [comp_apply,increment,Pi.one_apply,mul_one]; exact hx i

lemma enter_smul (w : MaskLog G d) (r : ℝ) (y : E4) :
    enter (r • w) y = r • enter w y := by simp [enter,Tensor.diagonal,Finset.smul_sum]

def tangent (H : Hol G) (o : Site n) := fderiv ℝ (surface H o) (0:Perturb G d)

private lemma rays {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {L : X→L[ℝ] Y} (h : HasFDerivAt f L 0) (v : X) :
    HasDerivAt (f ∘ (fun y : ℝ => y • v)) (L v) 0 ∧ Tendsto (fun y : ℝ => y • v) (𝓝 0) (𝓝 0) := by
  have he : HasDerivAt (fun y : ℝ => y • v) v 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v
  exact ⟨h.comp_hasDerivAt_of_eq 0 he (by simp),by simpa using he.continuousAt.tendsto⟩

set_option maxHeartbeats 600000 in
lemma identify (H : Hol G) (o x : Site n) (X : Support n) (h : Nonwrapping X o) (hn : 2 ≤ n.val)
    (hx : x∈X) (i : Axis) (p : Perturb G d) :
    let L := lift (x-o)
    let a := position L
    tangent H o p (x,i) = enter p.2 a + access p.1 (L,i) - enter p.2 (a+basis i) := by
  intro L a
  let z := enter p.2 a
  let z' := enter p.2 (a+basis i)
  let Z (t : ℝ) := visible H o (t • p) (x,i)
  let K (t : ℝ) := H.links d (expand d (t • p.1)) 1 (L,i)
  have he t : Z t=G.lieExp (t • z) * K t * (G.lieExp (t • z'))⁻¹ := by
    change G.lieExp (enter (t • p.2) a) * K t * (G.lieExp (enter (t • p.2) _))⁻¹ = _
    rw [enter_smul,enter_smul,lift_end hn h x hx,position_next]
  have hpow w : HasDerivAt (fun r : ℝ => G.mat (G.lieExp (r • w))) (G.colorMat w) 0 :=
    (G.expDiff_zero).comp_hasDerivAt_of_eq (f:=fun r : ℝ => r • w) 0 (by
      simpa using! (hasDerivAt_id' (0:ℝ)).smul_const w) (by simp)
  have ht := Work.G02.linkGerm H d (L,i)
  let M : Directions G n →L[ℝ] G.Color := ContinuousLinearMap.proj (x,i)
  let F (w) := M (surface (d:=d) H o w)
  let u (t : ℝ) := t • p
  let v := tangent H o p (x,i)
  have hh : HasFDerivAt F (M.comp (tangent (d:=d) H o)) 0 :=
    M.hasFDerivAt.comp 0 ((surface_diff H o).differentiableAt (by simp)).hasFDerivAt
  have hf : HasDerivAt (F ∘ u) v 0 := (@rays (Perturb G d) G.Color (inferInstanceAs (NormedAddCommGroup (Perturb G d))) (inferInstanceAs (NormedSpace ℝ (Snap G d × MaskLog G d))) _ _ _ _ hh p).1
  have hv : Tendsto u (𝓝 0) (𝓝 0) := (@rays (Perturb G d) G.Color (inferInstanceAs (NormedAddCommGroup (Perturb G d))) (inferInstanceAs (NormedSpace ℝ (Snap G d × MaskLog G d))) _ _ _ _ hh p).2
  have hg : HasDerivAt (fun t => G.mat (Z t)) (G.colorMat v) 0 := by
    apply (G.expDiff_zero.comp_hasDerivAt_of_eq 0 hf (by simp only [u, F, comp_apply, zero_smul, surface_zero,map_zero])).congr_of_eventuallyEq
    filter_upwards [hv.eventually (truly H o)] with t ht
    refine congr_arg G.mat ?_
    have he' := congr_fun ht (x,i); simp only [comp_apply, increment, Pi.one_apply,mul_one] at he'; exact he'
  have hK : HasDerivAt (fun t => G.mat (K t)) (G.colorMat (access p.1 (L,i))) 0 := ht.2.2 p.1
  have hA : HasDerivAt (fun t => G.mat (Z t)) (G.colorMat z+G.colorMat (access p.1 (L,i))-G.colorMat z') 0 := by
    simp_rw [he,G.mat_mul,G.mat_inv]
    apply (((hpow z).mul hK).mul (hpow z').star).congr_deriv
    have hZ : K 0 = 1 := by simp only [K,zero_smul]; exact ht.2.1
    simp [Pi.mul_apply,hZ,G.colorMat_skew,sub_eq_add_neg]; try rfl
  exact G.colorMat_injective (by rw [map_sub,map_add]; exact hg.unique hA)

end YM.Planned.AtomRegular.Flat
