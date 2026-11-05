import YM.Extra.WILSON_STARTUP.Taylor
import YM.Next.FLUCTUATIONS.Charts
import YM.Next.FOUNDATIONS.LinkBounds
import YM.Work.F03.Flat

/-!
# Top Wilson matching in curvature coordinates

Then we only need a one-face analytic jet conversion.

Work at the identity of the actual closed matrix gauge image, which needn't be
connected.

Projection curvature as in `Gauge.curvature`; quadratic part fixed
with its true physical Frobenius denominator.

No expansions assumed of U near
a small **link** when making an estimate at a small **plaquette**.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter Work Tensor Next.Fluctuations
open scoped ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable (G : Gauge)

def localK (x : G.Color) : G.Color := G.curvature (G.lieExp x)

@[simp] theorem localK_zero : localK G 0 = 0 := by simp [localK]

theorem localK_analytic (x : G.Color) : ContDiffAt ℝ ω (localK G) x :=
  curvature_diff_mat _ _ G.exp_jet.contDiffAt

private abbrev tangent := ContinuousLinearEquiv.refl ℝ G.Color

theorem localK_derivative : HasFDerivAt (localK G) (ContinuousLinearMap.id ℝ G.Color) 0 := by
  have h := (localK_analytic G 0).differentiableAt (by simp)
  convert! h.hasFDerivAt using 1
  ext1 x
  exact (G.leading_curvature x).unique (YM.Push.side _ h x)

private abbrev coord : OpenPartialHomeomorph G.Color G.Color :=
  (localK_analytic G 0).toOpenPartialHomeomorph (f':=tangent G) _ (localK_derivative G) (by simp)

def undo : G.Color → G.Color := (coord G).symm

private theorem source_zero : (0:G.Color) ∈ (coord G).source := ContDiffAt.mem_toOpenPartialHomeomorph_source ..
private theorem target_zero : (0:G.Color) ∈ (coord G).target := by
  rw [← localK_zero G]; exact ContDiffAt.image_mem_toOpenPartialHomeomorph_target ..

theorem undo_left : ∀ᶠ x in 𝓝 (0 : G.Color), undo G (localK G x) = x := by
  filter_upwards [(coord G).open_source.mem_nhds (source_zero G)] with x hx
  exact (coord G).left_inv hx

theorem undo_right : ∀ᶠ x in 𝓝 (0 : G.Color), localK G (undo G x) = x := by
  filter_upwards [(coord G).open_target.mem_nhds (target_zero G)] with x hx
  exact (coord G).right_inv hx

@[simp] theorem undo_zero : undo G 0 = 0 := by simpa using (undo_left G).self_of_nhds

theorem undo_analytic : ContDiffAt ℝ ω (undo G) 0 := by
  rw [← localK_zero G]
  exact (localK_analytic G 0).to_localInverse (f':=tangent G) (localK_derivative G) (by simp)

theorem undo_derivative : HasFDerivAt (undo G) (ContinuousLinearMap.id ℝ G.Color) 0 := by
  rw [← localK_zero G]
  exact ((localK_analytic G 0).hasStrictFDerivAt' (localK_derivative G) (by simp)).to_localInverse
    (f':=tangent G) |>.hasFDerivAt

def recover (x : G.Color) := G.lieExp (undo G x)

@[simp] theorem recover_zero : recover G 0 = 1 := by simp [recover]
theorem recover_near : Tendsto (recover G) (𝓝 0) (𝓝 1) := recover_zero G ▸
  G.lieExp_cont.continuousAt.tendsto.comp (undo_analytic G).continuousAt.tendsto

theorem recover_right : ∀ᶠ x in 𝓝 (0 : G.Color), G.curvature (recover G x) = x := undo_right G

theorem recover_left : ∀ᶠ u : G.El in 𝓝 1, recover G (G.curvature u) = u := by
  have he := (G.plog_diff.continuousAt.comp (x:=1) G.continuous_mat.continuousAt).tendsto
  change Tendsto (fun u : G.El => G.plog (G.mat u)) (𝓝 1) (𝓝 (G.plog 1)) at he
  rw [G.plog_one] at he
  filter_upwards [G.plog_right, he.eventually (undo_left G)] with u hu hv
  unfold localK at hv
  unfold recover
  rw [hu] at hv; rw [hv,hu]

theorem recover_analytic : ContDiffAt ℝ ω (fun x => G.mat (recover G x)) 0 :=
  G.exp_jet.contDiffAt.comp _ (undo_analytic G)

theorem recover_derivative : HasFDerivAt (fun x => G.mat (recover G x)) G.colorMat.toContinuousLinearMap 0 := by
  have h := (show HasFDerivAt (fun x => G.mat (G.lieExp x)) _ (undo G 0) by rw [undo_zero]; exact G.expDiff_zero).comp
    (0:G.Color) (undo_derivative G)
  exact h

variable {G}

def inK (G : Gauge) (x : G.Color) := G.price (recover G x)

theorem inK_diff : ContDiffAt ℝ ω (inK G) 0 := F03.price_smooth (recover_analytic G)

theorem inK_conjugate (u : G.El) : ∀ᶠ x in 𝓝 (0 : G.Color), inK G (G.adjoint u x) = inK G x := by
  have he : Tendsto (fun x => u * recover G x * u⁻¹) (𝓝 0) (𝓝 1) := by
    simpa only [mul_one,mul_inv_cancel] using ((tendsto_const_nhds (x:=u)).mul (recover_near G)).mul
      (tendsto_const_nhds (x:=u⁻¹))
  filter_upwards [he.eventually (recover_left G), recover_right G] with x hx he
  unfold inK
  rw [G.curvature_conjugate, he] at hx
  rw [hx, G.price_conj]

theorem inK_even : ∀ᶠ x in 𝓝 (0 : G.Color), inK G (-x) = inK G x := by
  have he : Tendsto (fun x => (recover G x)⁻¹) (𝓝 0) (𝓝 1) := by
    simpa only [inv_one] using (recover_near G).inv
  filter_upwards [he.eventually (recover_left G), recover_right G] with x hx he
  unfold inK
  rw [G.curvature_inv, he] at hx
  rw [hx, G.price_inv]

theorem inK_low : inK G 0 = 0 ∧ fderiv ℝ (inK G) 0 = 0 ∧ ∀ x y,
    iteratedFDeriv ℝ 2 (inK G) 0 ![x,y] = inner ℝ x y := by
  refine F03.hessian_of_limit (inK_diff.of_le le_top) (fun x => ?_) inner_add_left (fun x y => real_inner_comm y x)
  rw [real_inner_self_eq_norm_sq]
  apply F03.price_limit (V := fun t : ℝ => recover G (t • x)) (by simp only [zero_smul,recover_zero])
  have ht : HasDerivAt (fun t : ℝ => t • x) x 0 := by
    simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x
  exact (show HasFDerivAt (fun x => G.mat (recover G x)) _ ((0:ℝ) • x) by simpa using recover_derivative G).comp_hasDerivAt 0 ht

theorem coeff_adjoint (u : G.El) (j : ℕ) (x : Fin j → G.Color) :
    coeff (inK G) j 0 (fun i => G.adjoint u (x i)) = coeff (inK G) j 0 x := by
  let L := (G.adjoint u).toContinuousLinearMap
  have h : inK G ∘ L =ᶠ[𝓝 0] inK G := inK_conjugate u
  have he := (h.iteratedFDeriv ℝ j).eq_of_nhds
  rw [Next.Foundations.jets_linear _ (inK_diff.of_le le_top)] at he
  unfold coeff
  simp only [smul_apply]
  exact congr_arg (_ • ·) (congr_arg (fun u : Tensor.T G.Color ℝ j => u x) he)

theorem odd_diagonal (x : G.Color) (j : ℕ) (hj : Odd j) : diagonal (coeff (inK G) j 0) x = 0 := by
  let L := -ContinuousLinearMap.id ℝ G.Color
  have h : inK G ∘ L =ᶠ[𝓝 0] inK G := inK_even
  have he := (h.iteratedFDeriv ℝ j).eq_of_nhds
  rw [Next.Foundations.jets_linear _ (inK_diff.of_le le_top)] at he
  let A := coeff (inK G) j 0
  have ht : diagonal A ((-1:ℝ) • x) = diagonal A x := by
    rw [neg_one_smul]
    unfold A diagonal coeff
    simp only [smul_apply]
    exact congr_arg (_ • ·) (congr_arg (fun u : Tensor.T G.Color ℝ j => u (fun _ => x)) he)
  rw [homogeneous, hj.neg_one_pow, neg_one_smul] at ht
  change - diagonal A x = diagonal A x at ht
  change diagonal A x = 0; linarith

def fourth (G : Gauge) := coeff (inK G) 4 0

theorem convert_taylor (x : G.Color) : G05.blockTaylor 4 (inK G) x = ‖x‖^2/2 + diagonal (fourth G) x := by
  obtain ⟨h₀,-,h₂⟩ := inK_low (G:=G)
  have hz : diagonal (coeff (inK G) 0 0) x = 0 := (coeff_apply_zero ..).trans h₀
  have hq : diagonal (coeff (inK G) 2 0) x = ‖x‖^2/2 := by
    unfold diagonal coeff
    have hv : (fun _ : Fin 2 => x) = ![x,x] := by funext i; fin_cases i <;> rfl
    rw [hv, smul_apply, h₂, real_inner_self_eq_norm_sq]
    norm_num; ring
  simp [G05.blockTaylor, Finset.sum_range_succ, hz, odd_diagonal x 1 (by decide), odd_diagonal x 3 (by decide),hq, fourth]

def surplus (u : G.El) := G.price u - ‖G.curvature u‖^2/2 - diagonal (fourth G) (G.curvature u)

theorem surplus_jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E → G.El)
    (h : u 0 = 1) (hm : ContDiffAt ℝ ω (fun v => G.mat (u v)) 0) : FlatAt 5 (surplus ∘ u) 0 := by
  have hc : ContinuousAt u 0 := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr hm.continuousAt
  let k := fun x => G.curvature (u x)
  have hz : k 0 = 0 := by simp only [k,h,G.curvature_unit]
  refine FlatAt.congr (g := surplus ∘ u)
    (FlatAt.comp (f:=inK G - G05.blockTaylor 4 (inK G)) (u:=k)
       (hz.symm ▸ flat_sub_taylor _ 4 (inK_diff.of_le le_top))
       (by rw [hz]; exact (inK_diff.of_le le_top).sub (G05.blockTaylor_contDiff .. |>.contDiffAt))
       ((curvature_diff_mat u 0 hm).of_le le_top)) ?_
  filter_upwards [(show Tendsto u (𝓝 0) (𝓝 1) from h ▸ hc.tendsto).eventually (recover_left G)] with x hx
  simp only [comp_apply, Pi.sub_apply, convert_taylor, inK,k,hx,surplus]; ring
end YM.WilsonStartup
