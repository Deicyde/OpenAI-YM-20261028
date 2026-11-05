import YM.Extra.WEAK_SCALING_ACTLAW.Cube

/-!
# Low-order group invariants in the given faithful physical colors

Use actual Lie exponentials and simplicity on the actual image algebra. No
assertion here about noncollapse of labels in a quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Filter Set Function NormedSpace Gauge
open scoped Matrix.Norms.Frobenius Topology InnerProductSpace
variable {G : Gauge}

theorem tangent (x y : G.Color) : HasDerivAt (fun t : ℝ => G.adjoint (G.lieExp (t • x)) y) (G.ad x y) 0 := by
  let u := fun t : ℝ => exp (t • G.colorMat x)
  have he : HasDerivAt u (G.colorMat x) 0 := by simpa [u] using! hasDerivAt_exp_smul_const (G.colorMat x) (0:ℝ)
  have hf := (he.mul_const (G.colorMat y)).mul he.star
  have h : HasDerivAt (fun t : ℝ => G.colorMat (G.adjoint (G.lieExp (t • x)) y)) (G.colorMat (G.ad x y)) 0 := by
    simpa [u,Gauge.conjugate,map_smul, colorMat_skew,sub_eq_add_neg] using! hf
  have ht := G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) h
  change HasDerivAt (fun t : ℝ => G.projectColor (G.colorMat _)) (G.projectColor (G.colorMat _)) _ at ht
  simpa only [G.project_colorMat] using! ht

theorem commutators (h : G.Simple) : Submodule.span ℝ (range fun p : G.Color × G.Color => G.ad p.1 p.2) = ⊤ := by
  let V := Submodule.span ℝ (range fun p : G.Color × G.Color => G.ad p.1 p.2)
  have he (x y : G.Color) : G.ad x y ∈ V := Submodule.subset_span (mem_range_self (x,y))
  obtain ⟨x,y,hxy⟩ := h.nonabelian
  exact (h.ideals V (fun x y _ => he x y)).resolve_left (fun e => hxy ((Submodule.mem_bot ℝ).mp (e ▸ he x y)))

theorem linear_invariant (h : G.Simple) (p : G.Color →ₗ[ℝ] ℂ)
    (hp : ∀ g y, p (G.adjoint g y) = p y) (x : G.Color) : p x = 0 := by
  suffices he : LinearMap.ker p = ⊤ from LinearMap.mem_ker.mp (he ▸ Submodule.mem_top)
  rw [eq_top_iff,← commutators h,Submodule.span_le]
  rintro _ ⟨⟨y,z⟩,rfl⟩
  have ht := p.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) (tangent y z)
  rw [LinearMap.coe_toContinuousLinearMap',comp_def] at ht
  simp only [hp] at ht
  exact ht.unique (hasDerivAt_const (0:ℝ) _)

theorem adInvariant (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (h : ∀ g x y, B (G.adjoint g x) (G.adjoint g y)=B x y) (x y z : G.Color) : B (G.ad x y) z = - B y (G.ad x z) := by
  let L := (LinearMap.toContinuousLinearMap.toLinearMap.comp B).toContinuousLinearMap
  have ht := (L.hasFDerivAt.comp_hasDerivAt 0 (tangent x y)).clm_apply (tangent x z)
  have hh : HasDerivAt (fun t : ℝ => B y z) (B (G.ad x y) z + B y (G.ad x z)) 0 := by
    have h0 (p : G.Color) : G.adjoint (G.lieExp ((0:ℝ) • x)) p = p := G.colorMat_injective (by simp)
    change HasDerivAt (fun t : ℝ => B (G.adjoint (G.lieExp (t • x)) y) _) (B _ _ + B _ _) _ at ht
    simpa only [h,h0] using ht
  exact eq_neg_of_add_eq_zero_left (hh.unique (hasDerivAt_const ..))

theorem ad_skew (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hB : ∀ x y, B x y= -B y x) (he : ∀ x y z, B (G.ad x y) z = - B y (G.ad x z)) (x y : G.Color) : B x y=0 := by
  have hA (x y : G.Color) : G.ad x y = -G.ad y x := G.colorMat_injective (by simp)
  have ht (i j k : G.Color) : B (G.ad i j) k = B (G.ad i k) j := (he ..).trans (hB ..).symm
  have h0 (i j k : G.Color) : B (G.ad i j) k = 0 := by
    have heq : B (G.ad i j) k = -B (G.ad i j) k := by
      conv_lhs => rw [ht i j k,hA i k,map_neg,LinearMap.neg_apply,ht k i j,hA k j,map_neg,LinearMap.neg_apply,ht j k i,hA j i,map_neg,LinearMap.neg_apply,neg_neg]
    linarith
  suffices hz : LinearMap.ker B = ⊤ from LinearMap.congr_fun (LinearMap.mem_ker.mp (hz ▸ Submodule.mem_top)) y
  rw [eq_top_iff,← commutators h,Submodule.span_le]
  rintro _ ⟨⟨i,j⟩,rfl⟩; exact LinearMap.ext (h0 i j)

theorem real_invariant (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ)
    (hB : ∀ g x y, B (G.adjoint g x) (G.adjoint g y)=B x y) : ∃ c : ℝ, ∀ x y, B x y = c * inner ℝ x y := by
  have ht := adInvariant B hB
  apply invariant_scalar h _ _ ht
  intro x y; apply sub_eq_zero.mp
  refine ad_skew h (B - B.flip) (fun i j => by simp) (fun i j k => ?_) x y
  change B _ _-B _ _=-(B _ _-B _ _)
  rw [ht,← neg_eq_iff_eq_neg.mpr (ht i k j)]; abel

theorem bilinear_invariant (h : G.Simple) (B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℂ)
    (hB : ∀ g x y, B (G.adjoint g x) (G.adjoint g y)=B x y) : ∃ c : ℂ, ∀ x y, B x y = (inner ℝ x y) • c := by
  have ht (p : ℂ →ₗ[ℝ] ℝ) := real_invariant h (B.compr₂ p) (fun g i j => congrArg p (hB g i j))
  obtain ⟨c,hc⟩ := ht Complex.reCLM.toLinearMap
  obtain ⟨d,hd⟩ := ht Complex.imCLM.toLinearMap
  refine ⟨⟨c,d⟩,fun i j => Complex.ext ((hc i j).trans ?_) ((hd i j).trans ?_)⟩ <;> simp [mul_comm]
end YM.Extra.WeakScaling.Color
