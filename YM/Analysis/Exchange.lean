import YM.Analysis.Homogeneous

/-!
# Exchange of smooth homogeneous coefficients

Local on any open configuration set. Factors `j!` at both ends. Independent
of domains of convergence of any series. Useful also for word-norm proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Tensor
open Function Set Filter
open Analysis
open scoped Topology ContDiff

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {j l : ℕ} {f : E → F} {x : E}

theorem coeff_apply_zero (f : E → F) (x) (v : Fin 0 → E) : coeff f 0 x v = f x := by simp [coeff]

theorem coeff_apply_cons (h : ContDiffAt ℝ (↑(j+1 : ℕ)) f x) (v : E) (s : Fin j → E) :
    coeff f (j+1) x (Fin.cons v s) = ((↑(j+1 : ℕ) : ℝ))⁻¹ • coeff (D v f) j x s := by
  rw [coeff, coeff]; simp only [smul_apply, cons_inner h, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv]

theorem coeff_linear (L : F →L[ℝ] M) (u : Fin j → E) (h : ContDiffAt ℝ j f x) :
    coeff (L ∘ f) j x u = L (coeff f j x u) := by
  simp only [coeff, L.iteratedFDeriv_comp_left h le_rfl, smul_apply, map_smul]; rfl

theorem coeff_smul (t : ℝ) (h : ContDiffAt ℝ j f x) :
    coeff (t • f) j x = t • coeff f j x := by
  simp only [coeff, iteratedFDeriv_const_smul_apply h, smul_comm t]

/-- Exchange iterates on a smooth patch. -/
theorem exchangeJet {U : Set E} (hU : IsOpen U) (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) (hx : x ∈ U)
    (u : Fin j → E) (v : Fin l → E) :
    coeff (fun y => coeff f l y v) j x u = coeff (fun y => coeff f j y u) l x v := by
  have he (n : ℕ) : (↑n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  induction j generalizing f with
  | zero => simp [coeff_apply_zero]
  | succ j ih =>
    have Hu := Fin.cons_self_tail u
    -- head through the remaining right-jet directionals
    let a := u 0
    let r := Fin.tail u
    let L := ContinuousMultilinearMap.apply ℝ (fun _ => E) F v
    rw [← Hu]
    change coeff _ (j+1) x (Fin.cons a r) = _
    rw [coeff_apply_cons (show ContDiffAt ℝ (↑(j+1 : ℕ)) (fun y => coeff f l y v) x from
      (L.contDiff.contDiffAt.comp x (coeff_smooth (hf x hx) l)).of_le (he _))]
    let t := ((↑(j+1 : ℕ) : ℝ))⁻¹
    have hp : D a (fun y => coeff f l y v) =ᶠ[𝓝 x] fun y => coeff (D a f) l y v := by
      filter_upwards [hU.mem_nhds hx] with y hy
      change fderiv ℝ (L ∘ fun y => coeff f l y) y a = _
      rw [fderiv_comp y L.differentiableAt ((coeff_smooth (hf y hy) l).differentiableAt (by simp)), L.fderiv,
        ContinuousLinearMap.comp_apply]
      exact congr_arg L (D_coeff ((hf y hy).of_le (he _)) a)
    rw [GermCoeff j hp]
    have hs (y) (hy : y ∈ U) : ContDiffAt ℝ ∞ (D a f) y := dSmooth (hf y hy) _ (by simp)
    rw [ih hs r]
    have hw : (fun y => coeff f (j+1) y (Fin.cons (u 0) (Fin.tail u))) =ᶠ[𝓝 x]
        (t • fun y => coeff (D a f) j y r) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact coeff_apply_cons ((hf y hy).of_le (he _)) a r
    rw [GermCoeff l hw, coeff_smul t]
    · rfl
    exact (((ContinuousMultilinearMap.apply ℝ (fun _ => E) F r).contDiff.contDiffAt.comp x
      (coeff_smooth (hs x hx) j)).of_le (he _))

/-- Composition with negation is diagonal on jets. -/
theorem reflectionJet (hf : ContDiffAt ℝ j f (-x)) :
    coeff (fun y => f (-y)) j x = (-1 : ℝ)^j • coeff f j (-x) := by
  apply ContinuousMultilinearMap.ext
  intro u
  induction j generalizing f x with
  | zero => simp [coeff_apply_zero]
  | succ j ih =>
    let a := u 0
    let r := Fin.tail u
    have he := coeff_apply_cons (hf.comp x contDiffAt_id.neg) a r
    rw [← Fin.cons_self_tail u]
    change coeff (fun y => f (-y)) (j+1) x (Fin.cons a r) = _
    have hn : coeff (fun y => f (-y)) (j+1) x (Fin.cons a r) = ((↑(j+1 : ℕ) : ℝ))⁻¹ •
        coeff (D a fun y => f (-y)) j x r := he
    rw [hn, smul_apply, coeff_apply_cons hf]
    have hp : D a (fun y => f (-y)) =ᶠ[𝓝 x] -(fun y => D a f (-y)) := by
      have ht := hf.eventually (by simp)
      filter_upwards [(continuous_neg.continuousAt (x := x)).preimage_mem_nhds ht] with y hy
      let N := -(ContinuousLinearMap.id ℝ E)
      have hy' : ContDiffAt ℝ (↑(j+1 : ℕ)) f (-y) := hy
      change fderiv ℝ (f ∘ N) y _ = _
      rw [fderiv_comp y (show DifferentiableAt ℝ f (N y) from hy'.differentiableAt (by simp)) N.differentiableAt,
        N.fderiv]
      exact map_neg (fderiv ℝ f (-y)) a
    rw [GermCoeff j hp, neg_coeff, neg_apply, ih]
    · change _ = (-1 : ℝ)^(j+1) • (↑(j+1 : ℕ) : ℝ)⁻¹ • coeff (D a f) j (-x) r
      simp [pow_succ, smul_comm ((↑j+1 : ℝ))⁻¹]
    exact dSmooth hf a (by push_cast; rfl)

/-- Convert a mixed covariance in z=x−y to actual y derivatives. -/
theorem oppositeCoeff (x y : E) (hf : ContDiffAt ℝ j f (x-y)) :
    coeff (fun y' => f (x-y')) j y = (-1 : ℝ)^j • coeff f j (x-y) := by
  let L := fun y' => f (x+y')
  have he := reflectionJet (show ContDiffAt ℝ j L (-y) from
    (show ContDiffAt ℝ j f (x+-y) by simpa [sub_eq_add_neg] using hf).comp _ (contDiffAt_const.add contDiffAt_id))
  rw [show (fun y' => f (x-y')) = fun y' => L (-y') from funext fun i => by simp [L,sub_eq_add_neg], he]
  simp [L, coeff, sub_eq_add_neg, iteratedFDeriv_comp_add_left]

end YM.Tensor
