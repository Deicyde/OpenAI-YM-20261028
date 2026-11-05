import YM.TraceExtension.PolynomialGrowth

/-!
# Absolute- and relative-variable Fourier identities

The ordered boundary, including on joint tests crossing the null cone, is
represented by the *same* spectral measure. Use the plus convention because
the right insertion is at `+X`. No puncturing of the origin of spacetime. No
statement about a Euclidean contact extension here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral OS
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace

section fourier
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def testPlus : Probe V →L[ℂ] Probe V := (↑(Probe.pref V):ℂ) • Probe.port
lemma testPlus_apply (f : Probe V) (p : V) : testPlus f p = ∫ x, Probe.plane x p * f x := by
  change ((Probe.pref V:ℝ):ℂ) • Probe.port f p = _
  rw [Probe.port_eq]
  have hp : Probe.pref V ≠ 0 := Probe.prepos.ne'
  rw [← Complex.coe_smul, smul_smul,← Complex.ofReal_mul,mul_inv_cancel₀ hp,Complex.ofReal_one,one_smul]

/-- A relative distribution in one variable. -/
def relative (μ : Measure V) [μ.HasTemperateGrowth] : Distn V :=
    (SchwartzMap.integralCLM ℂ μ).comp testPlus
lemma relative_apply (μ : Measure V) [μ.HasTemperateGrowth] (f : Probe V) :
    relative μ f= ∫ p,testPlus f p ∂μ := rfl
end fourier

def relativeLeg : E4 →L[ℝ] Points 2 := LinearMap.toContinuousLinearMap
  { toFun := fun p : E4 => points ![-p,p]
    map_add' := fun x y => by ext1 i; fin_cases i <;> simp [add_comm]
    map_smul' := fun t x => by ext1 i; fin_cases i <;> simp }
@[simp] lemma relativeLeg_zero (p : E4) : relativeLeg p 0= -p := rfl
@[simp] lemma relativeLeg_one (p : E4) : relativeLeg p 1=p := rfl

def legTest : Joint 2 →L[ℂ] Probe E4 := SchwartzMap.compCLM ℂ relativeLeg.hasTemperateGrowth
    (⟨1,1,fun x => by
       simp only [pow_one,one_mul]
       refine le_trans ?_ (le_add_of_nonneg_left zero_le_one)
       calc _ = ‖relativeLeg x 1‖ := by simp
            _ ≤ _ := PiLp.norm_apply_le ..⟩)

@[simp] lemma legTest_apply (f : Joint 2) (p : E4) : legTest f p=f (relativeLeg p) := rfl
lemma leg_plane (y : Points 2) (p : E4) : Probe.plane y (relativeLeg p) = Probe.plane p (y 1 - y 0) := by
    rw [Probe.plane_dot y,Probe.plane,Probe.plane,PiLp.inner_apply,Fin.sum_univ_two,relativeLeg_zero,relativeLeg_one, inner_neg_left, inner_sub_right]; ring_nf

def waveTest : Joint 2 →L[ℂ] Probe E4 := legTest.comp testPlus
lemma waveTest_apply (f : Joint 2) (p : E4) : waveTest f p = ∫ x, Probe.plane p (x 1-x 0)* f x := by
    change testPlus f _ = _; rw [testPlus_apply]; simp_rw [leg_plane]

variable {G : Gauge} {L : Register G} {S T : Table L} {C : Chamber T timeAxis}
  {F : Waves S} {B : Small S C} {J : StarOp S} {W : Surface S}

lemma surface_integral (h : Bid.Hull B F J) (hm : F.Breathes) (he : F.Opens W)
    (v : S.Union) (f : Joint 2) :
    W.W 2 (pairV J v) f = ∫ p, waveTest f p ∂ spectralMeasure B v := by
    let μ := spectralMeasure B v
    haveI ht : μ.HasTemperateGrowth := spectral_temperate h hm v
    have hk (s : ℝ≥0) (hs : 0<s) :
        F.atSlopes (pairV J v) (pairH 1) s f =
          ∫ p, Real.exp (-(2*(s:ℝ))*time p) • waveTest f p ∂μ := by
      let ρ := C.flow.ℚmeasure.diagonal (pointState B v s)
      haveI : IsFiniteMeasure ρ := PVM.finite ..
      have hp : (∫ p, waveTest f p ∂ρ) = ∫ p, Real.exp (-(2*(s:ℝ))*time p) • waveTest f p ∂μ := by
        rw [show ρ= OS.Semigroup.transform timeAxis (2*(s:ℝ)) μ from (damp h v s hs).symm, OS.Semigroup.transform, integral_withDensity_eq_integral_smul (OS.Semigroup.measurable ..)]; rfl
      rw [← hp]; unfold Waves.atSlopes
      rw [show (s:ℝ) • pairH 1=pairH s by funext i; fin_cases i <;> simp]
      have hh (x : Points 2) : F.restricted (pairV J v) (pairH s) x * f x = ∫ p, Probe.plane p (x 1-x 0)* f x ∂ρ := by
        rw [integral_mul_const,pair_restricted h v s hs,charFun_apply]; rfl
      simp_rw [hh,waveTest_apply]
      rw [integral_integral_swap]
      let A := fun x : Points 2 × E4 => Probe.plane x.2 (x.1 1-x.1 0)* f x.1
      apply (f.integrable.norm.comp_fst (ν:=ρ)).mono
      · exact (show Continuous A from by unfold A Probe.plane; fun_prop).aestronglyMeasurable
      change ∀ᵐ x ∂_, ‖A x‖ ≤ ‖‖f x.1‖‖
      filter_upwards with x; simp [A]
    apply tendsto_nhds_unique (he.profile 2 (pairV J v) (pairH 1) (east_pairH one_pos) f)
    let Y : ℝ → E4 → ℂ := fun r p => Real.exp (-(2*r)*time p) • waveTest f p
    have hh : Tendsto (fun r => ∫ p,Y r p ∂μ) (𝓝[>] (0:ℝ)) (𝓝 (∫ p, waveTest f p ∂μ)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun p => ‖waveTest f p‖)
      · exact Eventually.of_forall fun r => (show Continuous (Y r) from by unfold Y; fun_prop).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with r hr
        filter_upwards [ae_time (B:=B) v] with p hp
        dsimp only [Y]
        rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_of_le_one_left (norm_nonneg _)
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by have hx : 0 < r := hr; linarith) hp)
      · exact (waveTest f).integrable.norm
      filter_upwards with p
      simpa [Y] using (((show Continuous fun r => Y r p from by unfold Y; fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ))))
    refine hh.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    exact (hk ⟨r,hr.le⟩ hr).symm

/-- Absolute distribution as integral of relative plane waves with displacement
argument `x₁ - x₀`, showing W is the pullback of `relative μ`. -/
theorem pull_relative (h : Bid.Hull B F J) (hm : F.Breathes) (he : F.Opens W)
    (v : S.Union) (f : Joint 2) :
    W.W 2 (pairV J v) f = ∫ p, (∫ x, Probe.plane p (x 1-x 0)* f x) ∂spectralMeasure B v := by
    rw [surface_integral h hm he]; simp_rw [waveTest_apply]
end YM.TraceExtension
