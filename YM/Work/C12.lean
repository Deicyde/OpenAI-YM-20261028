import YM.Analysis.Polydisc
import YM.Bid.Tar
import YM.Spark.Limit


/-!
# Damping on the closed shift set

On the whole topological support of `cut`, proximity to `coneM` controls every
frequency derivative of the exponential, uniformly for bounded closed shifts.
Use Leibniz bounds, and joint convergence of jets plus these bounds (in one
extra weight for each test seminorm, via `Spark.ready`) to work in Schwartz space.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C12
open Function Set Filter Boundary Analysis Distribution
open scoped Topology InnerProductSpace BigOperators ContDiff

section exp
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def damping (y x : E) := Complex.exp (-↑(inner ℝ y x) : ℂ)

lemma damping_joint : ContDiff ℝ ∞ (uncurry (damping (E := E))) :=
  Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp
    (contDiff_fst.inner ℝ contDiff_snd)).neg

lemma damping_contDiff (y : E) : ContDiff ℝ ∞ (damping y) :=
  damping_joint.comp (contDiff_const.prodMk contDiff_id)

lemma damping_estimate (y x : E) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (damping y) x‖ ≤ Real.exp (-inner ℝ y x) * ‖y‖ ^ i := by
  let L := -(innerSL ℝ y)
  have h : damping y = Complex.ofRealLI ∘ (Real.exp ∘ L) := by
    ext z : 1
    simp [L, damping, Complex.ofReal_exp]
  rw [h, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (Real.contDiff_exp.comp L.contDiff).contDiffAt (le_refl (↑i : ℕ∞ω)),
    L.iteratedFDeriv_comp_right Real.contDiff_exp x (le_refl (↑i : ℕ∞ω))]
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_of_nonneg (Real.exp_nonneg _), L, innerSL_apply_norm] using
      (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i Real.exp (L x)) (fun _ => L))
end exp

/-- Joint smoothness of the partial iterated derivative of a smooth family. -/
lemma contDiff_partialJets {E X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : E → X → Y} (hf : ContDiff ℝ ∞ (uncurry f)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × X => iteratedFDeriv ℝ j (f p.1) p.2) := by
  induction j with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ X Y).symm.toContinuousLinearEquiv.contDiff.comp hf
  | succ j IH =>
    simp_rw [iteratedFDeriv_succ_eq_comp_left]
    have h₂ : ContDiff ℝ ∞ (fun s : (E × X) × X => iteratedFDeriv ℝ j (f s.1.1) s.2) :=
      IH.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => X)
      Y).symm.toContinuousLinearEquiv.contDiff.comp
      (ContDiff.fderiv (n := ∞) (f := fun s : E × X => iteratedFDeriv ℝ j (f s.1)) h₂ contDiff_snd
        (by change ((↑((⊤ : ℕ∞) + 1) : ℕ∞ω) ≤ _); simp))

variable {n : ℕ}

lemma cone_estimate (h : Bid.Wide n) {y x : Points n} (hy : y ∈ shores n) (hx : x ∈ ShadeSet 3 n) :
    -inner ℝ y x ≤ 3 * ‖y‖ := by
  rcases hx with ⟨z, hz, hxz⟩
  have h₁ := h.rim z y hz hy
  rw [real_inner_comm] at h₁
  have h₂ : inner ℝ y (z - x) ≤ ‖y‖ * 3 := (real_inner_le_norm ..).trans
    (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm, dist_comm]; exact hxz.le) (norm_nonneg _))
  rw [inner_sub_right] at h₂
  linarith

lemma cut_temperate (A : Blanket n) : HasTemperateGrowth (fun x => (A.cut x : ℂ)) :=
  Complex.ofRealCLM.hasTemperateGrowth.comp A.uses

lemma attenuate_contDiff (A : Blanket n) : ContDiff ℝ ∞ (uncurry A.attenuate) :=
  damping_joint.mul ((cut_temperate A).1.comp contDiff_snd)

lemma attenuate_estimate (h : Bid.Wide n) (A : Blanket n) (R : ℝ) (hR : 0 ≤ R) (i : ℕ) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ shores n, ‖y‖ ≤ R → ∀ x,
      ‖iteratedFDeriv ℝ i (A.attenuate y) x‖ ≤ C * (1 + ‖x‖) ^ k := by
  obtain ⟨k, C, hC, hcut⟩ := (cut_temperate A).norm_iteratedFDeriv_le_uniform i
  refine ⟨k, ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * (Real.exp (3 * R) * R ^ l) * C,
    by positivity, fun y hy hyR x => ?_⟩
  by_cases hX : x ∈ tsupport A.cut
  · have h₁ (l : ℕ) : ‖iteratedFDeriv ℝ l (damping y) x‖ ≤ Real.exp (3 * R) * R ^ l := by
      apply (damping_estimate y x l).trans
      gcongr
      exact (cone_estimate h hy (A.supported hX)).trans (by gcongr)
    refine (norm_iteratedFDeriv_mul_le (damping_contDiff y) (cut_temperate A).1 x
      (mod_cast le_top)).trans ?_
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    rw [mul_assoc (_ * _ : ℝ) C]
    gcongr
    · exact h₁ j
    · exact hcut _ (Nat.sub_le i j) _
  have ht : tsupport (A.attenuate y) ⊆ tsupport A.cut := closure_mono (fun z hz => fun hc => hz (by
    change A.cut z = 0 at hc; simp [Blanket.attenuate, hc]))
  have hv : iteratedFDeriv ℝ i (A.attenuate y) x = 0 := by
    by_contra hx
    exact hX (ht (support_iteratedFDeriv_subset _ hx))
  rw [hv, norm_zero]
  positivity

lemma actual (h : Bid.Wide n) (A : Blanket n) {y : Points n} (hy : y ∈ shores n) :
    HasTemperateGrowth (A.attenuate y) := by
  refine ⟨?_, fun i => ?_⟩
  · exact (damping_contDiff y).mul (cut_temperate A).1
  obtain ⟨k, C, _, H⟩ := attenuate_estimate h A ‖y‖ (norm_nonneg _) i
  exact ⟨k, C, H y hy le_rfl⟩

lemma diffuser_eq (h : Bid.Wide n) (A : Blanket n) {y : Points n} (hy : y ∈ shores n)
    (f : Joint n) : ⇑(A.diffuser y f) = fun x => A.attenuate y x * f x :=
  SchwartzMap.smulLeftCLM_apply (actual h A hy) f

lemma diffuser_estimate (h : Bid.Wide n) (A : Blanket n) (R : ℝ) (hR : 0 ≤ R)
    (f : Joint n) (i j : ℕ) :
    ∃ C : ℝ, ∀ y ∈ shores n, ‖y‖ ≤ R → Probe.size i j (A.diffuser y f) ≤ C := by
  choose k C hC hA using (attenuate_estimate h A R hR)
  let B (l : ℕ) := 2 ^ (k l + i) * (Finset.Iic (k l + i, j - l)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f
  have hB (l : ℕ) (x : Points n) :
      (1 + ‖x‖) ^ (k l + i) * ‖iteratedFDeriv ℝ (j - l) f x‖ ≤ B l :=
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k l + i, j - l)) le_rfl le_rfl f x
  have hpos (l : ℕ) : 0 ≤ B l := (show 0 ≤ _ * ‖_‖ from mul_nonneg (by positivity)
    (norm_nonneg _)).trans (hB l 0)
  refine ⟨∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * C l * B l, fun y hy hyR => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℂ _ _ _
    (Finset.sum_nonneg (fun l _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC l)) (hpos l)))
    (fun x => ?_)
  rw [diffuser_eq h A hy]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (actual h A hy).1
      (f.smooth ⊤) x (mod_cast le_top)) (by positivity))
  rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun l _ => ?_)
  calc
    _ ≤ (1 + ‖x‖)^i * ((j.choose l : ℝ) * (C l * (1 + ‖x‖)^(k l)) *
        ‖iteratedFDeriv ℝ (j-l) f x‖) := by
      gcongr
      · linarith
      · exact hA _ _ hy hyR x
    _ = (j.choose l : ℝ)*C l*((1 + ‖x‖)^(k l + i) * ‖iteratedFDeriv ℝ (j-l) f x‖) := by
      rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB l x) (by have := hC l; positivity)

theorem answer : YM.Bid.C12 := by
  intro n h A
  refine ⟨fun _ hy => actual h A hy, fun f y hy => ?_⟩
  apply Spark.ready
  · intro j x
    simp_rw [Spark.Jet]
    rw [diffuser_eq h A hy]
    let G (z : Points n) (p : Points n) := A.attenuate z p * f p
    have hG : ContDiff ℝ ∞ (uncurry G) :=
      (attenuate_contDiff A).mul ((f.smooth ⊤).comp contDiff_snd)
    refine (((contDiff_partialJets hG j).continuous.tendsto (y,x)).mono_left ?_).congr' ?_
    · rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin (a := y) (s := shores n))] with s hs
    rw [diffuser_eq h A hs]
  obtain ⟨R, hR⟩ := exists_gt ‖y‖
  intro i j
  obtain ⟨C, hC⟩ := diffuser_estimate h A R ((norm_nonneg _).trans hR.le) f i j
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    continuous_norm.continuousWithinAt.tendsto.eventually (gt_mem_nhds hR)] with z hz hzR using hC z hz hzR.le

-- Empty word check, not taking either positivity or a cutoff as a premise here.
example : ∃ A : Blanket 0, A.Modified := by
  have h : Bid.Wide 0 := by
    constructor
    · intro p y _ _; rw [Subsingleton.elim p 0, inner_zero_left]
    · intro y _
      exact ⟨1, by norm_num, Eventually.of_forall fun u p _ => by simp [Subsingleton.elim p 0]⟩
  have hs (x : Points 0) : x ∈ ShadeSet 3 0 :=
    ⟨0, pit 0, by rw [Subsingleton.elim x 0]; norm_num⟩
  let A : Blanket 0 := ⟨fun _ => 1, HasTemperateGrowth.const _, fun _ _ => rfl, fun x _ => hs x⟩
  exact ⟨A, answer 0 h A⟩

end YM.Work.C12
