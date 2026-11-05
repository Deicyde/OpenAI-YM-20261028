import YM.Push.LOCAL_SPLITTING.Raw

/-!
# Log-coordinate identity tests before canonical extraction

A kernel-side sufficient estimate for the coordinate error (cf. ).
Use arbitrary C^d models in coarse log coordinates; need NOT be actual
gauge invariant sources (the flat rule by itself need not be one), and not
used to define the readout. This estimate can be much sharper than applying
the regular-component bill to all primary coordinates. Tests only at the
identity, along normalized actual log-link variations. Constants chosen
before the side/block. No independent reoptimization of readout for a test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

def tests (F : Labels.Frame G d) : Finset (Probe G d) := (probe_budget F).choose
def testPrice (F : Labels.Frame G d) := (probe_budget F).choose_spec.choose

def logSample (A : Hol G) (o : Site n) (X : Support n) (θ : ℝ) (g : Directions G n → ℂ) (p : Probe G d) :=
  if Nonwrapping X o then iteratedDeriv p.2.val (g ∘ testLog A d o (θ • p.1)) 0 else if p.2.val = 0 then g 0 else 0

/-- Raw comparison on one atom, before multiplying by the exponential and
before subtracting any canonical coordinates. Zeroth order required, also on
wrapping supports. Higher variations can be restricted to those used by the
logarithmic-link chain rule and still suffice (stronger e.g. full position
directions bound allowed, but *not necessary* here). -/
structure IdentityTest (A : Hol G) (o : Site n) (X : Support n) (B : BudgetPoint) (f : Config G n → ℂ)
    (g : Directions G n → ℂ) (p : Probe G d) (c : ℝ) : Prop where
  value : ‖f 1 - g 0‖ ≤ c
  smooth : Nonwrapping X o → ContDiffAt ℝ (d : WithTop ℕ∞) g 0
  close : Nonwrapping X o → ∀ m : ℕ, m ≤ d → ∀ w : Fin m → Directions G n,
    (∀ i, B.dirBound o (w i) ∧ ∃ k ≤ d, ∃ z : ℝ, w i = z • iteratedDeriv k (testLog A d o (B.threshold • p.1)) 0) →
      ‖iteratedFDeriv ℝ m (f ∘ increment 1) 0 w - iteratedFDeriv ℝ m g 0 w‖ ≤ c

def logPrice (A : Hol G) (p : Probe G d) (i : ℕ) := (testLog_bound A d i p.1).choose

def partPrice (A : Hol G) (p : Probe G d) := 1 + ∑ q : OrderedFinpartition p.2.val, ∏ i, logPrice A p (q.partSize i)

theorem logPrice_pos (A : Hol G) (p : Probe G d) (i : ℕ) : 0 < logPrice A p i := (testLog_bound A d i p.1).choose_spec.1

theorem partPrice_pos (A : Hol G) (p : Probe G d) : 1 ≤ partPrice A p :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => (logPrice_pos A p _).le)

theorem compareSample {A : Hol G} {o : Site n} {X : Support n} {B : BudgetPoint} {f : Config G n → ℂ}
    {g : Directions G n → ℂ} {p : Probe G d} {c : ℝ} (hf : B.Regular X f) (hk : d ≤ B.order) (hP : d ≤ B.power)
    (h : IdentityTest A o X B f g p c) : ‖sample A o X B.threshold f p - logSample A o X B.threshold g p‖ ≤ partPrice A p * c := by
  let Z := testLog A d o (B.threshold • p.1)
  let f₀ := f ∘ increment (1 : Config G n)
  have hc := (norm_nonneg _).trans h.value
  unfold sample logSample; split <;> rename_i hx
  · rw [(show f ∘ A.testLinks d o (B.threshold • p.1) =ᶠ[𝓝 0] f₀ ∘ Z from (increment_testLog ..).fun_comp f).iteratedDeriv_eq]
    have h0 : Z 0 = 0 := testLog_zero ..
    have hf' : Chart d f 1 := (hf.smooth 1 (one_healthy X _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr hk)
    have hd : ContDiffAt ℝ (d : WithTop ℕ∞) Z 0 := (testLog_diff ..).of_le le_top
    have hi : (p.2.val : WithTop ℕ∞) ≤ (d : WithTop ℕ∞) := Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt)
    rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (g:=f₀) (h0.symm ▸ hf') hd hi, iteratedDeriv_vcomp_eq_sum_orderedFinpartition (h0.symm ▸ h.smooth hx) hd hi, ← Finset.sum_sub_distrib, h0]
    unfold partPrice; rw [add_mul,Finset.sum_mul]; apply le_trans _ (le_add_of_nonneg_left (by positivity : 0 ≤ 1*c))
    apply (norm_sum_le ..).trans
    refine Finset.sum_le_sum fun q _ => ?_
    let C (i : Fin q.length) := logPrice A p (q.partSize i)
    have hC (i) : 0 < C i := logPrice_pos ..
    let w (i : Fin q.length) := (C i)⁻¹ • iteratedDeriv (q.partSize i) Z 0
    have he (i) : q.partSize i ≤ d := (q.partSize_le i).trans (Nat.le_of_lt_succ p.2.isLt)
    have hw i : B.dirBound o (w i) := by
      intro l; let y : ℝ := 1+separation l.1 o
      have hh := (testLog_bound A d (q.partSize i) p.1).choose_spec.2 n o l _ B.threshold_pos.le B.threshold_le
      change ‖(C i)⁻¹ • iteratedDeriv (q.partSize i) Z 0 l‖ ≤ _
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (hC i)).le]
      calc
        _ ≤ (C i)⁻¹ * (C i*B.threshold*y^(q.partSize i-1)) := mul_le_mul_of_nonneg_left hh (inv_pos.mpr (hC i)).le
        _ = B.threshold*y^(q.partSize i-1) := by field_simp [(hC i).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp [y]) (by have := he i; omega : q.partSize i-1 ≤ B.power)) B.threshold_pos.le
    have hprod : 0 ≤ ∏ i, C i := Finset.prod_nonneg fun i _ => (hC i).le
    rw [show (fun i => iteratedDeriv (q.partSize i) Z 0) = fun i => C i • w i from funext fun i => by simp [w,smul_smul,(hC i).ne'], ContinuousMultilinearMap.map_smul_univ,(iteratedFDeriv ℝ q.length g 0).map_smul_univ C w, ← smul_sub,norm_smul,Real.norm_of_nonneg hprod]
    exact mul_le_mul_of_nonneg_left (h.close hx _ (q.length_le.trans (Nat.le_of_lt_succ p.2.isLt)) w (fun i => ⟨hw i,_,he i,_,rfl⟩)) hprod
  split
  · exact h.value.trans (le_mul_of_one_le_left hc (partPrice_pos ..))
  simpa using (mul_nonneg (zero_le_one.trans (partPrice_pos A p)) hc)

def errorPrice (A : Hol G) (F : Labels.Frame G d) := testPrice F * (1+∑ p∈tests F,partPrice A p)

theorem errorPrice_pos (A : Hol G) (F : Labels.Frame G d) : 1 ≤ errorPrice A F :=
  one_le_mul_of_one_le_of_one_le (probe_budget F).choose_spec.choose_spec.1 (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (partPrice_pos A i)))

/-- Models can treat principal, secondary and unit parts separately. In
applications their reproduction is itself a calculation on the linearized
flat stationary column (not a law of the measured RG map). No summability
loss by cancellations in the error certificates. Uses the same budget and
test weight `B.threshold`. -/
structure Models (A : Hol G) (o : Site n) (X : ℕ → Support n) (B : BudgetPoint) (M : Raw F n)
    (y : F.Coeff) (ε : ℝ) (g : ℕ → Directions G n → ℂ) : Prop where
  reproduces (p) : p ∈ tests F → HasSum (fun j => logSample A o (X j) B.threshold (g j) p) (runProbe F p (y - M.seed))
  estimates (p) : p ∈ tests F → ∃ e : ℕ → ℝ, SumBudget e ε ∧ ∀ j, IdentityTest A o (X j) B (M.bulk j) (g j) p (e j)

theorem compareModels {R : Rep G n} {A : Hol G} {T : SectionData F} {o : Site n} {X : ℕ → Support n} {w ε : ℝ} {g : ℕ → Directions G n → ℂ} {M : Raw F n} {y : F.Coeff}
    (S : Slots R.activities (fun i => joint T o (X i))) (hr : Readable A T R.p n w) (hf : M.Format o X R)
    (hs : Summable (M.row o X A R.p.threshold)) (hp : 0 ≤ ε) (h : Models A o X R.p M y ε g) :
    F.coeffSize ((M.build o X A T R S).x-y) ≤ errorPrice A F * ε := by
  unfold errorPrice; rw [mul_assoc]
  have hc p := zero_le_one.trans (partPrice_pos A (p : Probe G d))
  apply (probe_budget F).choose_spec.choose_spec.2 _ _ (mul_nonneg (by linarith [Finset.sum_nonneg (s:=tests F) (fun i _ => hc i)]) hp)
  intro p hq
  obtain ⟨e,he,hE⟩ := h.estimates p hq
  let D i := sample A o (X i) R.p.threshold (M.bulk i) p - logSample A o (X i) R.p.threshold (g i) p
  have hz : SumBudget (fun i => ‖D i‖) (partPrice A p * ε) := sumBudget_mono (sumBudget_mul_left he (hc p)) (fun _ => norm_nonneg _) (fun i => compareSample (hf.regular i) hr.order hr.power (hE i)) le_rfl
  have hsum := hz.2.1.of_norm.hasSum.add (h.reproduces p hq)
  simp only [D,sub_add_cancel] at hsum
  rw [map_sub,Raw.build_samples S hr hf hs,hsum.tsum_eq,map_sub,show ∀ x y z : ℂ, x+(y+(z-x))-z=y by intros; ring]
  exact ((norm_tsum_le_tsum_norm hz.2.1).trans hz.2.2).trans (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun i _ => hc i) hq).trans (le_add_of_nonneg_left zero_le_one)) hp)
end YM.Push.Local
