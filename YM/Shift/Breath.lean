import YM.Shift.Ridge

/-!
# Exact Taylor along real heights. Use *tested* repeated 1-direction lifts.
No bound on unscaled derivatives of distributions at the edge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary.Waves
open Filter Set Function MeasureTheory Probe Complex
open scoped Topology InnerProductSpace ContDiff BigOperators Interval ENNReal
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ} (F : Waves S)

def moves : (k : ℕ) → Joint n →L[ℂ] Joint n
  | 0 => ContinuousLinearMap.id ℂ _
  | k+1 => (clock (rate n)).comp (moves k)

def rocks (v : Fin n → S.Union) (y : Heights n) (f : Joint n) (t : ℝ) (k : ℕ) := F.psi v (y+t • rate n) (moves k f)

def coal (t : ℝ) (m : ℕ) := (-↑t : ℂ)^m*(m.factorial:ℂ)⁻¹

def pol (v : Fin n → S.Union) (y : Heights n) (f : Joint n) (t : ℝ) (m : ℕ) :=
    ∑ k ∈ Finset.range (m+1), coal t k * F.rocks v y f t k

def wind (v : Fin n → S.Union) (m : ℕ) (y : Heights n) (f : Joint n) (t : ℝ) := coal t m * F.rocks v y f t (m+1)

def desired (v : Fin n → S.Union) (m : ℕ) (y : Heights n) (f : Joint n) := F.pol v y f 1 m -∫ s : ℝ in Ioc 0 1,
    F.wind v m y f s

private lemma pipe (t : ℝ) (m : ℕ) : HasDerivAt (fun t : ℝ => coal t (m+1)) (-coal t m) t := by
  have he := (Complex.ofRealCLM.hasDerivAt (x:=t)).neg.pow (m+1) |>.mul_const ((m+1).factorial:ℂ)⁻¹
  apply he.congr_deriv
  unfold coal
  have hp : (m.factorial:ℂ)≠0 := by norm_cast; exact Nat.factorial_ne_zero _
  have hv : (m:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv]
  push_cast; simp only [Pi.neg_apply, ofRealCLM_apply,ofReal_one]
  field_simp

lemma right (h : F.Lines) (v : Fin n → S.Union) (y : Heights n) (f : Joint n) (m : ℕ) (x : ℝ)
    (p : y+x • rate n∈east n) : HasDerivAt (fun t => F.pol v y f t m) (F.wind v m y f x) x := by
  have H (k) : HasDerivAt (fun t => F.rocks v y f t k) (F.rocks v y f x (k+1)) x := h n v (moves k f) y _ x p
  induction m with
  | zero => simpa [wind,pol,coal] using! H 0
  | succ m IH =>
    have ht := IH.add ((pipe x m).mul (H (m+1)))
    simp_rw [show (fun t => F.pol v y f t (m+1))= (fun t => F.pol v y f t m+coal t (m+1)*F.rocks v y f t (m+1)) from funext fun t => Finset.sum_range_succ (fun k ↦ coal t k*_) _]
    apply ht.congr_deriv; unfold wind; ring

theorem meant (ha : F.Along) (h : F.Lines) (v : Fin n → S.Union) (y : Heights n) (hy : y∈east n)
    (f : Joint n) (m : ℕ) : F.desired v m y f= F.psi v y f := by
  unfold desired
  have he (x : ℝ) (hx : x ∈ uIcc (0:ℝ) 1) : y+x • rate n∈east n := grows hy (by rw [uIcc_of_le zero_le_one] at hx; exact hx.1)
  have ht : F.pol v y f 0 m= F.psi v y f := by
    unfold pol
    rw [Finset.sum_eq_single_of_mem 0 (by simp)]
    · simp [coal,rocks,moves]
    intro b _ hb; simp [coal,zero_pow hb]
  rw [← intervalIntegral.integral_of_le (a:=(0:ℝ)) (b:=1) zero_le_one, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => F.right h v y f m x (he x hx)), ht]; swap
  · have hh : ContinuousOn (F.wind v m y f) (uIcc (0:ℝ) 1) := by
      unfold wind; apply ContinuousOn.mul
      · unfold coal; fun_prop
      exact (ha n v _).comp (show ContinuousOn (fun t : ℝ => y+t • rate n) _ from by fun_prop) he
    exact hh.intervalIntegrable
  abel

lemma expense {v : Fin n → S.Union} (m : ℕ) {C : ℝ}
    (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)
    (y : Heights n) (hy : y∈sunrise n) (f : Joint n) {t : ℝ} (hr : t∈Ioc (0:ℝ) 1) :
    ‖F.wind v m y f t‖ ≤ C*weight (moves (m+1) f) := by
  have hF : ‖(m.factorial:ℂ)‖ = (m.factorial:ℝ) := by exact Complex.norm_natCast _
  have he : ((m.factorial:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos m)
  rw [wind,norm_mul,coal,norm_mul, Complex.norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr.1.le, norm_inv,hF]
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg hr.1.le m) he) (norm_nonneg _))
    (beam F m C hm hy (moves (m+1) f) hr)

theorem maintains (v : Fin n → S.Union) (ha : F.Along) (m : ℕ) {C : ℝ}
    (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)
    (f : Joint n) : ContinuousOn (fun y => F.desired v m y f) (sunrise n) := by
  intro s hs
  unfold desired
  apply ContinuousWithinAt.sub
  · apply ContinuousOn.continuousWithinAt (s:=sunrise n) (x:=s) (by
      unfold pol
      apply continuousOn_finsetSum; intro i _; apply ContinuousOn.const_mul
      exact (ha n v (moves _ f)).comp (continuous_id.add continuous_const).continuousOn (fun _ H => dawns H zero_lt_one)) hs
  refine tendsto_integral_filter_of_dominated_convergence (F:=fun (y : Heights n) => F.wind v m y f)
    (f:= F.wind v m s f) (bound := fun t : ℝ => C*weight (moves (m+1) f)) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have ht : ContinuousOn (F.wind v m y f) (Ioc 0 1) := by
      unfold wind; apply ContinuousOn.mul; unfold coal; fun_prop
      exact (ha n v _).comp (show ContinuousOn (fun t : ℝ => y+t • rate n) _ from by fun_prop) (fun _ p => dawns hy p.1)
    exact ht.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x h => F.expense m hm _ hy f h
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro x hx
  have H : ContinuousOn (fun y : Heights n => F.psi v (y+x • rate n) (moves (m+1) f)) (sunrise n) :=
    (ha n v _).comp (continuous_id.add continuous_const).continuousOn (fun _ hy => dawns hy hx.1)
  exact tendsto_const_nhds.mul (H s hs)
end YM.Boundary.Waves
