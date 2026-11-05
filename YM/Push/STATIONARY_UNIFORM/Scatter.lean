import YM.Push.STATIONARY_UNIFORM.Beacons
import YM.Push.STATIONARY_UNIFORM.Count

/-!
# The period-independent tensor bounds from exponentially paid local packets

Even for infinitely many labels in a row, on the SAME real field domains.
Beacon Σ→Scatter pays for the density as an actual sum over sites (not an
average). No promise of a uniform scalar bound at order zero after summing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric Lattice RG
open scoped Topology ContDiff BigOperators Classical

section series
variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma iterated_at_sum {u : α → E → F} {s : Set E} (h : IsOpen s) (hc : IsPreconnected s)
    {C : α → ℝ} (hC : Summable C) {N} (hu : ∀ i x, x∈s → Allows N (u i) x (C i)) {x : E} (hx : x∈s) (k : ℕ) (hk : k≤N) :
    iteratedFDeriv ℝ k (fun x => ∑' i, u i x) x = ∑' i, iteratedFDeriv ℝ k (u i) x := by
  induction k generalizing x with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp, comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k ih =>
    let f i := iteratedFDeriv ℝ k (u i)
    have he : Summable (fun i => f i x) := .of_norm_bounded hC (fun i => (hu _ x hx).norm_le k (by omega))
    have ht := hasFDerivAt_tsum_of_isPreconnected hC h hc
      (fun i x hx => ((hu i x hx).analytic.differentiableAt_iteratedFDeriv (m:=k) (by simp)).hasFDerivAt)
      (fun i x hx => by rw [fderiv_iteratedFDeriv]; simpa only [comp_apply,LinearIsometryEquiv.norm_map] using (hu i x hx).norm_le _ hk) hx he hx
    have hw : (iteratedFDeriv ℝ k fun x => ∑' i, u i x) =ᶠ[𝓝 x] fun x => ∑' i, f i x := by
      filter_upwards [h.mem_nhds hx] with i hi; exact ih hi (by omega)
    simp_rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, (ht.congr_of_eventuallyEq hw).fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

end series

variable {n : Side} {ι α E : Type} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Positions ι} {N : ℕ} {y : Site n} {a K C D : ℝ} {l : ι → Site n}

lemma beacon_sum {s : Finset α} {C : α → ℝ} {f : α → Positions ι → E}
    (h : ∀ i∈s, Beacon l a N (f i) y p (C i)) (he : ∀ i∈s, ContDiffAt ℝ ω (f i) p) : Beacon l a N (fun z => ∑ i∈s, f i z) y p (∑ i∈s, C i) := by
  induction s using Finset.induction with
  | empty => intro k hk q; simp [entry]
  | insert i s hi ih =>
    have ht j (hj : j∈s) := he j (Finset.mem_insert_of_mem hj)
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (he i (Finset.mem_insert_self ..)) (ContDiffAt.sum ht) (ih (fun _ hj => h _ (Finset.mem_insert_of_mem hj)) ht)

lemma beacon_tsum [CompleteSpace E] {u : α → Positions ι → E} {s : Set (Positions ι)} (h : IsOpen s) (hs : IsPreconnected s)
    {P Q : α → ℝ} (hP : Summable P) (hQ : SumBudget Q C) (ht : ∀ i x, x∈s → Allows N (u i) x (P i)) (hp : p∈s)
    (hB : ∀ i, Beacon l a N (u i) y p (Q i)) : Beacon l a N (fun z => ∑' i, u i z) y p C := by
  intro k hk q; let L := Real.exp (-a*spanSites l y q)
  have hf : Summable (fun i => iteratedFDeriv ℝ k (u i) p) :=
    .of_norm_bounded hP (fun i => (ht i p hp).norm_le _ hk)
  unfold entry; rw [iterated_at_sum h hs hP ht hp k hk, ContinuousMultilinearMap.tsum_eval hf]
  have he : Summable (fun i => ‖entry (u i) p q‖) := (hQ.2.1.mul_right L).of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hB i k hk q)
  apply (norm_tsum_le_tsum_norm he).trans
  apply le_trans (he.tsum_le_tsum (fun i => hB i k hk q) (hQ.2.1.mul_right L)); rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right hQ.2.2 (Real.exp_pos _).le

variable {f g : Positions ι → E}

def Scatter (l : ι → Site n) (a : ℝ) (N : ℕ) (f : Positions ι → E) (p : Positions ι) (C : ℝ) :=
  ∀ (k : ℕ), k ≤ N → ∀ (q : Fin k → ι) (j : Fin k), ‖entry f p q‖ ≤ C * Real.exp (-a*spanSites l (l (q j)) q)

lemma Scatter.add (hf : ContDiffAt ℝ ω f p) (hg : ContDiffAt ℝ ω g p) (h : Scatter l a N f p C) (h' : Scatter l a N g p D) :
    Scatter l a N (fun z => f z+g z) p (C+D) := by
  intro k hk q j
  unfold entry; rw [show (fun z => f z+g z)=f+g from rfl,iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top), add_mul]; exact (norm_add_le ..).trans
    (add_le_add (h _ hk _ j) (h' _ hk _ j))

lemma Scatter.smul (hf : ContDiffAt ℝ ω f p) (h : Scatter l a N f p C) (b : ℝ) :
    Scatter l a N (fun z => b • f z) p (|b| * C) := by
  intro k hk q j; unfold entry
  rw [show (fun z => b • f z) = b • f from rfl,iteratedFDeriv_const_smul_apply (hf.of_le le_top)]
  change ‖b • entry f p q‖ ≤ _; rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h _ hk _ j) (abs_nonneg _)

lemma Scatter.mono (h : Scatter l a N f p C) (hC : C≤D) : Scatter l a N f p D :=
  fun k hk q j => (h k hk q j).trans (mul_le_mul_of_nonneg_right hC (by positivity))

lemma entries_finset {u : α → Positions ι → E} {s : Finset α} (h : ∀ i∈s, ContDiffAt ℝ ω (u i) p) {k} (q : Fin k → ι) :
    entry (fun z => ∑ i∈s, u i z) p q = ∑ i∈s, entry (u i) p q := by
  induction s using Finset.induction with
  | empty => simp [entry]
  | insert i s hi ih =>
    have he j (hj : j∈s) := h j (Finset.mem_insert_of_mem hj)
    simp_rw [Finset.sum_insert hi,← ih he]; unfold entry
    let F z := ∑ j∈s, u j z
    change iteratedFDeriv ℝ k (u i+F) _ _ = _
    rw [iteratedFDeriv_add_apply ((h i (Finset.mem_insert_self ..)).of_le le_top) ((ContDiffAt.sum he).of_le le_top)]; rfl

lemma scatter_sum {u : α → Positions ι → E} {s : Finset α} (h : ∀ i∈s, ContDiffAt ℝ ω (u i) p)
    {P : α → ℝ} (hp : ∀ i∈s, Scatter l a N (u i) p (P i)) : Scatter l a N (fun z => ∑ i∈s, u i z) p (∑ i∈s,P i) := by
  intro k hk q j; rw [entries_finset h, Finset.sum_mul]; exact (norm_sum_le ..).trans
    (Finset.sum_le_sum fun i hi => hp i hi k hk q j)

def weaker (N : ℕ) (a : ℝ) := a/(2*(N+1 : ℝ))
omit [Fintype ι] in
lemma price_relative {k} (hk : k ≤ N) (q : Fin k → ι) (j : Fin k) (ha : 0≤a) :
    Real.exp (-a*spanSites l y q) ≤ Decay (a/2) (l (q j)) y * Real.exp (-(weaker N a)*spanSites l (l (q j)) q) := by
  let r := l (q j); let d := spanSites l y q
  have hp : separation y r ≤ d := Finset.single_le_sum (fun i _ => Nat.zero_le (separation y (l (q i)))) (Finset.mem_univ j)
  have hs : spanSites l r q ≤ (N+1)*d := calc
    _ ≤ ∑ i, (d+separation y (l (q i))) := Finset.sum_le_sum fun i _ => (separation_triangle r y (l (q i))).trans
      (by rw [separation_comm r]; omega)
    _ = k*d+d := by rw [Finset.sum_add_distrib]; simp [d,spanSites]
    _ ≤ _ := by rw [add_mul,one_mul]; exact Nat.add_le_add_right (Nat.mul_le_mul_right d hk) _
  rw [decay_comm, Decay, ← Real.exp_add,Real.exp_le_exp]
  have he : (separation y r:ℝ) ≤ d := by exact_mod_cast hp
  have hh : ((separation y r:ℝ))*(a/2) ≤ d * (a/2) := mul_le_mul_of_nonneg_right he (by linarith)
  have H : weaker N a * spanSites l r q ≤ a/2 * d := calc
    _ ≤ weaker N a * ((N+1:ℝ) * (d:ℝ)) := mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by unfold weaker; positivity)
    _ = _ := by unfold weaker; field_simp
  change -a*(d:ℝ) ≤ -(a/2)*(separation y r:ℝ) + -(weaker N a)*(spanSites l r q:ℝ)
  linarith

lemma scatter [Fintype α] {hc : ℕ} {y : α → Site n} (hy : Multiplicity y hc) {f : α → Positions ι → E}
    (hf : ∀ i, ContDiffAt ℝ ω (f i) p) (h : ∀ i, Beacon l a N (f i) (y i) p C) (ha : 0 < a) (hp : 0 ≤ C) :
    Scatter l (weaker N a) N (fun z => ∑ i, f i z) p (C*(hc:ℝ)*countCost (a/2)) := by
  intro k hk q j
  rw [entries_finset (fun i _ => hf i)]
  let A := l (q j); let B := Real.exp (-(weaker N a)*(spanSites l A q:ℝ))
  apply le_trans (norm_sum_le ..)
  calc
    _ ≤ ∑ i, C * (Decay (a/2) A (y i) * B) := Finset.sum_le_sum fun i _ => (h i k hk q).trans
      (mul_le_mul_of_nonneg_left (price_relative hk q j ha.le) hp)
    _ = C*(∑ i, Decay (a/2) A (y i))*B := by rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left (hy.count y (half_pos ha) A) hp
      rw [← mul_assoc] at he
      exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
end YM.Push.Uniform
