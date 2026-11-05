import YM.Next.EXTRACTION.Tails
import YM.Org.Theatre
import YM.Work.B04
import YM.Work.B06

/-!
# Cost compiler: numerical tools

Not a schedule theorem for all of E.

Arguments to our costs on an edge of the schedule are in the order
**input, output** `(j,i)`; these are *smoothing stages*, not step
numbers. They can be equal! Costs at dummy stages (e.g., j<4) use the
same types. Prefix operations here are always **finite**. The inputs to
them must already be known; these are not fixed-point lemmas for mutually
dependent quotations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler

open Filter Function Lattice RG RG.Supply Wilson
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- Possible stage edge, arguments (finer, coarser). Includes loops. -/
def StepStages (j i : ℕ) : Prop := i ≤ j ∧ j ≤ i+1

lemma stepStages_source {j i : ℕ} (h : StepStages j i) : j = i ∨ j = i+1 := by
  unfold StepStages at h
  omega

lemma stepStages_target {j i : ℕ} (h : StepStages j i) : i = j ∨ i = j-1 := by
  unfold StepStages at h
  omega

lemma stages_same (j : ℕ) : StepStages j j := ⟨le_rfl, Nat.le_succ _⟩

lemma stages_down (j : ℕ) : StepStages j (j-1) := by
  unfold StepStages
  omega

section Max
variable {ι α : Type*} [LinearOrder α]

/-- Common charge for both possible transitions FROM j. -/
def fromMax (u : ℕ → ℕ → α) (j : ℕ) : α := max (u j j) (u j (j-1))
/-- Common upper limit for a positive width/lower-bound constant,
computed from quotes for transitions FROM j (take min). -/
def fromMin (u : ℕ → ℕ → α) (j : ℕ) : α := min (u j j) (u j (j-1))
/-- Charge for both possible transitions ENDING AT i. -/
def intoMax (u : ℕ → ℕ → α) (i : ℕ) : α := max (u i i) (u (i+1) i)
/-- Width for both possible transitions ENDING AT i. -/
def intoMin (u : ℕ → ℕ → α) (i : ℕ) : α := min (u i i) (u (i+1) i)

lemma le_fromMax (u : ℕ → ℕ → α) {i j : ℕ} (h : StepStages j i) : u j i ≤ fromMax u j := by
  rcases stepStages_target h with h|h
  · rw [h]; exact le_max_left ..
  rw [h]; exact le_max_right ..

lemma fromMin_le (u : ℕ → ℕ → α) {i j : ℕ} (h : StepStages j i) : fromMin u j ≤ u j i := by
  rcases stepStages_target h with h|h
  · rw [h]; exact min_le_left ..
  rw [h]; exact min_le_right ..

lemma le_intoMax (u : ℕ → ℕ → α) {i j : ℕ} (h : StepStages j i) : u j i ≤ intoMax u i := by
  rcases stepStages_source h with h|h
  · rw [h]; exact le_max_left ..
  rw [h]; exact le_max_right ..

lemma intoMin_le (u : ℕ → ℕ → α) {i j : ℕ} (h : StepStages j i) : intoMin u i ≤ u j i := by
  rcases stepStages_source h with h|h
  · rw [h]; exact min_le_left ..
  rw [h]; exact min_le_right ..

/-- Finite prefix upper envelope. -/
def prefixHi (f : ℕ → α) (i : ℕ) := (Finset.range (i+1)).sup' (by simp) f
/-- Finite prefix lower envelope. -/
def prefixLo (f : ℕ → α) (i : ℕ) := (Finset.range (i+1)).inf' (by simp) f

lemma prefixHi_le {f : ℕ → α} {i : ℕ} {a : α} (h : ∀ j ≤ i, f j ≤ a) : prefixHi f i ≤ a :=
  Finset.sup'_le _ _ fun j hj => h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

lemma le_prefixLo {f : ℕ → α} {i : ℕ} {a : α} (h : ∀ j ≤ i, a ≤ f j) : a ≤ prefixLo f i :=
  Finset.le_inf' _ _ fun j hj => h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

lemma le_prefixHi (f : ℕ → α) {i j : ℕ} (h : j ≤ i) : f j ≤ prefixHi f i :=
  Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))

lemma prefixLo_le (f : ℕ → α) {i j : ℕ} (h : j ≤ i) : prefixLo f i ≤ f j :=
  Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))

lemma lt_prefixLo {f : ℕ → α} {i : ℕ} {a : α} (h : ∀ j ≤ i, a < f j) : a < prefixLo f i := by
  unfold prefixLo
  rw [Finset.lt_inf'_iff]
  exact fun j hj => h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

lemma prefixHi_mono (f : ℕ → α) : Monotone (prefixHi f) := fun _ _ hij =>
  prefixHi_le fun _ hk => le_prefixHi f (hk.trans hij)

lemma prefixLo_anti (f : ℕ → α) : Antitone (prefixLo f) := fun _ _ hij =>
  le_prefixLo fun _ hk => prefixLo_le f (hk.trans hij)





/-- Eventually requirements can always be bought as *monotone*
entrance/floor thresholds, using initial lower requests. No monotonicity
of the tested predicate required. Use for α=ℕ pre-L, or α=ℝ post-L. -/
theorem collect_upper (u : ℕ → α) (T : ℕ → α → Prop) (h : ∀ i, ∀ᶠ x in atTop, T i x) :
    ∃ m : ℕ → α, Monotone m ∧ u ≤ m ∧ ∀ i x, m i ≤ x → T i x := by
  have : Nonempty α := ⟨u 0⟩
  classical
  choose b hb using fun i => eventually_atTop.mp (h i)
  let f (i : ℕ) := max (b i) (u i)
  exact ⟨prefixHi f, prefixHi_mono _, fun _ => le_trans (le_max_right ..) (le_prefixHi f le_rfl),
    fun i x hx => hb i x (le_trans (le_trans (le_max_left ..) (le_prefixHi f le_rfl)) hx)⟩


end Max

section Edge
variable {α : Type*}
/-- Collect the two eventual transition tests at one stage; also works at 0. -/
theorem eventually_transitions (j : ℕ) (f : Filter α) (T : ℕ → α → Prop)
    (h : ∀ i, StepStages j i → ∀ᶠ x in f, T i x) : ∀ᶠ x in f, ∀ i, StepStages j i → T i x := by
  filter_upwards [h j (stages_same _), h (j-1) (stages_down _)] with x hx he i hi
  rcases stepStages_target hi with H|H
  · rwa [H]
  rwa [H]
end Edge

/-- Convenient upper envelope. Raw amount lower requests need not be positive. -/
def payHi (f : ℕ → ℝ) := prefixHi (fun i => max (1:ℝ) (f i))
lemma payHi_mono (f : ℕ → ℝ) : Monotone (payHi f) := prefixHi_mono _
lemma payHi_one (f : ℕ → ℝ) (i : ℕ) : 1 ≤ payHi f i :=
  le_trans (le_max_left ..) (le_prefixHi (fun i => max (1:ℝ) (f i)) le_rfl)
lemma payHi_pos (f : ℕ → ℝ) (i : ℕ) : 0 < payHi f i := lt_of_lt_of_le zero_lt_one (payHi_one ..)
lemma le_payHi (f : ℕ → ℝ) : f ≤ payHi f := fun _ =>
  le_trans (le_max_right ..) (le_prefixHi (fun i => max (1:ℝ) (f i)) le_rfl)

def rateLo (f : ℕ → ℝ) := prefixLo (fun i => min (1:ℝ) (f i))
lemma rateLo_anti (f : ℕ → ℝ) : Antitone (rateLo f) := prefixLo_anti _
lemma rateLo_pos {f : ℕ → ℝ} (h : ∀ i, 0 < f i) (i : ℕ) : 0 < rateLo f i :=
  lt_prefixLo fun j _ => lt_min zero_lt_one (h j)
lemma rateLo_one (f : ℕ → ℝ) (i : ℕ) : rateLo f i ≤ 1 :=
  le_trans (prefixLo_le (fun i => min (1:ℝ) (f i)) le_rfl) (min_le_left ..)
lemma rateLo_le (f : ℕ → ℝ) : rateLo f ≤ f := fun _ =>
  le_trans (prefixLo_le (fun i => min (1:ℝ) (f i)) le_rfl) (min_le_right ..)

section Clock
variable {G : Gauge}

lemma step_paid (a : Levels G) (m : ℕ) : StepStages (a.clock.J (m+1)) (a.clock.J m) :=
  ⟨a.fits.mono (Nat.le_succ _), a.fits.stepSlow _⟩

lemma first_le {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Paid I a) (m : ℕ) : p.first ≤ a.clock.J m :=
  le_trans h.firstZero.symm.le (a.fits.mono (Nat.zero_le m))

lemma block_eq {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Paid I a) (m : ℕ) : a.S.block m = D.L (a.clock.J (m+1)) :=
  (a.fits.sameFactor m).symm.trans (congr_fun h.lengths _)

lemma params_eq {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Paid I a) (m : ℕ) : a.params m = p.profile (a.clock.J m) :=
  congr_fun h.stage _

lemma side_ge_shell {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Paid I a) (m i : ℕ) : W.shells (a.clock.J (m+1)) ≤ (a.S.side m i).val := by
  refine le_trans ?_ (h.volume m i)
  refine Nat.le_mul_of_pos_right _ (pow_pos ?_ _)
  omega

lemma beta_eq {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Paid I a) (m : ℕ) : a.clock.hatBeta (m+1) =
      Pressure.betaF G (a.clock.hatBeta m) (D.L (a.clock.J (m+1))) := by
  unfold Calendar.hatBeta Pressure.betaF
  rw [Schedule.scale_succ, ← block_eq h m]
  change a.clock.bar + G.slopeConstant * (a.S.scale m + Real.log (a.S.block m).val) = _
  ring
end Clock

section Budget
variable {ι : Type*}

lemma sumBudget_mono {f g : ι → ℝ} {a b : ℝ} (h : SumBudget f a) (hz : ∀ i, 0 ≤ g i)
    (hg : g ≤ f) (ha : a ≤ b) : SumBudget g b := by
  have ht := h.2.1.of_nonneg_of_le hz hg
  exact ⟨hz, ht, (ht.tsum_le_tsum hg h.2.1).trans (h.2.2.trans ha)⟩
end Budget
end YM.Push.PriceCompiler
