import YM.Push.LOOP_COEFFICIENT.Grids

/-!
# From quadratic path labels (action convention) to an unaveraged curvature row
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Filter Function Set Lattice RG Wilson Precision Exterior Bloch Laurent
open scoped Topology ContDiff BigOperators
variable {ι J : Type*} {l : ι → J} {u : ι → ℝ}

def packed (l : ι → J) (u : ι → ℝ) (j : J) := ∑' i : l ⁻¹' {j}, u i
lemma packed_mul (l : ι → J) (u : ι → ℝ) (w : J → ℝ) (j : J) : w j * packed l u j = packed l (fun i => w (l i) * u i) j := by
  unfold packed; rw [← tsum_mul_left]; exact tsum_congr fun i => by dsimp only; rw [show l i = j from i.property]
lemma packed_hasSum (l : ι → J) {u : ι → ℝ} (h : Summable u) : HasSum (packed l u) (∑' i,u i) := h.hasSum.tsum_fiberwise l
lemma packed_norm (l : ι → J) {u b : ι → ℝ} (h : Summable b) (he : ∀ i, ‖u i‖≤b i) (j) : ‖packed l u j‖ ≤ packed l b j := by
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg (u i)) he h |>.subtype (fun i => i ∈ l ⁻¹' {j})
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun i => he i) (h.subtype (fun i => i ∈ l ⁻¹' {j})))
lemma packed_weight {C : ℝ} {w : J → ℝ} {b : ι → ℝ} (h : SumBudget b C) (hw : ∀ j, 0≤w j) (he : ∀ i, w (l i) * ‖u i‖ ≤ b i) :
    SumBudget (fun j => w j * ‖packed l u j‖) C := by
  have hb (i) : ‖w (l i) * u i‖ ≤ b i := by rw [norm_mul, Real.norm_of_nonneg (hw _)]; exact he i
  have hp := packed_hasSum l h.2.1
  have hs (j : J) : w j * ‖packed l u j‖ ≤ packed l b j := by rw [← Real.norm_of_nonneg (hw j),← norm_mul,packed_mul]; exact packed_norm _ h.2.1 hb j
  have h0 j := mul_nonneg (hw j) (norm_nonneg (packed l u j))
  have hh := Summable.of_nonneg_of_le h0 hs hp.summable
  exact ⟨h0, hh,(hh.tsum_le_tsum hs hp.summable).trans (hp.tsum_eq ▸ h.2.2)⟩
lemma packed_period (l : ι → J) {u : ι → ℝ} (h : Summable u) (p : J → Prop) [DecidablePred p] :
    (∑' j, if p j then packed l u j else 0) = ∑' i, if p (l i) then u i else 0 := by
  have he : Summable fun i => if p (l i) then u i else 0 := (h.indicator {i | p (l i)}).congr (fun i => by split <;> simp_all [indicator])
  refine Eq.trans (tsum_congr fun j => show (if p j then packed l u j else 0) = packed l (fun i => if p (l i) then u i else 0) j from ?_) (packed_hasSum l he).tsum_eq
  unfold packed; simp only [show ∀ i : l ⁻¹' {j}, l i = j from fun i => i.property]; split <;> simp [*]

variable {G : Gauge} {p : Clip} {W : PathData G} {σ C Λ : ℝ}
lemma size_vec (a : Step) : size (a.vec : Cover) = 1 := by rw [Step.vec]; split <;> simp [size,step,Pi.single_apply,apply_ite Int.natAbs]
lemma size_stop (x : Cover) (w : Walk) : size (stop x w) ≤ size x + w.length := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons a w ih => have := ih (x + a.vec); have h := size_add x a.vec; rw [size_vec] at h; simp only [stop,List.length_cons]; omega
lemma size_slot (s : Slot) : size s.offset ≤ s.length := by
  have h := size_stop 0 s.walk; simpa only [size,Pi.zero_apply, Int.natAbs_zero,Finset.sum_const_zero,zero_add,Slot.offset] using h.trans (show size (0:Cover) + s.walk.length ≤ s.length by simp [size,Slot.length])

def deltaPos (W : PathData G) (k : ℕ) := ((W.loop k).leg 1).offset - ((W.loop k).leg 0).offset
lemma size_delta (W : PathData G) (k : ℕ) : size (deltaPos W k) ≤ (W.loop k).length := by
  rw [deltaPos,sub_eq_add_neg]; exact (size_add ..).trans (by rw [size_neg, Atom.length,Fin.sum_univ_two,add_comm]; exact add_le_add (size_slot _) (size_slot _))

def atomRow (W : PathData G) (i j : Sides G) := W.loop_coeff ![i.1,j.1] ![i.2,j.2]

def loopRow (W : PathData G) : Row (Sides G) (Sides G) := fun i j => packed (deltaPos W) (atomRow W i j)
lemma loopRow_budget (hs : 0<σ) (hb : SumBudget (fun i => (W.loop i).budget σ) Λ) : (loopRow W).strip σ Λ := by
  intro i j; refine packed_weight hb (fun _ => (Real.exp_pos _).le) fun k => ?_
  rw [Atom.budget,mul_comm (W.loop k).magnitude]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (Real.exp_pos _).le
  · exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast size_delta W k) hs.le)
  unfold atomRow PathData.loop_coeff; split
  · exact Finset.single_le_sum (fun i _ => abs_nonneg ((W.loop k).coeff i)) (Finset.mem_univ _)
  rw [norm_zero]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma loopRow_sum (h : W.Bounds p σ C Λ) (i j : Sides G) : HasSum (loopRow W i j) 0 := by
  rw [← (h.loop_normal ![i.1,j.1] ![i.2,j.2]).1]; exact packed_hasSum _ (h.loopTerms ..).1
lemma loopRow_moment (h : W.Bounds p σ C Λ) (i j : Sides G) (d : Axis) : HasSum (fun z : Cover => (z d : ℝ)*loopRow W i j z) 0 := by
  have he := (h.loop_normal ![i.1,j.1] ![i.2,j.2]).2 d
  have ht := (h.loopTerms ![i.1,j.1] ![i.2,j.2]).2 d
  have eq (k) : (deltaPos W k d : ℝ)*atomRow W i j k = _ := mul_comm ..
  simp_rw [loopRow, show ∀ z : Cover, (z d : ℝ)*packed (deltaPos W) (atomRow W i j) z = _ from packed_mul (deltaPos W) (atomRow W i j) (fun z => (z d : ℝ)), eq]
  rw [← he]; exact packed_hasSum _ ht
end YM.Push.Loops
