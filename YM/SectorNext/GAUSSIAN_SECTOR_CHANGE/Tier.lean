import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Wisps


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Fixed-L growth in the parent metric, weighted gram prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Tier
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Tree
open YM.Work.F01 YM.Push.SectorMeasure YM.Bid YM.Next.Fluctuations Matrix Gaussian Rows Wisps LocalJet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

private def boxCost (σ : ℝ) (n : ℕ) := (81 * (1+(n:ℝ)^4)) * rate (-σ) n
private lemma box_nn (σ : ℝ) (n : ℕ) : 0 ≤ boxCost σ n := by unfold boxCost rate; positivity

private lemma summable_box {σ : ℝ} (hσ : 0 < σ) : Summable (boxCost σ) := by
  have he := Real.summable_pow_mul_exp_neg_nat_mul 4 hσ
  have hn := Real.summable_pow_mul_exp_neg_nat_mul 0 hσ
  unfold boxCost rate; simp_rw [mul_assoc,add_mul]
  exact ((by simpa using hn : Summable fun n : ℕ => (1:ℝ) * Real.exp (-σ * n)).add he).mul_left _

def wealth (σ : ℝ) := ∑' i, boxCost σ i

lemma wealth_nn (σ : ℝ) : 0 ≤ wealth σ := tsum_nonneg (box_nn σ)

private lemma grain_price (σ : ℝ) (n : ℕ) : grain n * rate (-σ) n ≤ boxCost σ n := by
  apply mul_le_mul_of_nonneg_right _ (rate_pos ..).le
  obtain rfl|h := eq_or_ne n 0
  · norm_num [grain]
  have he : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
  unfold grain; push_cast
  calc
    _ ≤ (3*(n:ℝ))^4 := by gcongr; linarith
    _ ≤ _ := by nlinarith

lemma land {σ : ℝ} (hσ : 0 < σ) (x : Site c) :
    (∑ y : Site c, rate (-σ) (separation y x)) ≤ wealth σ := by
  let h (d : ℕ) (y : Site c) := (if separation y x ≤ d then (1:ℝ) else 0) * rate (-σ) d
  let v := univ.image (fun y : Site c => separation y x)
  calc
    _ ≤ ∑ y : Site c, ∑ d ∈ v, h d y := by
      refine sum_le_sum fun i _ => ?_
      refine (le_of_eq ?_).trans (single_le_sum (f:=fun d => h d i) (fun d _ => ?_) (mem_image_of_mem _ (mem_univ i)))
      · simp [h]
      unfold h; split <;> simp [rate]
      exact (Real.exp_pos _).le -- if simp already
    _ = ∑ d ∈ v, (∑ i : Site c, if separation i x ≤ d then (1:ℝ) else 0) * rate (-σ) d := by rw [sum_comm]; unfold h; simp_rw [← Finset.sum_mul]
    _ ≤ ∑ d ∈ v, boxCost σ d := sum_le_sum fun i _ => (mul_le_mul_of_nonneg_right (spends _ _) (rate_pos ..).le).trans (grain_price _ _)
    _ ≤ wealth σ := (summable_box hσ).sum_le_tsum v (fun d _ => box_nn σ d)

section prices
variable (σ : ℝ) (hσ : 0 < σ)
include hσ
/-- Both alphabets, every address. Overcount even sites coinciding after
projection. -/
def keyFee (S : StepData c f) (G : Gauge) (σ : ℝ) : ℝ :=
  ((Fintype.card G.ColorIndex : ℝ) * (Fintype.card (Site S.patch.L) * Fintype.card Axis)) * wealth σ

def slotFee (S : StepData c f) (G : Gauge) (σ : ℝ) : ℝ :=
  Fintype.card G.ColorIndex * ((Fintype.card Signed:ℝ)*
    ((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site S.patch.L) * wealth σ)+
      Fintype.card Axis * wealth σ))

private lemma paired {α β : Type} [Fintype α] [Fintype β] (f : α → ℝ) :
    (∑ i : α × β, f i.1) = (Fintype.card β:ℝ) * ∑ i,f i := by rw [Fintype.sum_prod_type]; simp [mul_sum]

lemma front_price (A : Stores S) {x : ℝ} (F : Forest S.ratio) (G : Gauge) (i : Site c) :
    (∑ j : In x A F (G:=G), rate (-σ) (separation i (front A F j))) ≤ keyFee S G σ := by
  let R (x : Site c) := rate (-σ) (separation i x)
  rw [show (fun j => rate (-σ) (separation i (front A F j))) =
    (fun j : In x A F (G:=G) => (fun j : Active A x F => R (S.ratio.parent j.val.val.1)) j.1) from rfl, paired σ hσ (fun j : Active A x F => R (S.ratio.parent j.val.val.1))]
  let v (z : Active A x F) := z.val.val
  have h : Injective v := fun _ _ e => Subtype.ext (Subtype.ext e)
  have hb : (∑ j : Active A x F,R (S.ratio.parent j.val.val.1)) ≤ ∑ j : Bond f, R (S.ratio.parent j.1) := by
    rw [← sum_image (g:=v) (f:=fun i => R (S.ratio.parent i.1))]
    · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => (rate_pos ..).le
    exact fun _ _ _ _ => @h _ _
  unfold keyFee; rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left (hb.trans ?_) (Nat.cast_nonneg _)
  rw [paired σ hσ (fun e : Site f => R (S.ratio.parent e)), sum_parent S.ratio R]
  have hr : ∑ i : Site c, R i ≤ wealth σ := by
    unfold R; simp_rw [separation_comm i]; exact land hσ i
  change (Fintype.card Axis:ℝ)*((Fintype.card (Site S.patch.L):ℝ)*_) ≤ _
  conv_rhs => rw [mul_comm (Fintype.card (Site S.patch.L):ℝ), mul_assoc]; 
  gcongr -- hr 

lemma down_price (S : StepData c f) (G : Gauge) (i : Site c) :
    (∑ j : Receipt G S, rate (-σ) (separation i (down S j))) ≤ slotFee S G σ := by
  let R (s : Signed) (x : Site c) := rate (-σ) (separation i (s.act x))
  let T (j : Slots S) := R j.1 (roots S (j.2.elim (fun x => .inl x.1) .inr))
  change (∑ j : Slots S × G.ColorIndex, T j.1) ≤ _
  rw [paired σ hσ T,Fintype.sum_prod_type]; unfold slotFee
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [← nsmul_eq_mul (Fintype.card Signed), ← Finset.card_univ, ← Finset.sum_const]
  refine sum_le_sum fun s _ => ?_
  rw [Fintype.sum_sum_type]
  let e (x : Site c) := s.act x
  let E : Equiv.Perm (Site c) := Equiv.ofBijective e ⟨s.act_injective,Finite.injective_iff_surjective.mp s.act_injective⟩
  have hr : ∑ i : Site c, R s i ≤ wealth σ := by
    unfold R; simp_rw [separation_comm i]; change ∑ y, rate _ (separation (E y) _) ≤ _
    rw [Equiv.sum_comp E (fun x=> rate (-σ) (separation x i))]; exact land hσ _
  apply add_le_add
  · change ∑ p : Cell f × Bool, R s (S.ratio.parent p.1.1) ≤ _
    rw [paired σ hσ (fun e : Cell f => R s (S.ratio.parent e.1)), paired σ hσ (fun e : Site f => R s (S.ratio.parent e)), sum_parent S.ratio (R s)]
    change (Fintype.card Bool:ℝ)*((Fintype.card PlaqAxes:ℝ)*((Fintype.card (Site S.patch.L):ℝ)*_)) ≤ _
    simp only [mul_assoc]; gcongr
  change ∑ p : Site c × Axis, R s p.1 ≤ _
  rw [paired σ hσ (R s)]; gcongr

end prices
end YM.Next.SectorChange.Tier
