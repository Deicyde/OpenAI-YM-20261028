import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.FieldCount
import YM.Next.FREE_KERNELS.Amend
import YM.Next.SCHEDULE.Postal

/-!
# Upper costs for the A reference

Both true eta and radii of query footprint needed for h grades. Includes
zero-outside exact. Color counting. `along` uses only positive bonds (both
ends in `Hot`). At roots in another ontology compare indices before prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] {a : ι → Site c} {b : κ → Site c}
variable {M : Matrix ι κ ℝ}

def Thin (a : ι → Site c) (b : κ → Site c) (M : Matrix ι κ ℝ) (d : ℕ) := ∀ i j, d < separation (a i) (b j) → M i j=0
namespace Thin
variable {d e : ℕ} {g : ν → Site c} {K : Matrix κ ν ℝ}
omit [Fintype ι] [Fintype κ] in
lemma transpose (h : Thin a b M d) : Thin b a M.transpose d := fun i j he => h j i ((separation_comm ..) ▸ he)
omit [Fintype ι] in
lemma mul (hm : Thin a b M d) (ht : Thin b g K e) : Thin a g (M*K) (d+e) := by
  intro i j hij; rw [Matrix.mul_apply]; apply sum_eq_zero; intro k _
  by_cases hk : d < separation (a i) (b k)
  · rw [hm i k hk,zero_mul]
  have he := separation_triangle (a i) (b k) (g j)
  rw [ht k j (by omega),mul_zero]
end Thin
namespace Coat
variable (X : Coat T F)

lemma plume (h : Room P S T X.x) : Thin (aim S) (along S) X.form (X.B/4) := by
  intro i j hij
  obtain ⟨w,e,H,-⟩ := h.accepted.feeds
  unfold form; rw [of_apply]
  unfold stand motion; split
  next hp =>
    obtain ⟨L,hL⟩ := SliceRows.linear T X.R H i.1.1 i.1.2 X.V
    have hb : orientedRow T X.R i.1.1 i.1.2 X.V (X.lens (sing j))=orientedRow T X.R i.1.1 i.1.2 X.V 0 := by
      refine raw_near T h _ _ _ _ _ _ (fun _ _ => rfl) ?_
      intro e he; unfold lens sing; have hg : e ≠ j.1 := fun he' => hij.not_ge (show separation (aim S i) (atEdge S j.1) ≤ _ from he' ▸ he)
      rw [Pi.single_eq_of_ne hg, ite_self]; rfl
    rw [hb, ← hL, map_zero]; change _ * (0:ℝ)=0; ring
  next hn => change _ * (0:ℝ)=0; ring

lemma span (h : Room P S T X.x) : Thin (along S) (along S) X.plate (X.B/2) := by
  intro i j hij
  have he : i ≠ j := by intro hi; subst i; simp at hij
  simp only [plate,Matrix.add_apply,sleepy,(X.plume h).transpose.mul (X.plume h) i j (by omega)]; simp [he]

lemma sleep_cap (r : ℝ) : Rows (along S) (along S) X.sleepy r 1 := by
  intro i
  rw [Finset.sum_eq_single i]
  · by_cases hb : X.Hot i.1 <;> simp [sleepy,wt,hb]
  · intro b _ hb; simp [sleepy,hb.symm]
  simp

lemma form_price (h : Room P S T X.x) {C : ℝ} (hC : 0 < C) (hX : Bounded T P.top.width C) (i j) :
    wt P.top.width (aim S i) (along S j)*|X.form i j| ≤ scale*(2*C*Real.exp (P.top.width*(predReach S.patch+7:ℝ))) := by
  have ht := Coat.scale_pos
  by_cases hp : X.Hot j.1
  swap
  · obtain ⟨y,e,H,-⟩ := h.accepted.feeds
    rw [X.cold j hp H,abs_zero,mul_zero]; positivity
  have hy i' : X.lens (sing j) i'=sing j i' := by
    by_cases H : j.1=i'
    · subst i'; simp [hp,lens]
    simp [lens,sing,Ne.symm H]
  have hv : wt P.top.width (aim S i) (along S j) * ‖X.motion (sing j) i.1‖ ≤
      2*C*Real.exp (P.top.width*(predReach S.patch+7:ℝ)) := by
    unfold motion; split
    next he =>
      rw [funext hy]; unfold sing
      apply (transported_impulse h.accepted hC hX X.V i.1.1 i.1.2 X.R j.1 _).trans_eq
      simp [dot]
    next hk => rw [norm_zero,mul_zero]; positivity
  unfold form stand; rw [of_apply,abs_mul, abs_of_nonneg ht.le, mul_left_comm _ scale]
  apply mul_le_mul_of_nonneg_left _ ht.le
  exact (mul_le_mul_of_nonneg_left (stand_cap ..) (wt_pos ..).le).trans hv

lemma charges (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) : ∃ C : ℝ, 0<C ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F),
      S.patch=D → S.patch.L=L → Room P S T X.x → ∀ r : ℝ, 0 ≤ r → r ≤ P.top.width/2 →
        Both (aim S) (along S) X.form r C C ∧ Rows (along S) (along S) X.plate r (C*C+1) := by
  obtain ⟨K,hK,hX⟩ := bounded_stencils P D hd
  let B := P.top.width
  let s := price0 (B-B/2)
  let b := scale*(2*K*Real.exp (P.top.width*(predReach D+7:ℝ)))
  let m := tubularPrice G L
  let n := mentionPrice L*Fintype.card G.ColorIndex
  let C := 1+max (max 0 (s*m*b)) (s*n*b)
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one ((le_max_left ..).trans (le_max_left ..))
  have hb : 0 ≤ b := by have := scale_pos; unfold b; positivity
  have hy : 0 < B := P.top.width_pos
  refine ⟨C,hC,fun c f S T F X hS hL hR r hr hf => ?_⟩
  have he (i j) : wt B (aim S i) (along S j)*|X.form i j| ≤ b := by
    have hv := X.form_price hR hK (hX c f S T hS hR.accepted) i j; rwa [hS] at hv
  have hx := rows (entering (G:=G) S) (aim S) X.form hb (show B/2 < B by linarith) he
  have hg := rows (aims (G:=G) S) (along S) X.form.transpose hb (show B/2 < B by linarith) (fun i j => by rw [wt_symm]; exact he j i)
  have hh (i j : Site c) : wt r i j ≤ wt (B/2) i j := Real.exp_monotone (mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg _))
  have hu : Rows (aim S) (along S) X.form r C := by
    rw [hL] at hx
    intro x
    apply le_trans (c:=C) (le_trans (b:=∑ j,wt (B/2) (aim S x) (along S j) *|X.form x j|) ?_ (hx x))
      ((le_max_right ..).trans ((le_max_left ..).trans ((le_add_of_nonneg_left zero_le_one))))
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hh _ _) (abs_nonneg _)
  have hv : Rows (along S) (aim S) X.form.transpose r C := by
    rw [hL] at hg
    intro x
    apply le_trans (c:=C) (le_trans (b:=∑ j,wt (B/2) (along S x) (aim S j) *|X.form j x|) ?_ (hg x))
      ((le_max_right ..).trans (le_add_of_nonneg_left zero_le_one))
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hh _ _) (abs_nonneg _)
  exact ⟨⟨hu,hv⟩,(hv.multiply hr hu hC.le).plus (X.sleep_cap _)⟩
end Coat
end YM.ConnectedActivityE6
