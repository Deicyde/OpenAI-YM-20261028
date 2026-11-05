import YM.Push.ABSOLUTE_SUMS.Labels
import YM.Push.ABSOLUTE_SUMS.Log


/-!
# Ratio estimate for a deleted set of unforced labels

Before assembly, avoiding the footprint of a family.

Here for the
literal disjoint gas, fixed word activities (real).

Neither
assumes absence is already independent nor forbids more interactions
without paying an actual correction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Gas
open Lattice Trees Graph Ursell Finset RG
open scoped BigOperators Classical Topology
variable {ι : Type*} {n : Side} (X : ι → Support n) (Y : Support n) (B : ℕ) (w : ι → ℝ)

def cut (i : ι) := if Disjoint Y (X i) then w i else 0
def missing (i : Clusters ι) := if Disjoint Y (unionOf X i.2) then 0 else term (blocked X) w i

lemma opens (j : Clusters ι) : term (blocked X) (cut X Y w) j = term (blocked X) w j - missing X Y w j := by
  unfold missing; split
  next h =>
    unfold term; rw [sub_zero]; congr 2
    apply prod_congr rfl; intro i hi
    apply if_pos; rw [Finset.disjoint_left]; intro k hk he
    exact Finset.disjoint_left.mp h hk (mem_biUnion.mpr ⟨i,hi,he⟩)
  next h =>
    rw [Finset.not_disjoint_iff] at h; obtain ⟨i,hk,hi⟩ := h
    obtain ⟨p,hp,hh⟩ := mem_biUnion.mp hi
    have hv : cut X Y w (j.2 p)=0 := if_neg (Finset.not_disjoint_iff.mpr ⟨i,hk,hh⟩)
    unfold term; rw [Finset.prod_eq_zero hp hv]; ring

lemma missing_tail (hn : ∀ i,(X i).Nonempty) {a γ δ q : ℝ} (ha : 0 ≤ a)
    (h : Ready X B (fun i => ‖w i‖) a γ δ q) (m : ℕ) :
    SumBudget (fun i : Clusters ι => if m ≤ i.1 then ‖missing X Y w i‖ else 0)
      (Y.card * (γ*q^m*(1-q)⁻¹)) := by
  let f := fun (x : Site n) (z : Clusters ι) => if m ≤ z.1 ∧ x ∈ unionOf X z.2 then
    clusters (blocked X) (fun i => ‖w i‖) z.2 * currency B a (unionOf X z.2) else 0
  let D := γ*q^m*(1-q)⁻¹
  have he i : SumBudget (f i) D := log_hit_tail _ _ _ (literal_test X hn) h ha m i
  have hg := budget_over Y f (fun _ => D) (fun i _ => he i)
  change SumBudget _ (Y.card*D)
  rw [show (Y.card:ℝ)*D = ∑ _i ∈ Y,D by simp]
  apply budget_mono hg
  · intro i; split <;> first | exact le_rfl | exact norm_nonneg _
  intro i; unfold missing; split
  next hk =>
    split
    next hh => rw [norm_zero]; exact hg.1 i
    next hh =>
      rw [Finset.not_disjoint_iff] at hh; obtain ⟨p,hp,he'⟩ := hh
      rw [term_nonneg]; apply le_trans _ (single_le_sum (f:=fun p => f p i) (fun p _ => (he p).1 i) hp)
      unfold f; rw [if_pos ⟨hk,he'⟩]
      exact le_mul_of_one_le_right (clusters_nonneg _ (fun _ => norm_nonneg _) _)
        (Real.one_le_exp (mul_nonneg ha (by positivity)))
  next hk => exact hg.1 i

/-- Common mass retains the actual sign; absorption paid only in the
upper bound. Includes Y empty and works for any fixed finite torus.
Hit and the ratio-cost constant uniform in that size (per site of Y).
-/
theorem restores_log (hn : ∀ i,(X i).Nonempty) {a γ δ q : ℝ} (ha : 0 ≤ a)
    (h : Ready X B (fun i => ‖w i‖) a γ δ q) :
    let t := total (blocked X) w
    let u := total (blocked X) (cut X Y w)
    let p := ∑' i, missing X Y w i
    let C := (Y.card:ℝ)*(γ*(1-q)⁻¹)
    u = t * Real.exp (-p) ∧ |p| ≤ C ∧ t*Real.exp (-C) ≤ u ∧ u ≤ t*Real.exp C := by
  have hk i : ‖cut X Y w i‖ ≤ ‖w i‖ := by
    unfold cut; split <;> first | exact le_rfl | exact norm_zero.trans_le (norm_nonneg _)
  have he : Ready X B (fun i => ‖cut X Y w i‖) a γ δ q := by
    rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
    exact ⟨h1,h2,h3,h4,fun _ => norm_nonneg _,Labels.raise_prices _ _ (fun _ => norm_nonneg _) h6 hk⟩
  have hb : Hard (blocked X) := ⟨fun i => Or.inl rfl, fun _ _ => blocked_back X⟩
  have hf := price_log _ w hb X B (literal_test X hn) ha h; have hg := price_log _ _ hb X B (literal_test X hn) ha he
  intro t u p C
  have H : SumBudget (fun i => ‖missing X Y w i‖) C := by
    simpa only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] using
      missing_tail X Y B w hn ha h 0
  have hP : |p| ≤ C := (norm_tsum_le_tsum_norm H.2.1).trans H.2.2
  have hi := H.2.1.of_norm; have hh := hf.2.1.2.1.of_norm
  have hx : logSum (blocked X) (cut X Y w)=logSum (blocked X) w - p := by
    unfold logSum p; simp_rw [opens, hh.tsum_sub hi]
  have hw : u=t*Real.exp (-p) := by unfold u t; rw [← hg.2.2.1, hx, ← hf.2.2.1, sub_eq_add_neg,Real.exp_add]
  have he : 0 ≤ t := hf.2.2.2.1.le
  refine ⟨hw,hP,?_,?_⟩
  · rw [hw]; gcongr; exact (abs_le.mp hP).2
  rw [hw]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by have he := abs_le.mp hP; linarith)) he
end YM.Push.AbsoluteSums.Gas
