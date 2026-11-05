import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Probe

/-!
# Finite absolute probe fees: constructors
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Filter Function Set Finset
open YM.Multi.Vacuum.Gauss Probe
open scoped Topology BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]
namespace Loan
variable {f : Row I → ℂ} {n : ℕ} {w : Row I} {H B : ℕ → ℝ}

lemma longer (h : Costs n f w H) (he : ∀ i,H i≤B i) : Costs n f w B :=
  ⟨fun i => (h.fees i).trans (he i),h.charm,h.fires,
   fun l hl x => (h.price l hl x).trans (mul_le_mul_of_nonneg_right (he _) (Real.exp_pos _).le)⟩

lemma entry (hh : ∀ k, 0≤H k) (hf : Continuous f) (he : ∀ x,‖f x‖≤H 0 * Real.exp (pay w x)) :
    Costs 0 f w H := by
  refine ⟨hh,fun l hl => ?_,fun _ hl => ?_,fun l hl => ?_⟩
  · obtain rfl : l=[] := by simpa using hl
    exact hf
  · omega
  obtain rfl : l=[] := by simpa using hl
  exact he

lemma next (hh : ∀ k,0 ≤ H k) (hd : Differentiable ℝ f) (he : ∀ x,‖f x‖≤H 0 * Real.exp (pay w x))
    (h : ∀ a : I,Costs n (hit f a) w (fun i=> H (i+1))) : Costs (n+1) f w H := by
  refine ⟨hh,fun l => ?_,fun l => ?_,fun l => ?_⟩
  · induction l using List.reverseRecOn with
    | nil => exact fun _ => hd.continuous
    | append_singleton l a ih => rw [← jet_hit]; exact fun h₁ => (h a).charm _ (by simpa using h₁)
  · induction l using List.reverseRecOn with
    | nil => exact fun _ => hd
    | append_singleton l a ih => rw [← jet_hit]; exact fun h₁ => (h a).fires _ (by simpa using h₁)
  induction l using List.reverseRecOn with
  | nil => exact fun _ => he
  | append_singleton l a ih =>
    rw [← jet_hit]; intro h₁; simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using
      (h a).price l (by simpa using h₁)

lemma scaling (z : ℂ) (h : Costs n f w H) : Costs n (fun x => z*f x) w (fun k => ‖z‖ * H k) := by
  have hz (l : List I) (hl : l.length ≤ n) : jet (fun x=>z*f x) l=fun x => z * jet f l x := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      have hm : l.length < n := by simp only [List.length_cons] at hl; omega
      simp only [jet,ih hm.le]; funext x; rw [hit, fderiv_const_mul ((h.fires l hm) x)]; rfl
  refine ⟨fun k => mul_nonneg (norm_nonneg z) (h.fees _),fun l hl => ?_,fun l hl => ?_,fun l hl x => ?_⟩
  · rw [hz l hl]; exact continuous_const.mul (h.charm l hl)
  · rw [hz l hl.le]; exact (h.fires l hl).const_mul z
  rw [hz l hl,norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.price _ hl x) (norm_nonneg _)

lemma batch {α : Type} (s : Finset α) (f : α → Row I → ℂ) (K : α → ℕ → ℝ)
    (h : ∀ i∈s,Costs n (f i) w (K i)) : Costs n (fun x=>∑ i∈s,f i x) w (fun k=>∑ i∈s,K i k) := by
  have he l (hl : l.length ≤ n) : jet (fun x=>∑ i∈s,f i x) l=fun x=>∑ i∈s,jet (f i) l x := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      have hv : l.length < n := by simp only [List.length_cons] at hl; omega
      simp only [jet,ih hv.le]; funext x; simp_rw [hit]
      rw [fderiv_fun_sum (fun i hi=> (h i hi).fires l hv x),_root_.sum_apply]
  refine ⟨fun k => sum_nonneg fun i hi=> (h i hi).fees k, fun l hl => ?_,fun l hl=> ?_,fun l hl=>?_⟩
  · rw [he l hl]; exact continuous_finsetSum _ fun i hi => (h i hi).charm l hl
  · rw [he l hl.le]; exact Differentiable.fun_sum fun i hi => (h i hi).fires l hl
  rw [he l hl]; intro x; rw [Finset.sum_mul]
  exact (norm_sum_le ..).trans (sum_le_sum fun i hi=> (h i hi).price l hl x)
end Loan
end YM.Primitives.GCC
