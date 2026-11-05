import YM.Next.FREE_KERNELS.Buffer
import YM.Next.FREE_KERNELS.Pilot

/-!
# Releasing A after puncture cancellation

Analytic budgets for A still with factor L. Real identities will be glued
pointwise, including all fine aliases.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {ι α β : Type*} {j t : ℕ}

lemma Moderate.branches (c : ι → Prop) {w : ι → ℝ} {f : ι → Momentum → ℂ} (h : ∀ i, 0 ≤ w i)
    (ht : Moderate (fun i : Subtype c => w i) fun i => f i)
    (hb : Moderate (fun i : {i // ¬ c i} => w i) fun i => f i) : Moderate w f := by
  obtain ⟨η,C,hp,hc,h1⟩ := ht; obtain ⟨θ,B,hq,hb,h2⟩ := hb
  refine ⟨min η θ,max C B,lt_min hp hq,lt_max_of_lt_left hc,fun i => ?_⟩
  by_cases hs : c i
  · exact (h1 ⟨i,hs⟩).mono (min_le_left ..) (mul_le_mul_of_nonneg_right (le_max_left ..) (h i))
  exact (h2 ⟨i,hs⟩).mono (min_le_right ..) (mul_le_mul_of_nonneg_right (le_max_right ..) (h i))

lemma Pay.branches (c : ι → Prop) {w : ι → ℝ} {f : ι → Momentum → Matrix α β ℂ} (h : ∀ i, 0 ≤ w i)
    (ht : Pay (fun i : Subtype c => w i) fun i => f i) (hb : Pay (fun i : {i // ¬ c i} => w i) fun i => f i) : Pay w f :=
    ⟨h,fun a b => Moderate.branches c h (ht.tap a b) (hb.tap a b)⟩

lemma out_budget (r : ℕ) : Pay (fun _ : ι => 1) fun _ p => signal 1 r p := by
  apply Pay.expose_wedge
  intro a
  have h := seed_control (fun _ : ι => 1) (fun _ => a)
  simpa [tripQ,seedQ,narrow] using h

namespace Flight
variable (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (ht : 4 ≤ t)
    (F : ι → Flight j t) (l : ∀ i, Site (F i).L)

include hk ht
lemma prior_cost : Pay (fun _ : ι => 1) fun i p => priorG k (F i) p := by
  let v (i) := (F i).land
  have h (a : Axis) := (Train.bulb_budget k ht v (fun _ => a)).inv (Train.bulb_firm k hk v _) (fun _ => one_pos)
  unfold priorG; simpa only [v,inv_one,one_pow] using Pay.expose_mask 1 h
lemma sluice_cost : Pay (fun _ : ι => 1) fun i p => sluice k (F i) p := by
  let v (i) := (F i).land
  have h := (((out_budget (ι:=ι) 0).reverse.transpose).times (prior_cost k hk ht F)).scale
    ((Train.bend_budget k hk ht v).inv (Train.bend_firm k hk ht v) fun _ => one_pos)
  unfold sluice mirage; simpa only [v, inv_one,mul_one] using h

include hj
lemma ahead_cost : Pay (fun i => decay j (l i)) fun i p => ahead k (F i) p (l i) := by
  apply Pay.branches (fun i => l i=0) (fun i => (decay_pos ..).le)
  · have hh (a : Axis) := (Train.bulb_budget k hj (fun i => (F i).wing) (fun _ => a)).on_alias _ (fun i => (F i).odd) (fun _ => 0)
    have hx := (((Pay.expose_mask 1 hh).times (flux_budget F 1 (fun _ => 0))).times (prior_cost k hk ht F)).reindex
      (fun i : {i // l i=0} => i.val)
    have hl (i : {i // l i=0}) : l i.val=0 := i.property
    simp only [ahead,hl,if_true,decay_zero]
    unfold toe; simpa only [one_pow,decay_zero,mul_one] using hx
  let I := {i // ¬ l i=0}; let F' (i : I) := F i; let l' (i : I) := l i.val
  have hh (a : Axis) := portD_budget k hj F' l' (fun i : I => i.property) (fun _ => a)
  have hx := (((Pay.expose_mask 1 hh).times (flux_budget F' 1 l')).times (prior_cost k hk ht F')).scale
    (divisor_control fun i => (F' i).land.mass)
  have he : Pay (fun i => decay j (l' i)) fun i p => (F' i).span p •
      (mask 1 (portD k (F' i) p (l' i))*flux (F' i) 1 (aliasAt p (l' i))*priorG k (F' i) p) := by
    apply hx.raise
    intro i; dsimp only; rw [pow_one,one_mul,mul_one]
    exact mul_le_of_le_one_left (decay_pos ..).le (inv_le_one_of_one_le₀ (one_le_pow₀ (grade_ge _)))
  have hl (i : {i // ¬ l i=0}) : ¬ l i.val=0 := i.property
  simpa only [ahead,hl,if_false] using he

lemma rests_cost (a : Axis) : Moderate (fun _ : ι => 1) fun i p => rests k (F i) p a := by
  have hB : Moderate (fun _ : ι => 1) fun i p => massFilter (F i).patch ((F i).toe p) := by
    simpa only [toe,decay_zero] using bills F (fun _ => 0)
  have hh := hB.inv (bills_firm F) fun _ => one_pos
  let v := fun i => (F i).land
  have hC := (tail_budget k hj F a).mul ((Train.bulb_budget k ht v (fun _ => a)).inv (Train.bulb_firm k hk v _) fun _ => one_pos)
  have hA := (hills_budget k hj F).mul ((abide_budget k hj F).inv (abide_firm k hk F) fun _ => one_pos)
  unfold rests; simpa only [v,mul_one, inv_one,div_eq_mul_inv] using hh.mul (hC.sub hA)
lemma gains_cost (a : Axis) : Moderate (fun i => decay j (l i) *(grade (l i)^2)⁻¹)
    fun i p => gains k (F i) p (l i) a := by
  apply Moderate.branches (fun i => l i=0) (fun i => mul_nonneg (decay_pos ..).le (by positivity))
  · have he (i : {i // l i=0}) : l i.val=0 := i.property
    convert! (rests_cost k hk hj ht F a).index (fun i : {i // l i=0} => i.val) using 1
    · ext i; simp [he i, grade,pdist]
    ext i; simp [gains, he i]
  let I := {i // ¬ l i=0}; let F' (i : I) := F i; let l' (i : I) := l i.val
  have he (i : I) : l i.val≠0 := i.property
  have hB := back_bills F' l'
  have hP (a : Axis) := portD_budget k hj F' l' (fun i => i.property) (fun _ => a)
  have hQ := (Moderate.sum Finset.univ _ (hP 0).nonneg (fun a _ => hP a)).mul ((abide_budget k hj F').inv (abide_firm k hk F') fun _ => one_pos)
  let v := fun i => (F' i).land
  have hR := (rails F' l' (fun _ => a)).mul (reverse_rails F' l' fun _ => a)
  have hX := ((hP a).mul hR).mul ((Train.bulb_budget k ht v (fun _ => a)).inv (Train.bulb_firm k hk v _) fun _ => one_pos)
  simp only [inv_one,mul_one] at hQ hX
  have ht := hB.mul (hQ.sub hX)
  dsimp only [F',l',I,v] at *
  unfold gains
  simpa only [he,if_false, fled,yen,div_eq_mul_inv,Pi.neg_apply] using ht

/-- Per-alias bound still on the cube. -/
lemma pilot_cost : Pay (fun i => decay j (l i)) fun i p => pilot k (F i) p (l i) := by
  unfold pilot; apply (ahead_cost k hk hj ht F l).add
  have hg := ((Pay.expose_mask 1 (gains_cost k hk hj ht F l)).times (sig_budget F l 0)).times (sluice_cost k hk ht F)
  apply hg.raise
  intro i; dsimp only; rw [pow_one,mul_one,mul_assoc]
  apply mul_le_of_le_one_right (decay_pos ..).le
  rw [inv_mul_eq_div, div_le_one (pow_pos (grade_pos _) _)]
  nlinarith [grade_ge (l i)]
end Flight
end YM.Next.Free
