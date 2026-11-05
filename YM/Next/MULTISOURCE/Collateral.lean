import YM.Next.MULTISOURCE.Bulk
import YM.Next.MULTISOURCE.Evaluate

/-!
# Cost a single tangent variation
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi

open RG Wilson Lattice Function Pack MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {n : Side} {G : Gauge}

/-- Pack payload before global coverage. -/
structure Legible (P : BudgetPoint) (i : Pack n) (F : Config G n → ℂ) : Prop where
  borel : Measurable F
  symmetry : GaugeInvariant F
  reads : UsesFinal P.threshold i.zone F
  inventory (U : Config G n) : F U ≠ 0 → i.zone ∩ flags P.threshold U=i.flagsAt

namespace Legible
variable {P : BudgetPoint} {q : Pack n} {F F' : Config G n → ℂ}

lemma zero (P : BudgetPoint) (q : Pack n) : Legible P q (0 : Config G n → ℂ) :=
  ⟨measurable_const,fun _ _ => rfl,fun _ _ _ _ => rfl,fun _ h => False.elim (h rfl)⟩

lemma scale (h : Legible P q F) (z : ℂ) : Legible P q (z • F) := by
  refine ⟨measurable_const.smul h.borel,fun i U => by simp only [Pi.smul_apply,h.symmetry i U],
    fun U V hx hy => by simp only [Pi.smul_apply,h.reads U V hx hy],fun U hu => h.inventory U ?_⟩
  intro H; exact hu (by simp only [Pi.smul_apply,H,smul_zero])

lemma add (h : Legible P q F) (h' : Legible P q F') : Legible P q (F+F') := by
  refine ⟨h.borel.add h'.borel,fun i U => by simp only [Pi.add_apply,h.symmetry i U,h'.symmetry i U],
    fun U V hx hy => by simp only [Pi.add_apply,h.reads U V hx hy,h'.reads U V hx hy],?_⟩
  intro U hu; by_cases hv : F U=0
  · exact h'.inventory U (fun H => hu (by rw [Pi.add_apply,hv,H,zero_add]))
  exact h.inventory U hv
end Legible

/-- Price for tangents. Max-like at one key. `c` pays singular denominator at K via κ. -/
def Credit (P : BudgetPoint) (r κ : ℝ) (X : Support n) (D : Pulse G n) (c : ℝ) : Prop :=
    X.Nonempty ∧ 0 ≤ r ∧ 0 < κ ∧ 0 ≤ c ∧
    (∃ (i : ℂ) (F : Config G n → ℂ), D.1=(fun x => i+F x) ∧
      (2 ≤ X.card → i=0) ∧ ‖i‖ ≤ c ∧ Banked P r X F c) ∧
    ∃ f : Pack n → ℝ, (∑ i, burn P r i.zone * f i) ≤ κ*c ∧
      ∀ i : Pack n, Legible P i (D.2 i) ∧ (D.2 i ≠ 0 → X ⊆ i.zone) ∧
        0 ≤ f i ∧ ∀ U, ‖D.2 i U‖ ≤ f i

namespace Credit
variable {P : BudgetPoint} {X : Support n} {r κ a b c : ℝ} {D E : Pulse G n}

lemma zero (P : BudgetPoint) (h : 0 ≤ r) (h' : 0 < κ) (hx : X.Nonempty) :
    Credit P r κ X (0 : Pulse G n) 0 := by
  refine ⟨hx,h,h',le_rfl,⟨0,0,?_,fun _ => rfl, (norm_zero).le,Banked.zero ..⟩,fun _ => 0,?_,?_⟩
  · change (0 : Config G n → ℂ)=_; funext x; simp
  · simp
  intro i; exact ⟨Legible.zero ..,fun H => False.elim (H rfl),le_rfl,fun _ => (norm_zero).le⟩

lemma expand (h : Credit P r κ X D a) (ht : a ≤ b) : Credit P r κ X D b := by
  obtain ⟨hx,h',hv,ha,⟨u,F,hu,ht',hi,H⟩,f,hf,hk⟩ := h
  exact ⟨hx,h',hv,ha.trans ht,⟨u,F,hu,ht',hi.trans ht,H.enlarge ht⟩,f,
    hf.trans (mul_le_mul_of_nonneg_left ht hv.le),hk⟩

lemma scale (h : Credit P r κ X D c) (z : ℂ) : Credit P r κ X (z • D) (‖z‖*c) := by
  obtain ⟨hx,h',hv,ha,⟨u,F,hu,hH,hi,H⟩,f,hf,hk⟩ := h
  refine ⟨hx,h',hv,mul_nonneg (norm_nonneg _) ha,⟨z*u,z • F,?_,fun hh => by rw [hH hh,mul_zero],
    (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left hi (norm_nonneg _)),H.scale z⟩,fun i => ‖z‖*f i,?_,?_⟩
  · funext i; simp [hu,mul_add]
  · simp_rw [mul_left_comm _ ‖z‖, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hf (norm_nonneg _)
  intro i; obtain ⟨HE,hH,hh,hj⟩ := hk i
  change Legible P i (z • D.2 i) ∧ _
  refine ⟨HE.scale z,fun hi => hH fun h => hi ?_,mul_nonneg (norm_nonneg _) hh,fun U => ?_⟩
  · rw [Prod.smul_snd,Pi.smul_apply,h,smul_zero]
  simp only [Prod.smul_snd,Pi.smul_apply,norm_smul]
  exact mul_le_mul_of_nonneg_left (hj U) (norm_nonneg _)

lemma add (h : Credit P r κ X D a) (h' : Credit P r κ X E b) : Credit P r κ X (D+E) (a+b) := by
  obtain ⟨hx,hr,hc,ha,⟨u,F,hu,H,v,hF⟩,f,hf,h⟩ := h
  obtain ⟨-,-,-,hb,⟨u',F',hu',H',v',hF'⟩,f',hf',h'⟩ := h'
  refine ⟨hx,hr,hc,add_nonneg ha hb,⟨u+u',F+F',?_,fun hh => by rw [H hh,H' hh,zero_add],
    (norm_add_le ..).trans (add_le_add v v'),hF.add hF' hx hr⟩,f+f',?_,?_⟩
  · funext i; simp only [Prod.fst_add,Pi.add_apply,hu,hu']; ring
  · simp_rw [Pi.add_apply,mul_add,Finset.sum_add_distrib]; exact add_le_add hf hf'
  intro i; obtain ⟨HE,hz,h₁,h₂⟩ := h i; obtain ⟨HE',hz',h₁',h₂'⟩ := h' i
  refine ⟨HE.add HE',?_, add_nonneg h₁ h₁',fun U =>
    (norm_add_le _ _).trans (add_le_add (h₂ U) (h₂' U))⟩
  intro hh; by_cases he : D.2 i=0
  · apply hz'; intro e; exact hh (by simp [he,e])
  exact hz he

lemma sums {I : Type*} (S : Finset I) (f : I→Pulse G n) (k : I→ℝ) (hv : X.Nonempty)
    (hr : 0≤r) (hc : 0<κ) (h : ∀ i∈S,Credit P r κ X (f i) (k i)) :
    Credit P r κ X (∑ i∈S,f i) (∑ i∈S,k i) := by
  classical
  induction S using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact zero P hr hc hv
  | insert i S hS ih =>
    simp only [Finset.sum_insert hS]
    exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma refund (h : Credit P r κ X D c) (hk : 2 ≤ X.card) : Credit P 0 κ X D (fare P r X*c) := by
  classical
  obtain ⟨hx,h',hv,hc,⟨u,F,hu,hH,_,H⟩,f,hf,h⟩ := h
  have hp : 0 ≤ fare P r X := (Real.exp_pos _).le
  let p i := if D.2 i=0 then 0 else f i
  refine ⟨hx,le_rfl,hv,mul_nonneg hp hc,⟨u,F,hu,hH,?_,H.rebate h'⟩,p,?_,?_⟩
  · rw [hH hk,norm_zero]; exact mul_nonneg hp hc
  · calc
      _ ≤ ∑ i, fare P r X*(burn P r i.zone*f i) := Finset.sum_le_sum fun i _ => by
        have hh : 0 ≤ f i := (h i).2.2.1
        unfold p; split
        · rw [mul_zero]; exact mul_nonneg hp (mul_nonneg (burn_pos ..).le hh)
        rename_i he; exact (mul_le_mul_of_nonneg_right (cheaper P h' ((h i).2.1 he)) hh).trans_eq (mul_assoc ..)
      _ ≤ _ := by rw [← Finset.mul_sum, mul_left_comm κ]; exact mul_le_mul_of_nonneg_left hf hp
  intro i; obtain ⟨hh,hx,h⟩ := h i
  refine ⟨hh,hx,?_⟩
  unfold p; split
  · rename_i he; rw [he]; simp
  exact h
end Credit
end YM.Multi
