import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.ITERATION_NO_LOSS.Sums
import YM.Work.B04

/-!
# Contour/physical regular norms and fixed-period parameter continuity

`Shoot.deviation` only used on one period. Its support exponential is on
`coverNumber` of the *torus* support (not unwrapped path length). Thus we
can upgrade a slightly smaller exponent for continuity **but not for the
uniform E,K size estimates**. Fixed lists, same masks, thresholds and at
least the full derivative order and direction power still required. Parameter
variation, not regularity of K as a function of the link variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Comparison
open Function Lattice Wilson RG Shoot Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
structure HasJets (s q : BudgetPoint) : Prop where
  threshold : s.threshold=q.threshold
  order : q.order ≤ s.order
  power : q.power ≤ s.power

namespace HasJets
variable {s q : BudgetPoint} (h : HasJets s q)
include h
lemma dirs (x : Site n) {A : Directions G n} (he : q.dirBound x A) : s.dirBound x A := by
  intro e; apply (he e).trans; rw [h.threshold]; gcongr; exacts [q.threshold_pos.le,by simp,h.power]
lemma sup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P : Support n} {U : Config G n → E} {o b} (he : s.supBounds o P U b) :
    q.supBounds o P U b := ⟨he.1,fun V hv l hl hx => he.2 V (h.threshold.symm ▸ hv) l (hl.trans h.order) (fun i hi => h.dirs o (hx i hi))⟩
lemma regular {A : Activities G n} (hs : A.RegularFamily s) : A.RegularFamily q where
  at_flat := hs.at_flat
  vanish := hs.vanish
  smooth i := { (hs.smooth i) with
    smooth := fun U he => ((hs.smooth i).smooth U (h.threshold.symm ▸ he)).of_le (by exact_mod_cast h.order)
    hasDerivs := fun U he a l hl => (hs.smooth i).hasDerivs U (h.threshold.symm ▸ he) a l (hl.trans_le h.order) }
lemma forced {A : Activities G n} (hs : A.ForcedFamily s) : A.ForcedFamily q := { hs with
    reads := h.threshold ▸ hs.reads
    reads_test := h.threshold ▸ hs.reads_test
    permit := h.threshold ▸ hs.permit }

private def overhead (s : BudgetPoint) (n : Side) := Real.exp (s.supportExponent * Fintype.card (Site n))
omit h in
private lemma cover_money (s : BudgetPoint) (P : Support n) : Real.exp (s.supportExponent * coverNumber s.B P) ≤ overhead s n := by
  obtain ⟨D,_,hd⟩ := coverNumber_realized s.B P
  rw [← hd, overhead, Real.exp_le_exp]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ D) s.exponent_pos.le

lemma varies {U V : Config G n → ℝ} {X : RegularAddress n} {c : ℝ} (hc : variesRegular s X U V c) : variesRegular q X U V c :=
  ⟨hc.1,fun t ht l hl hi => hc.2 t (h.threshold.symm ▸ ht) l (hl.trans h.order) (fun i hl => h.dirs _ (hi i hl))⟩

lemma deviation_price {U V : Activities G n} {δ : ℝ} (hd : deviation s U V δ) : deviation q U V (overhead q n*δ) := by
  obtain ⟨c,d,hc,hd,ht,hf⟩ := hd
  have he (f : ℕ → Support n) (u : ℕ → ℝ) (hu : ∀ i : ℕ, 0 ≤ u i) (hf : SumBudget (fun i => s.mass (f i) (u i)) δ) :
      SumBudget (fun i => q.mass (f i) (u i)) (overhead q n*δ) := by
    refine Cost.mono (Cost.scale hf _ (Real.exp_pos _).le) (fun i => mul_nonneg (Real.exp_pos _).le (hu i)) fun i => ?_
    exact (mul_le_mul_of_nonneg_right (cover_money q (f i)) (hu i)).trans (mul_le_mul_of_nonneg_left (s.loMass _ _ (hu i)) (Real.exp_pos _).le)
  exact ⟨c,d,fun i => h.varies (hc i),hd,he _ _ (fun i => (hc i).1) ht,he _ _ (fun i => (hd i).1) hf⟩

lemma across {F : ℝ → Rep G n} {S : Set ℝ} (hc : Curve s F S) : Curve q F S := by
  refine { hc with continuous := fun ε he x hx => ?_ }
  let C := overhead q n; have hC : 0 < C := Real.exp_pos _
  filter_upwards [hc.continuous _ (div_pos he hC) x hx] with y hy
  have he := h.deviation_price hy; rwa [show overhead q n * (ε/C) = ε by change C*_=_; field_simp] at he
end HasJets

/-- This relation transfers also the size estimates (we require exact B
handoff here). Neither direction changes the hard flag threshold. -/
structure HasBudget (s q : BudgetPoint) : Prop extends HasJets s q where
  B : s.B=q.B
  exponent : q.supportExponent ≤ s.supportExponent
namespace HasBudget
variable {s q : BudgetPoint} (h : HasBudget s q)
include h
lemma mass (X : Support n) {c : ℝ} (hc : 0 ≤ c) : q.mass X c ≤ s.mass X c := by unfold BudgetPoint.mass; rw [h.B]; gcongr; exact h.exponent
lemma eBound {A : Activities G n} {δ v : ℝ} (hd : A.EBound s v) (he : v ≤ δ) : A.EBound q δ := by
  obtain ⟨b,hb,hB⟩ := hd
  refine ⟨b,fun i => h.toHasJets.sup (hb i),fun x => Cost.enlarge (Cost.mono (hB x) ?_ ?_) he⟩
  · intro i; split
    · exact mul_nonneg (Real.exp_pos _).le (hb i).1
    exact le_rfl
  intro i; split <;> simp [*,h.mass _ (hb i).1]
lemma kBound {A : Activities G n} {δ v : ℝ} (hd : A.KBound s v) (he : v ≤ δ) : A.KBound q δ := by
  obtain ⟨b,hb,hB⟩ := hd
  refine ⟨b,hb,fun x => Cost.enlarge (Cost.mono (hB x) ?_ ?_) he⟩
  · intro i; split
    · exact mul_nonneg (Real.exp_pos _).le (hb i).1
    exact le_rfl
  intro i; split <;> simp [*,h.mass _ (hb i).1]
lemma valid {A : Activities G n} {δ w v u : ℝ} (hs : A.Valid s v u) (he : v ≤ δ) (hw : u ≤ w) : A.Valid q δ w :=
  { hs with regular := h.toHasJets.regular hs.regular
            forced := h.toHasJets.forced hs.forced
            boundE := h.eBound hs.boundE he
            boundK := h.kBound hs.boundK hw }
end HasBudget
end YM.Extra.Iteration.Comparison
