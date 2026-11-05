import YM.Next.WARD_BIN.Bundles
import YM.Source.Insertion


/-!
# Deposits at actual alphabet positions, order one

Needs enough positions to realize geometric selections. Require here **one**
index per shape with extraTest allowing all corresponding flags; no post hoc enlargement to
a different `Activities`. Not inferred from `Valid`. Budgets inclusive of
actual flags (via `offer`) and one-for-one support exponent, to use with κ later.
Proves density coefficient equality for any supported address choices having
same grouped offers (needn't all use the same Pad).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Gas
open Function Filter Finset Lattice Wilson RG Source Ac MeasureTheory
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {A : Activities G n} {R : Rep G n}
  {p : BudgetPoint} {δ w : ℝ}

/-- An input at startup. Circle obligations include enough actual indices
at the following levels too. -/
structure Pad (A : Activities G n) (p : BudgetPoint) where
  site : Shape n → ℕ
  for_shape (i) : shape A (site i)=i
  tests i U : wall i∩flags p.threshold U=inv i → (A.forced (site i)).extraTest U

/-- Deposit entries remain on original labels, including gauge invariance
and support for evaluations even of the forced pieces at unselected U. -/
structure Kept (p : BudgetPoint) (a : ForcedAddress G n) (X : Support n) (f : Config G n → ℂ) : Prop where
  allowed U : f U ≠ 0 → a.eligible p.threshold U
  carries : f≠0 → X⊆a.support
  sym : GaugeInvariant f
  borel : Measurable f
  uses : UsesFinal p.threshold a.support f
lemma empty (a : ForcedAddress G n) (X : Support n) : Kept p a X 0 :=
  ⟨fun _ h => (h rfl).elim,fun h => (h rfl).elim,fun _ _ => rfl,measurable_const,fun _ _ _ _ => rfl⟩

namespace Pad
variable (D : Pad A p)

-- Each f could be complex-valued, or a budget bound itself.
def lay {R : Type*} [Zero R] (f : Shape n→R) (i : ℕ) := if D.site (shape A i)=i then f (shape A i) else 0
lemma ready {R : Type*} [Zero R] (f : Shape n→R) (j) : D.lay f (D.site j)=f j := by simp [lay,D.for_shape]

lemma tries {R : Type*} [AddCommMonoid R] [TopologicalSpace R] (f : Shape n→R) (j) :
    bucket A (D.lay f) j=f j := by
  unfold bucket; rw [tsum_eq_single (D.site j)]; simp [D.ready,D.for_shape]
  intro i hi
  split_ifs with he
  · unfold lay; rw [he]; exact if_neg (Ne.symm hi)
  rfl
lemma function_lay {R V : Type*} [Zero R] (f : Shape n→V→R) (v : V) (i : ℕ) :
    D.lay f i v=D.lay (f · v) i := by unfold lay; split_ifs <;> rfl
lemma staged {R V : Type*} [AddCommMonoid R] [TopologicalSpace R] (f : Shape n→V→R) (v j) :
    bucket A (fun i => D.lay f i v) j=f j v := by simp_rw [D.function_lay]; exact D.tries _ _
lemma injective : Injective D.site := Function.LeftInverse.injective D.for_shape

lemma keeper {X : Support n} {f : Shape n→Config G n→ℂ} (h : ∀ i,Boxed p i X (f i)) (i) :
    Kept p (A.forced i) X (D.lay f i) := by
  unfold lay; split
  · rename_i H
    let z := shape A i
    have hh : (A.forced i).support=wall z := rfl
    have hf (U) (he : wall z ∩ flags p.threshold U=inv z) : (A.forced i).extraTest U := H ▸ D.tests z U he
    exact ⟨fun U he => ⟨(h z).born U he,hf U ((h z).born U he)⟩,(h z).needed,(h z).sym,(h z).borel,(h z).vicinity⟩
  exact YM.WardBin.Gas.empty ..

lemma cash {f : Shape n → Config G n → ℂ} {K : Shape n → ℝ}
    (hk : ∀ i, 0 ≤ K i) (h : ∀ i U, ‖f i U‖ ≤ K i) :
    SumBudget (fun i => p.mass (A.forced i).support (D.lay K i)) (∑ i,p.mass (wall i) (K i)) ∧
      ∀ i,0≤D.lay K i ∧ ∀ U, ‖D.lay f i U‖ ≤ D.lay K i := by
  let g (i : ℕ) := p.mass (A.forced i).support (D.lay K i)
  let J := univ.image D.site
  have ht (i : ℕ) : 0≤D.lay K i := by unfold lay; split; exact hk _; exact le_rfl
  have hJ : ∀ i∉J,g i=0 := by
    intro i hi; simp only [g,BudgetPoint.mass,lay]
    rw [if_neg (fun H => hi (mem_image.mpr ⟨shape A i,mem_univ _,H⟩)),mul_zero]
  refine ⟨⟨fun i => mul_nonneg (Real.exp_pos _).le (ht _),summable_of_ne_finset_zero hJ,?_⟩,fun i => ⟨ht _,fun U => ?_⟩⟩
  · change (∑' i,g i) ≤ _
    rw [tsum_eq_sum hJ]
    unfold J g; rw [sum_image D.injective.injOn]
    exact (sum_congr rfl (fun i _ => by
      change p.mass (wall (shape A (D.site i))) _=_; rw [D.for_shape,D.ready])).le
  rw [function_lay]; unfold lay; split; exact h _ _; simp
end Pad



def hop (A : Activities G n) (p : BudgetPoint) (X : Support n) (f : Config G n→ℂ) (i : Shape n) (U : Config G n) :=
  tag X (flags p.threshold U) (f U) (fun j => (vacuum A U j:ℂ)) i
lemma offered_hop (p : BudgetPoint) (X : Support n) (f : Config G n → ℂ) (i : Shape n) :
    hop A p X f i=offer (fun _ : Unit => X) (fun _ => f) A p.threshold {()} i := by
  funext U; exact (singleton_till (fun _ : Unit => X) (fun _ => f U) (fun j => (vacuum A U j:ℂ)) _ () i).symm

lemma tangents {o : Site n} {d : ℕ} {F : Labels.Frame G d} {P : Coefficient F n}
    {h K} (ht : P.remBound o R h K) : Dominated P.forced := by
  obtain ⟨X,Y, _, _, _, _, _, ⟨k,hk,hK⟩⟩ := ht
  exact ⟨k,hk.2.1.of_nonneg_of_le (fun i => (hK i).1) (fun i => R.p.loMass _ _ (hK i).1),fun i => (hK i).2⟩

section Vital
variable {d : ℕ} {F : Labels.Frame G d} (P : Coefficient F n) {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w)





lemma holds_sub {f g : ℕ → ℂ} (hf : Summable f) (hg : Summable g) (i : Shape n) :
    bucket A (fun i => f i-g i) i=bucket A f i-bucket A g i := by
  unfold bucket; rw [← (summable_ite hf _).tsum_sub (summable_ite hg _)]; refine tsum_congr fun j => ?_; split_ifs <;> simp



include h


end Vital

lemma write_tag (D : Pad A p) {X : Support n} {f : Config G n→ℂ} (hh : Fault p X f)
    (h : A.ForcedFamily p) (i) : Kept p (A.forced i) X (D.lay (hop A p X f) i) :=
  D.keeper (fun i => by simpa [offered_hop] using! collect h ({()}:Finset Unit) (fun _ => hh) i) _

lemma ink_tag (D : Pad A p) (X : Support n) {f : Config G n→ℂ} {c : ℝ} (ht : ∀ U, ‖f U‖ ≤ c)
    (h : A.KBound p w) :
    ∃ b : ℕ → ℝ, SumBudget (fun i => p.mass (A.forced i).support (b i)) (p.mass X c*(Real.exp (X.card*w)-1)) ∧
      ∀ i,0≤b i ∧ ∀ U, ‖D.lay (hop A p X f) i U‖ ≤ b i := by
  obtain ⟨e,he,H,hq⟩ := all_cost (fun _ : Unit => X) (singleton_nonempty ()) h (fun _ => ht)
  obtain ⟨⟨hS,hH,hZ⟩,hv⟩ := D.cash he (show ∀ i U,‖hop A p X f i U‖ ≤ e i from by intro i U; rw [offered_hop]; exact H i U) (p:=p)
  exact ⟨_,⟨hS,hH,hZ.trans (by simpa [bill] using hq)⟩,hv⟩
end YM.WardBin.Gas
