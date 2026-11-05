import YM.MultiNext.VACUUM_STABILITY.FirstGas

set_option warningAsError false

/-!
# A single countable output, padded as required by MULTISOURCE
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

namespace Pad
variable {A F : Type*} {I J : Type}

def pick (I : Type) [Countable I] : ℕ ≃ (I ⊕ ℕ) := Classical.choice nonempty_equiv_of_countable

def wide [Countable I] (f : I → A) (a : A) := Sum.elim f (fun _ => a) ∘ pick I

lemma all [Countable I] (f : I → A) (a : A) (P : A → Prop) (i : ℕ) (hf : ∀ i,P (f i)) (ha : P a) : P (wide f a i) := by
  unfold wide; dsimp only [Function.comp_apply]; obtain x|x := pick I i
  · exact hf _
  exact ha

lemma wider [Countable I] (f : I → A) (a : A) (g : I→F) (b : F) (P : A → F → Prop) (i : ℕ)
    (hf : ∀ i,P (f i) (g i)) (hh : P a b) : P (wide f a i) (wide g b i) := by
  unfold wide; dsimp only [Function.comp_apply]; obtain x|x:=pick I i
  · exact hf _
  exact hh

lemma padding_left {f : I ⊕ J → ℂ} (hg : ∀ j : J,f (.inr j)=0) : ∑' i,f i=∑' i,f (.inl i) := by
  symm
  apply Sum.inl_injective.tsum_eq
  rintro (i|j) H
  · exact ⟨i,rfl⟩
  exact False.elim (H (hg _))

lemma padding_right {f : I ⊕ J → ℂ} (hg : ∀ j : I,f (.inl j)=0) : ∑' i,f i=∑' i,f (.inr i) := by
  symm
  apply Sum.inr_injective.tsum_eq
  rintro (i|j) H
  · exact False.elim (H (hg _))
  exact ⟨j,rfl⟩

lemma wide_sum [Countable I] (f : I → A) (a : A) (u : A → ℂ) (h : u a=0) :
    ∑' i, u (wide f a i)=∑' i,u (f i) :=
  ((pick I).tsum_eq (u ∘ Sum.elim f fun _ => a)).trans <| padding_left fun _ => h

lemma wide_cost [Countable I] (f : I → A) (a : A) (g : I → ℝ) (u : A → ℝ → ℝ) (hx : u a 0=0) {c : ℝ}
    (h : SumBudget (fun i => u (f i) (g i)) c) : SumBudget (fun i => u (wide f a i) (wide g 0 i)) c := by
  let x (i : I ⊕ ℕ) := u (Sum.elim f (fun _ => a) i) (Sum.elim g (fun _ => 0) i)
  have ht : SumBudget (x ∘ Sum.inr) 0 := by simp [x,hx,Function.comp_def,SumBudget]
  have hh := Absolute.union (f:=x) h ht
  rw [add_zero] at hh
  exact ⟨fun i => hh.1 _, (pick I).summable_iff.mpr hh.2.1, ((pick I).tsum_eq _).trans_le hh.2.2⟩
end Pad

variable {V I J : Type} {n : Side} {G : Gauge} [Countable I] [Countable J]

/-- packaging lemma, exposed also for other constructions of the reservoir -/
structure Armoire (V : Type) (G : Gauge) (n : Side) (I J : Type) where
  e : I → SmoothLetter V G n
  k : J → Pack n × Stamp V (Config G n)
  pay : V → ℂ

namespace Armoire
variable (Y : Armoire V G n I J)

private def spare : SmoothLetter V G n := { zone := {0}, stamp := ⟨0,0⟩, anchor := 0, origin := by simp }
private def gap : Pack n × Stamp V (Config G n) := ⟨⟨⟨{0},{0}⟩,by simp⟩,0,0⟩

def dressed (P : Rep G n) : Reservoir P V where
  support i := (Pad.wide Y.e spare i).zone
  D i := (Pad.wide Y.e spare i).stamp.say
  k i := (Pad.wide Y.k gap i).1
  K i := (Pad.wide Y.k gap i).2.say
  pay := Y.pay

variable (P : Rep G n)

omit [Countable I] [Countable J] in
structure Complete (L : V → Support n → Prop) : Prop where
  letters i : let w := Y.e i
    P.p.Regular w.zone w.stamp.ink ∧ (∀ x∈w.stamp.name.support,L x w.zone) ∧ (w.stamp.name=0 → w.stamp.ink=0)
  holder i : let w := (Y.k i).2; let q := (Y.k i).1
    Legible P.p q w.ink ∧ (∀ x∈w.name.support,L x q.zone) ∧ (w.name=0 → w.ink=0)

variable [Fintype V]



structure Insured (A : Set (V→ℂ)) (κ : ℝ) : Prop where
  earns z : z ∈ A → ∃ f, (∀ i, 0 ≤ f i ∧ ∀ x∈(Y.e i).zone,P.p.supBounds x (Y.e i).zone ((Y.e i).stamp.tell z) (f i)) ∧
    Ac.Hit (fun i => (Y.e i).zone) P.p.B f (Rates.radius P.p) 1
  guns z : z ∈ A → ∃ f, (∀ i, 0 ≤ f i ∧ ∀ U, ‖(Y.k i).2.tell z U‖ ≤ f i) ∧
    Ac.Hit (fun i => (Y.k i).1.zone) P.p.B f (Rates.radius P.p) κ






end Armoire
end YM.Multi.Vacuum
