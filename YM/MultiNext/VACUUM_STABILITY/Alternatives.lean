import YM.MultiNext.VACUUM_STABILITY.Words
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Org.Theatre

set_option warningAsError false

/-!
# Packing alternatives at one letter

Optional (Mayer or cluster) exponentials really multiplied using their powers. One power per
selected letter, absolute sums. This avoids paying repeating tree counts in the merger. The
fiber lemma also lets us finally sum merged forced data at packs with the full inventory.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum.Alternatives
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Syllable Corona  
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I J : Type*}

private lemma powers_approach : Tendsto Finset.powerset (atTop (α:=Finset I)) atTop := by
  refine tendsto_atTop_atTop.mpr fun L => ⟨L.biUnion id,fun U hu b hb => ?_⟩
  exact Finset.mem_powerset.mpr fun i hi => hu (Finset.mem_biUnion.mpr ⟨b,hb,hi⟩)

private lemma accepts {I : Type*} (s : I → Prop) [DecidablePred s] {f : I → ℂ} (h : Summable f) :
    Summable (fun i => if s i then f i else 0) := by
  refine (h.indicator (setOf s)).congr ?_
  intro i; by_cases H : s i <;> simp [Set.indicator,H]

/-- One fiber, arbitrary (finite) target pack. -/
lemma earned [DecidableEq I] [DecidableEq J] (u : I → J) {f : I → ℂ} (h : Summable fun i => ‖f i‖) (s : Finset J) :
    ∏ j∈s, (∑' i, if u i=j then f i else 0) = ∑' b : Finset I,
      if b.image u=s ∧ Set.InjOn u b then ∏ i∈b,f i else 0 := by
  have ht : Summable (fun b : Finset I => if b.image u=s ∧ Set.InjOn u b then ∏ i∈b,f i else 0) :=
    accepts _ (summable_finsetProd_of_summable_norm h)
  have hj := ht.hasSum.comp powers_approach
  refine tendsto_nhds_unique ?_ hj
  have he (L : Finset I) : (∑ b ∈ L.powerset, (if b.image u=s ∧ Set.InjOn u b then ∏ i∈b,f i else 0)) =
      ∏ j∈s, ∑ i∈L, if u i=j then f i else 0 := by
    simp_rw [← sum_filter]; exact (Multi.unique_fibers_prod u f L s).symm
  change Tendsto (fun L : Finset I => (∑ b∈L.powerset, if b.image u = s ∧ Set.InjOn u b then ∏ i∈b, f i else 0)) _ _
  simp_rw [he]; exact tendsto_finsetProd s (fun i _ => (accepts _ h.of_norm).hasSum)

/-- Group an absolute system by its opportunities `u`; repeats of `u` forbidden,
external rule on the total set of occupied slots. -/
lemma classify [DecidableEq I] [DecidableEq J] (u : I → J) {f : I → ℂ} (h : Summable fun i => ‖f i‖) (P : Finset J → Prop) [DecidablePred P] :
    (∑' s : Finset J, if P s then ∏ j∈s,(∑' i, if u i=j then f i else 0) else 0) = ∑' b : Finset I,
      if P (b.image u) ∧ Set.InjOn u b then ∏ i∈b,f i else 0 := by
  let q (B : Finset I) := if P (B.image u) ∧ Set.InjOn u B then ∏ i∈B,f i else 0
  have hf := (accepts (f:=fun b : Finset I => ∏ i∈b,f i) (fun B : Finset I => P (B.image u) ∧ Set.InjOn u B)
    (summable_finsetProd_of_summable_norm h))
  have hs : Summable q := hf
  refine Eq.trans ?_ (hs.hasSum.tsum_fiberwise (fun B : Finset I => B.image u)).tsum_eq
  refine tsum_congr fun b => ?_
  rw [_root_.tsum_subtype]
  by_cases H : P b
  · rw [if_pos H, earned u h b]; refine tsum_congr fun i => ?_
    by_cases he : i.image u=b
    · by_cases hh : Set.InjOn u i <;> simp [q,Set.indicator,H,he,hh]
    simp [Set.indicator,he]
  rw [if_neg H]; symm
  refine (tsum_congr (g:=fun _ => 0) ?_).trans tsum_zero
  intro i; by_cases he : i.image u = b <;> simp [Set.indicator,H,he,q]

abbrev Choices (I : Type*) := I × ℕ

def spice (z : ℂ) (k : ℕ) := ((↑(k+1).factorial:ℂ)⁻¹)*z^(k+1)
def honey (t : ℝ) (k : ℕ) := ((↑(k+1).factorial:ℝ)⁻¹)*t^(k+1)



lemma paid {t : ℝ} (ht : 0 ≤ t) (hk : t ≤ 1/2) : SumBudget (honey t) (2*t) := by
  refine Absolute.compare (Absolute.geometric ht hk) (fun i => by unfold honey; positivity) fun i => ?_
  unfold honey; exact mul_le_of_le_one_left (pow_nonneg ht _) (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos _))

lemma splice (z : ℂ) : HasSum (spice z) (Complex.exp z - 1) := by
  unfold spice; simpa using (hasSum_nat_add_iff' 1).mpr (Absolute.cexp z)

def heat (f : I → ℂ) (i : Choices I) := spice (f i.1) i.2

lemma grouped (f : I → ℂ) (h : Summable f) (hg : Summable fun i => ‖heat f i‖) :
    Complex.exp (∑' i, f i) = ∑' b : Finset (Choices I), if Set.InjOn (Prod.fst : Choices I → I) b then ∏ i∈b,heat f i else 0 := by
  let v i := ∑' j, heat f (i,j)
  have hv i : v i=Complex.exp (f i)-1 := (splice (f i)).tsum_eq
  have hA : Summable v := hg.of_norm.prod
  have ht (i : I) : v i = ∑' j : Choices I, if j.1=i then heat f j else 0 := by
    rw [(accepts (fun j : Choices I => j.1=i) hg.of_norm).tsum_prod]
    rw [tsum_eq_single i]; simp [v]
    intro b hb; simp [hb]
  calc
    _ = ∏' i, (1+v i) := by
      rw [show (fun i => 1+v i) = Complex.exp ∘ f by ext i; rw [hv]; simp]; exact h.hasSum.cexp.tprod_eq.symm
    _ = ∑' b : Finset I, ∏ i∈b, v i := tprod_one_add (summable_finsetProd_of_summable_norm hA.norm)
    _ = _ := by
      have hs := classify (I:=Choices I) (J:=I) Prod.fst hg (fun _ => True)
      simpa only [← ht,if_true,true_and] using hs

section
variable {n : Side}

/-- Raise additive letter hits to exponential-power choice hits. Distinct choice used at most once;
at any one occurrence keep the chosen repeat count in its address. -/
lemma charges (X : I → Support n) (h : ∀ i, (X i).Nonempty) {f : I → ℝ} {a c : ℝ} (M : ℕ)
    (hh : Ac.Hit X M f a c) (ha : 0 ≤ a) (hk : c ≤ 1/2) :
    Ac.Hit (fun i : Choices I => X i.1) M (fun i => honey (f i.1) i.2) a (2*c) := by
  have hp := (Absolute.burden h hh).1
  let e i := Real.exp (a*coverNumber M (X i))
  have he i : 0 ≤ e i := (Real.exp_pos _).le
  have hF i : SumBudget (honey (f i)) (2*f i) := by
    apply paid (hp i); obtain ⟨x,hx⟩ := h i
    refine (le_mul_of_one_le_right (hp i) (show 1 ≤ e i from Real.one_le_exp (by positivity))).trans ?_
    refine le_trans ?_ hk
    simpa only [if_pos hx,e] using Absolute.little (hh x) i
  intro x
  let t (i : Choices I) := if x ∈ X i.1 then honey (f i.1) i.2 * e i.1 else 0
  have hl i : SumBudget (fun j => t (i,j)) (2*(if x ∈ X i then f i*e i else 0)) := by
    by_cases hx : x ∈ X i
    · rw [if_pos hx,mul_comm (f i),mul_left_comm 2]; simp_rw [t,if_pos hx,mul_comm (honey _ _)]; exact permit_mul (hF _) (he _)
    simp [t,hx,SumBudget]
  have hw i : 0 ≤ t i := (hl i.1).1 _
  have hu := Absolute.compare (permit_mul (hh x) (by norm_num : (0:ℝ) ≤ 2)) (fun i => tsum_nonneg (hl i).1)
    fun i => (hl i).2.2
  have hT : Summable t := (summable_prod_of_nonneg hw).2 ⟨fun i => (hl i).2.1,hu.2.1⟩
  exact ⟨hw,hT,hT.tsum_prod.trans_le hu.2.2⟩
end
end YM.Multi.Vacuum.Alternatives
