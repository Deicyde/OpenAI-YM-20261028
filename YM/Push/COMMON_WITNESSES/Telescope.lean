import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Work.B06

/-!
# Replacing arrays on a single aligned tiling

 elementary but conditional on actual full root estimates. We'll
use it to relate the Grill supplier's problem in transport to one other
quantitative per-field problem in *centred* cells. No normalizing with a
product of independent-cell measures; the root is already for the full
copies with the same Wilson law.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Lattice MeasureTheory Next.Extract Wilson OS
open scoped Topology BigOperators ContDiff

variable {G : Gauge} {m : Side} (T : Tiling m) {ι : Type*} [Fintype ι]
variable (c : ι → T.Cell)

/-- Send initial-cell entries to each required address. -/
def stageProduct (F : ι → Config G m → ℂ) (U : Config G m) := ∏ i, T.copy (c i) (F i) U

lemma lawful {β : ℝ} (F : ι → Config G m → ℂ) (hF : ∀ i, Interior (T.chamber 0) (F i)) :
    Integrable (stageProduct T c F) (law G _ β) := by
  have h : Interior univ (stageProduct T c F) := Interior.combines _ _ fun i _ =>
    (T.copies (c i) (hF i)).enlarges (subset_univ _)
  exact h.integrable _

lemma less_f {K : Set (Site m)} {F P : Config G m → ℂ} (h : Interior K F) (he : Interior K P) : Interior K (F-P) := by
  have hx : F-P = fun U => F U + (-1:ℂ)*P U := by funext x; simp [sub_eq_add_neg]
  rw [hx]; exact h.plus (he.scale _)

/-- Quantitative comparison before sending hierarchy/Grill questions to
further orders. Hypothesis at *one* cutoff. Use a spare factor of B≥1 to
cover the empty product case without denominator. -/
theorem replacing {β : ℝ} (H : Seam G m β) (hc : Injective c) (F P : ι → Config G m → ℂ)
    (B δ : ℝ) (hb : 1 ≤ B) (hδ : 0 ≤ δ) (hi : ∀ i, Interior (T.chamber 0) (F i) ∧ Interior (T.chamber 0) (P i) ∧
      T.rootTest β (F i) ≤ B ∧ T.rootTest β (P i) ≤ B ∧ T.rootTest β (P i-F i) ≤ δ) :
    ‖moment β (stageProduct T c P) - moment β (stageProduct T c F)‖ ≤ Fintype.card ι * (δ * B ^ Fintype.card ι) := by
  classical
  let e (s : Finset ι) i := if i∈s then P i else F i
  let u := Finset.univ (α:=ι)
  have he (s i) : Interior (T.chamber 0) (e s i) ∧ T.rootTest β (e s i)≤B := by
    unfold e; split; exact ⟨(hi _).2.1,(hi _).2.2.2.1⟩; exact ⟨(hi _).1,(hi _).2.2.1⟩
  let L (s : Finset ι) := moment β (stageProduct T c (e s))
  have h1 (s : Finset ι) (i : ι) (h : i ∉ s) : ‖L (insert i s)-L s‖ ≤ δ*B^Fintype.card ι := by
    let p := update (e s) i (P i - F i)
    have hP (j : ι) : Interior (T.chamber 0) (p j) := by
      by_cases hv : j=i
      · subst j; unfold p; rw [update_self]; exact less_f (hi i).2.1 (hi i).1
      unfold p; rw [update_of_ne hv]; exact (he _ _).1
    have ht (U : Config G m) : stageProduct T c p U = stageProduct T c (e (insert i s)) U - stageProduct T c (e s) U := by
      let M (Q : ι → Config G m → ℂ) := ∏ j ∈ u.erase i, T.copy (c j) (Q j) U
      have hW (Q : ι → Config G m → ℂ) : stageProduct T c Q U = T.copy (c i) (Q i) U * M Q :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
      have hu : M (e s)=M p := Finset.prod_congr rfl fun j hj => by rw [show p j=e s j from update_of_ne (Finset.mem_erase.mp hj).1 ..]
      have hZ : M (e (insert i s))=M (e s) := Finset.prod_congr rfl fun j hj => by simp [e,(Finset.mem_erase.mp hj).1]
      rw [hW,hW,hW,hZ,hu, ← sub_mul]
      dsimp only [p,e]; rw [update_self, if_pos (Finset.mem_insert_self ..), if_neg h]; unfold Tiling.copy
      split_ifs <;> simp
    unfold L moment; rw [← integral_sub (lawful T c _ fun i => (he _ i).1) (lawful T c _ fun i => (he _ i).1)]
    simp_rw [← ht]
    apply le_trans (T.planted H c hc p hP)
    rw [← Finset.mul_prod_erase u (fun j => T.rootTest β (p j)) (Finset.mem_univ i)]
    have h0 : 0≤T.rootTest β (p i) := T.root_nonneg ..
    have h2 : T.rootTest β (p i) ≤ δ := by unfold p; rw [update_self]; exact (hi i).2.2.2.2
    apply mul_le_mul h2 _ (Finset.prod_nonneg fun j _ => T.root_nonneg ..) hδ
    calc
      _ ≤ ∏ _ ∈ u.erase i, B := Finset.prod_le_prod (fun j _ => T.root_nonneg ..) (fun j hj => by
        rw [show p j=e s j from update_of_ne (Finset.mem_erase.mp hj).1 ..]; exact (he _ _).2)
      _ ≤ _ := by
        rw [Finset.prod_const]; exact pow_le_pow_right₀ hb (Finset.card_le_univ _)
  have hyp (s : Finset ι) : ‖L s-L ∅‖ ≤ s.card * (δ*B^Fintype.card ι) := by
    induction s using Finset.induction_on with
    | empty => simp only [sub_self,norm_zero,Finset.card_empty, Nat.cast_zero, zero_mul, le_refl]
    | insert i s hx ih =>
      refine (norm_sub_le_norm_sub_add_norm_sub _ (L s) _).trans ((add_le_add (h1 s i hx) ih).trans_eq ?_)
      rw [Finset.card_insert_of_notMem hx,Nat.cast_add]; ring
  simpa only [L,e,u,Finset.mem_univ,Finset.notMem_empty,↓reduceIte,Finset.card_univ] using hyp u
end YM.Push.Common
