import YM.Further.CURVED_GAUSSIAN_JETS.Doses
import YM.Further.CURVED_GAUSSIAN_JETS.Sales
import YM.Further.CURVED_GAUSSIAN_JETS.Signed

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tree Lattice Wilson RG Precision Bid Exterior SectorNext.Vacuum Pockets Work Set Metric Matrix Function Filter WardBin.Lies Push.Uniform Progress.StationaryScenes Pressure Shape Next.Fluctuations Jets
open Green (wt)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {I J : Type*} [Fintype I] [Fintype J] {V : Config G c}
    {a : I→ Site f} {b : J → Site f} {r : Ratio c f} {o : Site f} {t δ C D v w : ℝ} (ht : 0≤t) (hδ : 0<δ) {k q : ℕ} {Q : Directions G c→Prop}

namespace Stock
variable {A : Jets.Field G c I} {B : Jets.Field G c J}
lemma joint_buy {m : I⊕J → Site f} (s : Jets.Weights m) (h : Stock w Q (s.restrict Sum.inl) k A V C) (h' : Stock w Q (s.restrict Sum.inr) k B V C) : Stock w Q s k (fun u=> Joint.join (A u) (B u)) V C := by
  refine ⟨h.has,?_, fun l hl hd=> ?_⟩
  · rintro (i|i) (j|j); exact h.good i j; exact contDiffAt_const; exact contDiffAt_const; exact h'.good i j
  have he : jet l (fun u=>Joint.join (A u) (B u)) V = Joint.join (jet l A V) (jet l B V) := by
    ext (i|i) (j|j) <;> simp [jet,Joint.join,G07.left_const]
  have hp (A : Table I) (B : Table J) (h : (s.restrict Sum.inl).Costs w l.length A C) (h' : (s.restrict Sum.inr).Costs w l.length B C) : s.Costs w l.length (Joint.join A B) C := by
    rintro (i|j) <;> rw [Fintype.sum_sum_type]
    · simpa only [Joint.join, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,abs_zero,mul_zero,Finset.sum_const_zero,add_zero] using! h i
    simpa only [Joint.join, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, abs_zero, mul_zero,Finset.sum_const_zero,Matrix.fromBlocks_apply₂₂, zero_add] using! h' j
  rw [he]; exact ⟨hp _ _ (h.cash l hl hd).1 (h'.cash l hl hd).1, by unfold Joint.join; rw [fromBlocks_transpose,transpose_zero,transpose_zero]; exact hp _ _ (h.cash l hl hd).2 (h'.cash l hl hd).2⟩

lemma sum {X : Type*} (E : X → Jets.Field G c I) {s : Jets.Weights a} (Z : Finset X)
    (h : ∀ i∈Z, Stock w Q s k (E i) V C) : Stock w Q s k (fun u=> ∑ i∈Z, E i u) V (Z.card*C) := by
  induction Z using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact ⟨by simp,Jets.Good.const 0, fun l hl hd=> by rw [jet_const,ite_self]; apply Weights.zero; simp⟩
  | insert a t ha ih =>
    simp_rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha]; push_cast
    rw [add_mul,one_mul,add_comm]; exact (h a (Finset.mem_insert_self ..)).plus (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
lemma avg {E : Signed → Jets.Field G c I} {s : Jets.Weights a} (h : ∀ i, Stock w Q s k (E i) V C) : Stock w Q s k (fun u=>Rot.average (fun i=> E i u)) V C := by
  have he := (Stock.sum E Finset.univ (fun i _=> h i)).scale ((Fintype.card Signed:ℝ)⁻¹)
  rw [abs_of_pos (inv_pos.mpr Rot.normal),Finset.card_univ,inv_mul_cancel_left₀ Rot.normal.ne'] at he
  convert he using 1; funext u; ext i j; simp [Rot.average, Matrix.sum_apply]
end Stock

variable [DecidableEq J] {X : Type*} [Fintype X] {e : I⊕J ≃ X} {loc : X → Site f} {A : Jets.Field G c I}
lemma completed (h : Stock w Q (rule (loc ∘ e ∘ Sum.inl) o q ht hδ) k A V C) : Stock w Q (rule loc o q ht hδ) k (fun u=>Joint.place e (Joint.join (A u) 1)) V (max 1 C) := by
  let s := rule (loc ∘ e) o q ht hδ
  have hf : Stock w Q (s.restrict Sum.inr) k (fun _=> (1:Table J)) V 1 := ⟨zero_le_one, Jets.Good.const _, Jets.cash_one⟩
  have he := (Stock.joint_buy s (h.larger (le_max_right 1 C)) (hf.larger (le_max_left 1 C))).restrict e.symm.toEmbedding
  have hb : (loc ∘ ⇑e) ∘ ⇑e.symm = loc := funext fun i=> by simp
  -- dependent rewrite at he
  change Stock w Q (rule ((loc ∘ ⇑e) ∘ ⇑e.symm) o q ht hδ) k _ V (max 1 C) at he
  rw [hb] at he; exact he
end YM.Further.CurvedGaussianJets.ChangeV
