import YM.Bid.Fuels
import YM.Next.WARD_BIN.Strands

/-!
# Separate mixed tower cap from singleton shipments

One-way reserve conversion at nonfactorial VT weights (slightly stronger
working stance than a factorial charge for rank≥2). Only separated towers,
actual origins and support, forced budget per marker with one κ. Census chosen
complete. The one-step construction with these actual costs needs work upstream
-- nothing obtained here from RRaw path semantics alone!
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
-- universe 0 V for I01
variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V]
  {w u v c κ' : ℝ} {W : V → ℝ} {R : Rep G n} {r : Census V}

abbrev Full (V : Type) [Fintype V] [DecidableEq V] := Stock.census V
abbrev Mode (V : Type) [Fintype V] [DecidableEq V] := (Full V).Mode
def chest : Finset V≃Mode V where
  toFun i := ⟨i,mem_univ _⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

structure Crest (G : Gauge) (n : Side) (r : Census V) where
  surface : ℕ → Support n
  aims : ℕ → r.Mode
  bits : ℕ → Config G n → ℂ
  creed : ℕ → ℕ → r.Mode
  doses : ℕ → ℕ → Config G n → ℂ

namespace Crest
variable {T : V → Site n} (C : Crest G n r)

structure Green (R : Rep G n) (T : V → Site n) : Prop where
  loaded i : 2 ≤ (C.aims i).val.card
  roots i : (C.aims i).val.image T ⊆ C.surface i
  forms i : R.p.Regular (C.surface i) (C.bits i)
  ranks i j : 2 ≤ (C.creed i j).val.card
  holds i j : Gas.Kept R.p (R.activities.forced i) ((C.creed i j).val.image T) (C.doses i j)

/- High-only budget, at extra support exponent u, e.g. the post-L provisional
purchase for 1. Use coarse witnesses once only. -/
def air (p : BudgetPoint) (X : Support n) (u c : ℝ) := Real.exp ((p.supportExponent+u)*coverNumber p.B X)*c
@[simp] lemma air_mass (p : BudgetPoint) (X : Support n) (c : ℝ) : air p X 0 c=p.mass X c := by simp [air,BudgetPoint.mass]
structure Rich (R : Rep G n) (T : V → Site n) (W : V → ℝ) (u c κ : ℝ) : Prop where
  warms : ∃ k : ℕ → ℝ,(∀ i, 0 ≤ k i) ∧ (∀ i,∀ j∈ (C.aims i).val,R.p.supBounds (T j) (C.surface i) (C.bits i) (k i)) ∧
    ∀ i, SumBudget (fun j => if i∈(C.aims j).val then Poly.toll W (C.aims j)*air R.p (C.surface j) u (k j) else 0) c
  winds : ∃ k : ℕ×ℕ → ℝ,(∀ i,0≤k i) ∧ (∀ i j U,‖C.doses i j U‖ ≤ k (i,j)) ∧
    ∀ i, SumBudget (fun p : ℕ×ℕ => if i∈(C.creed p.1 p.2).val then Poly.toll W (C.creed p.1 p.2)*
      air R.p (R.activities.forced p.1).support u (k p) else 0) (κ*c)

section Air
variable {X : Support n} {P : BudgetPoint} {Q W : V → ℝ}

def Hollow (P : BudgetPoint) (T : V → Site n) := 8≤P.B ∧ ∀ i j,i≠j → P.B^2 ≤ separation (T i) (T j)


end Air
/- Interlace Nat addresses; actual compatibility unchanged. -/

def enr (V : Type) [Fintype V] : (V×ℕ ⊕ ℕ)≃ℕ := Classical.choice inferInstance
def enf (V : Type) [Fintype V] : V⊕ℕ ≃ ℕ := Classical.choice inferInstance
def meld (Q : V → Rib G n) (C : Crest G n r) (R : Rep G n) : Bands r R where
  origins i := (Q i).root
  units i := (Q i).head
  support i := Sum.elim (fun p : V×ℕ => (Q p.1).annals p.2) C.surface ((enr V).symm i)
  rays i := Sum.elim (fun p => r.fire p.1) C.aims ((enr V).symm i)
  H i := Sum.elim (fun p : V×ℕ => (Q p.1).body p.2) C.bits ((enr V).symm i)
  marks i j := Sum.elim (fun v => r.fire v) (C.creed i) ((enf V).symm j)
  entries i j := Sum.elim (fun v => (Q v).band i) (C.doses i) ((enf V).symm j)

@[simp] lemma faces_left (Q : V → Rib G n) (R : Rep G n) (a : V) (b : ℕ) : (meld Q C R).rays (enr V (Sum.inl (a,b)))=r.fire a := by simp [meld]
@[simp] lemma faces_right (Q : V → Rib G n) (R : Rep G n) (b : ℕ) : (meld Q C R).rays (enr V (Sum.inr b))=C.aims b := by simp [meld]
lemma joined {Q : V → Rib G n} (hp : ∀ i,(Q i).Pitched R) (hg : C.Green R fun i => (Q i).root) : (meld Q C R).Active := by
  have he i j : ((meld Q C R).marks i j).val.Nonempty ∧ Gas.Kept R.p (R.activities.forced i) (((meld Q C R).marks i j).val.image (meld Q C R).origins) ((meld Q C R).entries i j) := by
    obtain ⟨j,rfl⟩ := (enf V).surjective j; cases j with
    | inl v => simp only [meld,Equiv.symm_apply_apply,Sum.elim_inl,Census.fire,image_singleton]; exact ⟨singleton_nonempty _,(hp _).tails _⟩
    | inr j =>
      simp only [meld,Equiv.symm_apply_apply,Sum.elim_inr]; exact ⟨card_pos.mp (Nat.lt_of_lt_of_le (by omega) (hg.ranks i j)),hg.holds i j⟩
  refine ⟨fun i => ?_,fun i j hj => ?_,fun i => ?_,fun i j => (he i j).1,
    fun i j h s ht => ((he i j).2.carries h) (mem_image_of_mem _ ht),fun i j => (he i j).2.uses,
    fun i j => (he i j).2.allowed,fun i j => (he i j).2.borel,fun i j => (he i j).2.sym⟩
  · obtain ⟨⟨i,j⟩|i,rfl⟩ := (enr V).surjective i
    · rw [faces_left]; exact singleton_nonempty _
    rw [faces_right]; exact card_pos.mp (Nat.lt_of_lt_of_le (by omega) (hg.loaded i))
  · obtain ⟨⟨v,x⟩|x,rfl⟩ := (enr V).surjective i
    · simp only [meld,Census.fire,Equiv.symm_apply_apply,Sum.elim_inl,mem_singleton] at *; rw [hj]; exact (hp _).supports _
    rw [faces_right] at hj; simp only [meld,Equiv.symm_apply_apply,Sum.elim_inr]
    exact hg.roots x (mem_image_of_mem _ hj)
  obtain ⟨⟨v,x⟩|x,rfl⟩ := (enr V).surjective i
  · simp only [meld,Equiv.symm_apply_apply,Sum.elim_inl]; exact (hp _).color _
  simp only [meld,Equiv.symm_apply_apply,Sum.elim_inr]; exact hg.forms x

lemma purse_sum {X Y : Type*} {f : X ⊕ Y → ℝ} (hf : SumBudget (f ∘ Sum.inl) u) (hg : SumBudget (f ∘ Sum.inr) v) : SumBudget f (u+v) :=
  ⟨fun i => by cases i; exact hf.1 _; exact hg.1 _,Summable.sum f hf.2.1 hg.2.1,
    (Summable.tsum_sum hf.2.1 hg.2.1).trans_le (add_le_add hf.2.2 hg.2.2)⟩



def each (V : Type) [Fintype V] : (ℕ×V ⊕ ℕ×ℕ) ≃ ℕ×ℕ := (Equiv.prodSumDistrib ..).symm.trans (Equiv.prodCongr (Equiv.refl _) (enf V))
omit [DecidableEq V] in
lemma each_inl (i : ℕ) (j : V) : each V (Sum.inl (i,j))=(i,enf V (Sum.inl j)) := rfl
omit [DecidableEq V] in
lemma each_inr (x : ℕ×ℕ) : each V (Sum.inr x)=(x.1,enf V (Sum.inr x.2)) := rfl


end Crest
end YM.WardBin
