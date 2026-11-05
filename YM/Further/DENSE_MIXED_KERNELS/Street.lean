import YM.Further.DENSE_MIXED_KERNELS.ColorCosts
import YM.Further.DENSE_MIXED_KERNELS.Packet
import YM.Further.DENSE_MIXED_KERNELS.Word

/-!
# Producer inputs at the alphabet/component level

What needs to be prepared *by* a reindexing of the step (not asserting
this is possible for the committed vacuum or works for independent
step-scalar choices). Letter surveys, SPELLINGS, identities at
actual entries, with NO budgets on component evaluation supplied.
Prices bought separately after arithmetic uses. Coding is permissive:
if more labels with algebraic zero are to be used, keep them all included
wherever they are to be evaluated; `omits` is just for blank padding.
Discarding without checking even well-definedness, or forgetting to
pay for tags/eligibility queries, is NOT justified by these statements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Lattice RG Wilson Source Labels Marker Overlay Extra.Multi Extra.Multi.Merger Extra.Multi.System
open Port Gaussian Surface Precision Tree Pressure 
open Push.AbsoluteSums
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

-- Keep one forest data source. Can also take a single fixed F. With mixtures,
-- account separately for every selected F at any used entry. No result here
-- on choice locality needed for reindexing/reconstruction.
variable {G : Gauge} {m n : Side} {S : StepData m n} (I : Type) [Fintype I]
structure Vault (I : Type) [Fintype I] (S : StepData m n) where
  tree : I → Forest S.ratio
  portion : I → ℝ
  pos : ∀ i, 0≤portion i
  one : ∑ i,portion i=1

omit [Fintype I] in
lemma Pitch.swept {j : ℕ} (T : Finset I) {f : I → Config G n → ℂ} {U : Config G n} {P : Directions G n → Prop} {b : I → ℝ}
    (h : ∀ i∈T, Pitch (f i) U P j (b i) 1) : Pitch (fun x => ∑ i∈T,f i x) U P j (∑ i∈T,b i) 1 := by
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,norm_zero] using! Pitch.fixed (U:=U) (P:=P) (0:ℂ) zero_le_one
  | insert i T hi ih =>
    simpa only [Finset.sum_insert hi] using (h i (by simp)).plus (ih (fun _ hk => h _ (Finset.mem_insert_of_mem hk)))

variable {I}
def Vault.pour (D : Vault I S) (f : I → Config G m → ℂ) (x) := ∑ i,D.portion i • f i x

theorem Vault.pitch (D : Vault I S) {g : I → Config G m → ℂ} {U : Config G m} {P : Directions G m→Prop} {k : ℕ} {c : ℝ}
    (h : ∀ i,Pitch (g i) U P k c 1) : Pitch (D.pour g) U P k c 1 := by
  let L i : ℂ →L[ℝ] ℂ := D.portion i • ContinuousLinearMap.id ℝ _
  have H i (x : ℂ) : ‖L i x‖ ≤ D.portion i * ‖x‖ := (norm_smul_of_nonneg (D.pos i) x).le
  have hp := Pitch.swept I Finset.univ (fun i (_:i∈Finset.univ) => (h i).linear (L i) (H i) (D.pos i))
  simpa only [←Finset.sum_mul,D.one,one_mul] using! hp

lemma Vault.norm_le (D : Vault I S) (f : I→Config G m → ℂ) (x) (B : ℝ) (h : ∀ i, ‖f i x‖ ≤ B) :
    ‖D.pour f x‖ ≤ B := by
  unfold pour; apply (norm_sum_le ..).trans
  simp_rw [norm_smul_of_nonneg (D.pos _)]
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (D.pos i)) ?_
  rw [← Finset.sum_mul,D.one,one_mul]

section Structure
variable {V : Type} [DecidableEq V] {R : Census V} {P : Rep G n} {L : Bands R P}

/-- Common prices on one step, tag identities shared with the whole
Marker system. Vacuum sponsors include Stores BOOKKEEPING with charged halo.
Receipts concern ALL true entries; not just sales with nonzero value at U. -/
structure Bazaar (L : Bands R P) (S : StepData m n) (E F : Layer G V m) where
  owner : E.Id → Pieces
  color : E.Id → ℝ
  nonneg i : 0 ≤ color i
  plain : EmptyBook S F.Id

namespace Bazaar
variable {E F : Layer G V m} (Z : Bazaar L S E F)

def scale (M B : ℕ) : E.Id ⊕ F.Id → ℕ := Sum.elim (fun i => coverNumber M (blocks L (Z.owner i))) (Z.plain.depth F.supp B)
def down : E.Id⊕F.Id→ℝ := Sum.elim Z.color Z.plain.down
def cash : E.Id⊕F.Id→ℝ := Sum.elim Z.color Z.plain.rate
def flags : E.Id⊕F.Id → Support m := Sum.elim (fun _ => ∅) (fun i => (Z.plain.pack i).elim ∅ (fun s=>s.flags))

theorem greater (h : L.Active) (M B) (i) : 0< Z.scale M B i := by
  rcases i with i|i
  · exact lives L h M _
  exact le_max_left 1 _
theorem down_le (i) : Z.down i ≤ Z.cash i := by rcases i with i|i; exact le_rfl; exact EmptyBook.down_le ..
lemma pays (i) : 0 ≤ Z.down i := by rcases i with i|i; exact Z.nonneg _; exact EmptyBook.down_pos ..

variable {B l : ℕ}
lemma required {x : Chain (E.Id⊕F.Id)} (hr : (collect Z.flags (catalog x)).Nonempty) :
    ∃ i y s,x.2 i = Sum.inr y ∧ Z.plain.pack y = some s ∧ s.flags.Nonempty := by
  obtain ⟨a,ha⟩ := hr; unfold Merger.collect at ha; simp only [Finset.mem_biUnion,Multiset.mem_toFinset,catalog,Extra.Multi.Numbered.bag,Multiset.mem_map] at ha
  obtain ⟨b,⟨i,_,hh⟩,hi⟩ := ha
  rcases b with b|b
  · simp [flags] at hi
  unfold flags at hi; dsimp only [Sum.elim_inr] at hi; generalize hs : Z.plain.pack b=s at hi
  cases s <;> simp only [Option.elim_none,Option.elim_some,Finset.notMem_empty] at hi
  exact ⟨i,b,_,hh,hs,a,hi⟩

lemma discount {x : Chain (E.Id⊕F.Id)} {γ : ℝ} (hq : (collect Z.flags (catalog x)).Nonempty)
    (hl : Real.exp (-Z.plain.ep) ≤ γ) : ∏ i,Z.down (x.2 i) ≤ γ * ∏ i,Z.cash (x.2 i) := by
  obtain ⟨i,b,s,hb,hs,h⟩ := Z.required hq
  have hp : 0 < s.shares := lt_of_lt_of_le (Finset.card_pos.mpr h) (by unfold Stores.shares; omega)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),← Finset.mul_prod_erase Finset.univ
    (fun i => Z.cash (x.2 i)) (Finset.mem_univ i),hb, ← mul_assoc]
  exact mul_le_mul (Z.plain.shield hs hp hl) (Finset.prod_le_prod (fun _ _ => Z.pays _) (fun i _ => Z.down_le _))
    (Finset.prod_nonneg (fun i _ => Z.pays _)) (mul_nonneg ((Real.exp_pos _).le.trans hl) (Z.plain.paid _))
end Bazaar

/-- Structural requirements for component price. Doesn't assert that spelling
supplies enough of other data e.g. for log/canonical comparisons; Scheme
already tests its own compatibility. -/
structure Keys (A B : Layer G V m) where
  used : Set B.Id
  visit : used → Chain A.Id
  separate : Injective (fun i:used => catalog (visit i))
  omits : ∀ i∉ used,B.value i=0
  conect (i : used) : mesh A.supp (catalog (visit i))
  supp i : B.supp i.val=collect A.supp (catalog (visit i))
  names i : B.names i.val=collect A.names (catalog (visit i))
  one i : ((catalog (visit i)).toFinset : Set A.Id).PairwiseDisjoint A.names
  again i : ∀ j,2 ≤ (catalog (visit i)).count j → A.names j=∅

variable {A B : Layer G V m} (X : Keys A B)

def Keys.cost (f : A.Id → ℝ) (i : B.Id) := if h : i∈X.used then Merger.paid f (catalog (X.visit ⟨i,h⟩)) else 0

omit [DecidableEq V] in
lemma Keys.prices {f : A.Id→ℝ} (h : ∀ i,0≤f i) (i : B.Id) : 0 ≤ X.cost f i := by
    unfold Keys.cost; split
    next h => exact Merger.paid_nonneg (by assumption) _
    exact le_rfl

omit [DecidableEq V] in
lemma Keys.display {f : A.Id→ℝ} : Merger.Display A.names A.supp B.names B.supp f (X.cost f) 1 := by
  let m (i : B.Id) := if h : i∈X.used then catalog (X.visit ⟨i,h⟩) else 0
  have ht i (hi : 0<X.cost f i) : i∈X.used := by by_contra hh; simp [Keys.cost,hh] at hi
  refine ⟨m, fun i hi j hj hp => ?_, fun i hi => ?_⟩
  · dsimp only [m] at hp; rw [dif_pos (ht i hi),dif_pos (ht j hj)] at hp
    exact congr_arg (fun a : X.used=> a.val) (X.separate hp)
  let w : X.used := ⟨i,ht i hi⟩
  unfold m; rw [dif_pos w.property]
  exact ⟨X.conect w,(Finset.Subset.refl _ : (B.supp i) ⊆ _ ) |>.trans (by rw [show B.supp i = _ from X.supp w]),
    X.names w,X.one w,X.again w,by rw [Keys.cost,dif_pos w.property,one_mul]⟩
end Structure
end YM.Further.DenseMixedKernels
