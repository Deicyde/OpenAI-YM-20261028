import YM.Pressure.Seeds
import YM.SectorNext.RECONNECTED_LOCALITY.Pinned



set_option warningAsError false

/-!
# Another log IR for disjoint unforced gas 

Instead of numbering tuple graphs, proving tree sign cancellation etc, we give a different
convergent expansion of the unrestricted/restricted log, using trees DIRECTLY and over
an arbitrary countable alphabet. Trees are legal log-label *addresses*, including arbitrary
ordered repetitions of the same family member. They will reproduce the log by the differential
relation for the disjoint gas with a family-specific speed (scale member i by $t^{d_i}$,
$d_i$ its support charge), together with HasDerivAt results for unrestricted & all restricted
gases. Doesn't require analytic complex continuation. With the chosen speed a tree gets a
degree denominator (sum of its support charges not count of its nodes) essential to the
proof of convergence: a node anywhere in a child subtree can invoke a connection to its parent,
costing that parent's hit sum times the OCCURRENCE SIZE of the child; so instead of cancelling a
factor n for choosing a marked occurrence we cancel a factor ~D at its grandparent root.
Computing canonical low coefficients from this variant IR still needs authentic low/loop work;
use total pressure identity, don't assert these address coefficients are the numbered E $K$.
This file: tree algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
open Lattice
open Function

variable (ι : Type*)

/-- Rose address. -/
def Rose := WType (fun i : ι × ℕ => Fin i.2)

namespace Rose
variable {ι}

instance [Countable ι] : Countable (Rose ι) := by
  classical
  letI := Encodable.ofCountable (ι×ℕ)
  unfold Rose
  infer_instance

def root (i : ι) {n : ℕ} (x : Fin n → Rose ι) : Rose ι := .mk (β:=fun i : ι×ℕ => Fin i.2) (i,n) x -- param name

@[elab_as_elim] theorem inspect {Q : Rose ι → Prop} (h : ∀ (i : ι) (n : ℕ) (x : Fin n → Rose ι),
    (∀ j,Q (x j)) → Q (root i x)) (X : Rose ι) : Q X := by
  induction (show WType _ from X) with
  | mk a f ih => cases a; exact h _ _ f ih

/-- All children orders included. Division by factorial handled in the weight. -/
abbrev Row (ι : Type*) := Σ n : ℕ,Fin n → Rose ι

def trunk : Rose ι ≃ ι × Row ι where
  toFun a := let b:=WType.toSigma (show WType (fun i : ι × ℕ => Fin i.2) from a);
    (b.1.1,⟨b.1.2,b.2⟩)
  invFun a := root a.1 a.2.2
  left_inv a := by unfold Rose at a; rcases a with ⟨⟨i,n⟩,j⟩; rfl
  right_inv a := by rcases a with ⟨i,n,j⟩; rfl

@[simp] theorem trunk_root (i : ι) {n : ℕ} (x : Fin n → Rose ι) : trunk (root i x)=(i,⟨n,x⟩) := rfl
@[simp] theorem root_trunk (i : ι × Row ι) : trunk.symm i=root i.1 i.2.2 := rfl

def fold {ω : Type*} (f : ι → (n : ℕ) → (Fin n → ω) → ω) (a : Rose ι) : ω :=
    WType.elim ω (fun h => f h.1.1 h.1.2 h.2) (show WType (fun i : ι × ℕ => Fin i.2) from a)

@[simp] theorem fold_node {ω : Type*} {f : ι → (n : ℕ) → (Fin n → ω) → ω} {n : ℕ} {i} (x : Fin n → Rose ι) :
    fold f (root i x)=f i _ (fun j => fold f (x j)) := by
  unfold fold root; rw [WType.elim]

variable {c : Side} (S : ι → Support c) (B : ℕ)

/-- Full locations before any correction merger. -/
def union : Rose ι → Support c := fold fun i _ f => S i ∪ Finset.univ.biUnion f
@[simp] lemma union_node {i : ι} {n : ℕ} (f : Fin n → Rose ι) : union S (root i f)=S i∪Finset.univ.biUnion (fun j => union S (f j)) := by
  rw [union,fold_node]

def fee : Rose ι → ℕ := fold fun i _ f => coverNumber B (S i) + ∑ j, f j
@[simp] lemma fee_node {i : ι} {n : ℕ} (f : Fin n → Rose ι) : fee S B (root i f)=coverNumber B (S i)+ ∑ j,fee S B (f j) := by
  rw [fee,fold_node]

def occurrences : Rose ι → ℕ := fold fun _ _ f => 1+∑ j,f j
@[simp] lemma number_node {i : ι} {n : ℕ} (f : Fin n → Rose ι) : occurrences (root i f)=1+ ∑ j,occurrences (f j) := by
  rw [occurrences,fold_node]

def depth (t : Rose ι) := WType.depth (β:=fun i : ι × ℕ => Fin i.2) t

lemma depth_pos (t : Rose ι) : 0 < depth t := WType.depth_pos _
lemma climbs (i : ι) {n : ℕ} (x : Fin n → Rose ι) (j) : depth (x j) < depth (root i x) := WType.depth_lt_depth_mk (β:=fun i : ι × ℕ => Fin i.2) (i,n) x j

lemma exist (p : Rose ι) : 0 < occurrences p := by
  obtain ⟨⟨i,n,j⟩,rfl⟩:=trunk.symm.surjective p; rw [root_trunk,number_node]; omega

lemma funds (h : ∀ i,(S i).Nonempty) (p : Rose ι) : occurrences p ≤ fee S B p := by
  induction p using Rose.inspect with
  | h i n x IH =>
    rw [number_node, fee_node]; exact Nat.add_le_add (Ledger.cover_pos (h i)) (Finset.sum_le_sum (fun i _ => IH i))



/-- Root connections: for each child require parent index i support meets **some**
part of the child (not requiring it to meet root of the child!). -/
def link (i : ι) (a : Rose ι) := ¬Disjoint (S i) (union S a)

/-- Active trees. Each child invokes connection OF ITS SUPPORT to the parent, the parents' positions
not shifted. Use all original overlap test positions of unforced u. -/
def operating : Rose ι → Prop := WType.rec (motive:=fun _ : WType (fun i : ι × ℕ => Fin i.2) => Prop)
  (fun a f children => ∀ j,link S a.1 (f j) ∧ children j)

@[simp] lemma active_node {i : ι} {n : ℕ} (f : Fin n → Rose ι) :
    operating S (root i f) = ∀ j,link S i (f j) ∧ operating S (f j) := rfl

private lemma wrap (p : Rose ι) (H : operating S p) :
    coverNumber B (union S p) ≤ fee S B p := by
  induction p using Rose.inspect with
  | h i n f IH =>
    have hh (s : Finset (Fin n)) : coverNumber B (S i ∪ s.biUnion (fun a => union S (f a))) ≤
        coverNumber B (S i) + ∑ a∈s,fee S B (f a) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.biUnion_insert,Finset.sum_insert hj]
        obtain ⟨a,ha,hx⟩ := Finset.not_disjoint_iff.mp (((active_node S f).mp H j).1)
        have he:= Corona.meets_sum (X:=S i∪s.biUnion (fun a => union S (f a))) hx (Finset.mem_union_left _ ha) B
        rw [Finset.union_left_comm]
        apply le_trans he
        have ht:=IH j (((active_node S f).mp H j).2)
        omega
    rw [fee_node,union_node]; exact hh _



private lemma volume (a : Rose ι) : (union S a).card ≤ (fee S B a)*Ledger.size B := by
  induction a using Rose.inspect with
  | h i n f IH =>
    rw [union_node,fee_node, Nat.add_mul,Finset.sum_mul]
    apply le_trans (Finset.card_union_le ..)
    exact Nat.add_le_add (Corona.pays ..) ((Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun i _ => IH i)))

theorem contained (a : Rose ι) : (union S a).card ≤ (fee S B a)*Ledger.size B := volume S B a

open scoped Classical
/-- Root grade d_i / D. At positive parameter radius will still have recurrence over trees.
θ=1 for positive estimate. θ=−1 for signed *pressure*, NOT negative log of density
until later storage in actions. `v` can already carry masks. -/
def word (θ : ℝ) (v : ι → ℝ) : Rose ι → ℝ := WType.rec
    (motive:=fun _ : WType (fun i : ι × ℕ => Fin i.2) => ℝ) (fun a children w =>
      ((coverNumber B (S a.1) : ℕ) : ℝ) / fee S B (root a.1 children) * v a.1 *
      (∏ j,(if link S a.1 (children j) then θ*w j else 0)) / (a.2.factorial:ℝ))

@[simp] lemma spell (θ : ℝ) (v : ι → ℝ) {i : ι} {n : ℕ} (f : Fin n → Rose ι) :
    word S B θ v (root i f)= ((coverNumber B (S i) : ℕ) : ℝ) / fee S B (root i f) * v i *
      (∏ j,(if link S i (f j) then θ*word S B θ v (f j) else 0)) / (n.factorial:ℝ) := by
  rfl

end Rose
end YM.SectorNext.Reconnect
