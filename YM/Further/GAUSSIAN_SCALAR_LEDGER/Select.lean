import YM.Further.GAUSSIAN_SCALAR_LEDGER.Hitting
import YM.Next.FREE_KERNELS.Amend


set_option warningAsError false

/-!
# Matrix-only locality of the per-address values

Both nonzero tests & to evaluate from submatrix windows. Supports below
whole unions of B-halos **including all route positions**. NOT
post-Wilson support! Entries inside these balls (and lens positions and
presence of indices themselves) must in turn be localized when reading
seeds or U, etc. May increase each halo by a fixed B multiple if have
receipts for that. No paths or stencil bounds inferred back from a
zero actual matrix value. `Sparse` assumed globally on both systems.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar.Trail
open Matrix Function Filter MeasureTheory Precision SectorNext.Vacuum Lattice
open RawPrice (tear field)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Side} (l : ι → Site n) (L : Lens ι) (B : ℕ)

-- assume numerical range in these units (close can use fitted patches)
def Sparse (A : Wall ι) := ∀ i j, ¬ separation (l i) (l j) ≤ B → A i j=0
def Housed := ∀ i j, j∈L.eye i → separation (l i) (l j) ≤ B

def TrailOK : ∀ k : ℕ, ι → (Fin k → ι) → ι → Prop
  | 0,i,_,j => separation (l i) (l j) ≤ B
  | k+1,i,f,j => separation (l i) (l (f 0)) ≤ B ∧ TrailOK k (f 0) (Fin.tail f) j

def ground : ∀ k : ℕ, ι → (Fin k → ι) → ι → Support n
  | 0,i,_,j => halo B {l i} ∪ halo B {l j}
  | k+1,i,f,j => halo B {l i} ∪ ground k (f 0) (Fin.tail f) j

omit [Fintype ι] [DecidableEq ι] in
lemma checkpoint (k : ℕ) (i : ι) (f : Fin k → ι) (j : ι) : halo B {l i} ⊆ ground l B k i f j := by
  cases k <;> exact Finset.subset_union_left

-- choose ref distance 2r. `M` >= 5 then envelopes actually retain
-- a unit-r pair extension around numerical matrices; V-row field costs extra.
def airport (M : ℕ) (k : ℕ) (i : ι) (f : Fin k → ι) (j : ι) : Support n :=
    if TrailOK l (B+B) k i f j then ground l (M*B) k i f j else ∅

omit [Fintype ι] [DecidableEq ι] in
lemma hop_range (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (i : ι) (f : Fin k → ι) (j : ι)
    (hv : TrailOK l (B+B) k i f j) (x : Site n) (hh : x∈ ground l (M*B) k i f j) :
    separation x (l i) ≤ (k+2)*(M*B) := by
  have hp : B+B ≤ M*B := by simpa [two_mul] using Nat.mul_le_mul_right B hM
  have he (i : ι) (hh : x∈halo (M*B) {l i}) : separation x (l i) ≤ M*B := by
    rw [separation_comm]; simpa [halo_spec] using hh
  induction k generalizing i with
  | zero =>
    change separation (l i) (l j) ≤ _ at hv
    rcases Finset.mem_union.mp hh with hx | hx
    · have hy := he i hx; omega
    have hy := he j hx; have hk := separation_triangle x (l j) (l i)
    rw [separation_comm (l i) (l j)] at hv; omega
  | succ k ih =>
    change separation (l i) (l (f 0)) ≤ _ ∧ _ at hv
    rw [show (k+1+2)*(M*B)=(k+2)*(M*B)+M*B by ring]
    rcases Finset.mem_union.mp hh with hx | hx
    · have hy := he i hx; omega
    have hy := ih (f 0) (Fin.tail f) hv.2 hx
    have hk := separation_triangle x (l (f 0)) (l i)
    rw [separation_comm (l i) (l (f 0))] at hv; omega

omit [Fintype ι] [DecidableEq ι] in
lemma hop_budget (M : ℕ) (hM : 2 ≤ M) (hB : 0 < B) (k : ℕ) (i : ι) (f : Fin k → ι) (j : ι)
    (hv : TrailOK l (B+B) k i f j) : coverNumber B (ground l (M*B) k i f j) ≤ (k+2)*(M+M+1)^4 := by
  have hp : B+B ≤ M*B := by simpa [two_mul] using Nat.mul_le_mul_right B hM
  have hx (s t : ι) (hs : separation (l s) (l t) ≤ B+B) : l t ∈ halo (M*B) {l s} :=
    halo_spec.mpr ⟨_, Finset.mem_singleton_self _,hs.trans hp⟩
  have he (s : ι) : l s ∈ halo (M*B) {l s} := hx s s (by simp)
  induction k generalizing i with
  | zero =>
    unfold ground
    apply (Corona.meets_sum (hx _ _ hv) (he j) B).trans
    exact (Nat.add_le_add (Corona.tile (l i) M B hB) (Corona.tile (l j) M B hB)).trans_eq (by ring)
  | succ k ih =>
    unfold TrailOK at hv
    unfold ground
    apply (Corona.meets_sum (hx _ _ hv.1) (checkpoint l _ _ _ _ _ (he (f 0))) _).trans
    exact (Nat.add_le_add (Corona.tile (l i) M B hB) (ih (f 0) (Fin.tail f) hv.2)).trans_eq (by ring)

omit [Fintype ι] [DecidableEq ι] in
lemma funded_steps (M : ℕ) (hM : 2≤M) (hB : 0 < B) :
    Filed (χ:=fun k => Fin (k+1) → ι) B (2*(M*B)) (2*(M+M+1)^4) l
      (fun k i f => airport l B M (k+1) i f i) ∧
    Filed (χ:=fun k => Fin k → ι) B (M*B) ((M+M+1)^4) l
      (fun k i f => airport l B M k i f i) ∧
    Filed (χ:=fun k => ι×(Fin (k+1) → ι)) B (2*(M*B)) (2*(M+M+1)^4) l
      (fun k i p => airport l B M (k+1) i p.2 p.1) := by
  have hl (k : ℕ) (i j : ι) (f : Fin k→ι) (x : Site n) (h : x∈airport l B M k i f j) :
      separation x (l i) ≤ (k+2)*(M*B) ∧ coverNumber B (airport l B M k i f j) ≤ (k+2)*(M+M+1)^4 := by
    by_cases he : TrailOK l (B+B) k i f j; swap; simp [airport,he] at h
    unfold airport at *; rw [if_pos he] at h ⊢
    exact ⟨hop_range l B M hM k i f j he x h, hop_budget l B M hM hB k i f j he⟩
  have hx (k : ℕ) (y : ℕ) : (k+1+2)*y ≤ (k+2)*(2*y) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨fun k i f x h => ?_,fun k i f x h => hl _ _ _ _ _ h, fun k i p x h => ?_⟩
  all_goals
    obtain ⟨hv,hw⟩ := hl _ _ _ _ _ h
    exact ⟨hv.trans (hx ..),hw.trans (hx ..)⟩

namespace Diff
omit [Fintype ι] [DecidableEq ι] in
lemma widen {W : Wall ι} (h : Sparse l B W) : Sparse l (B+B) W := fun i j hv =>
  h i j fun ht => hv (by omega)

omit [DecidableEq ι] in
lemma times {r s : ℕ} (X Y : Wall ι) (h : Sparse l r X) (hv : Sparse l s Y) : Sparse l (r+s) (X*Y) := by
  intro i j he
  rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hx : separation (l i) (l k) ≤ r
  · rw [hv k j (by have hd := separation_triangle (l i) (l k) (l j); omega),mul_zero]
  rw [h i k hx,zero_mul]

omit [Fintype ι] in
lemma view (X : Wall ι) (h : Housed l L B) (u : ℝ) : Sparse l B (L.visit X u) := by
  intro i j he; unfold Lens.visit; rw [Matrix.of_apply,dif_neg ?_]
  intro hx; rw [separation_comm] at he; exact he (h j i hx)



omit [Fintype ι] [DecidableEq ι] in
private lemma far {W Y : Wall ι} (h : Sparse l (B+B) W) (hv : Sparse l (B+B) Y)
    (k : ℕ) (i : ι) (f : Fin k→ι) (j : ι) (he : ¬ TrailOK l (B+B) k i f j) : tread W Y k i f j=0 := by
  induction k generalizing i with
  | zero => exact hv i j he
  | succ k ih =>
    unfold tread
    by_cases hx : separation (l i) (l (f 0)) ≤ B+B
    · rw [ih (f 0) (Fin.tail f) (fun hr => he ⟨hx,hr⟩),mul_zero]
    rw [h _ _ hx,zero_mul]



-- MATRIX lookup only. Same Lens choices.
def Heard (X : Support n) (A V : Wall ι) := ∀ i, l i∈X → ∀ j, A i j=V i j

section dependence
variable {A V : Wall ι} {X : Support n} (hA : Sparse l B A) (hV : Sparse l B V) (ht : Heard l X A V)
    (hL : Housed l L B)
include ht hL
omit [Fintype ι] [DecidableEq ι] in
lemma glasses (j : ι) (hh : halo B {l j} ⊆ X) : L.glass A j = L.glass V j := by
  ext i k; apply ht _ _ k
  exact hh (halo_spec.mpr ⟨l j,Finset.mem_singleton_self _,hL j _ i.property⟩)

omit [Fintype ι] in
lemma same_columns (j : ι) (hh : halo B {l j} ⊆ X) (i : ι) (u : ℝ) :
    L.visit A u i j = L.visit V u i j := by
  unfold Lens.visit; rw [Matrix.of_apply,Matrix.of_apply]; split; rw [glasses l L B ht hL j hh]; rfl

include hA hV

end dependence

omit [Fintype ι] [DecidableEq ι] in
private lemma thread (k M : ℕ) (i j : ι) (f : Fin k → ι) (X Y Z W : Wall ι)
    (h : ∀ i', halo M {l i'}⊆ground l M k i f j → ∀ j', X i' j'=Y i' j' ∧ Z i' j'=W i' j') :
    tread X Z k i f j=tread Y W k i f j := by
  induction k generalizing i with
  | zero => exact (h i (checkpoint l M _ i f _) _).2
  | succ k ih =>
    unfold tread; rw [(h i (checkpoint l M _ i f _) _).1, ih (f 0) (Fin.tail f)]
    intro x hx; exact h x (Finset.Subset.trans hx Finset.subset_union_right)






end Diff
end YM.Further.GaussianScalar.Trail
