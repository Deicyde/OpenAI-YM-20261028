import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Position
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Connectors
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix


/-! # Covers and displacements for *all* full addresses, even the non-occurring / unreachable

In particular leaves the rates of `hire` unchanged even on a chain
crossing the whole period because it doesn't assume that a port has
already excluded too-long jumps. Can of course cut such entries by
*proving* finite range; here just use native exponential rate at cost
O(1/B) per unit length to connect the complete dependency sets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.LocalGaussian Further.GaussianScalar YM.Primitives.GCC
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {I J : Type} {c f : Side} {G : Gauge} {S : StepData c f} {A : Stores S} {F : Forest S.ratio} {B m k : ℕ} {x : ℝ} {v : Charges}

abbrev From (I : Type) (p : I→ Site c) (r : ℕ) (i : I) := halo r {p i}

def sectionMap (p : I → Site c) (r : ℕ) : (k : ℕ) → I → (Fin k → I) → I → Support c
  | 0,i,_,j => From I p r i ∪ From I p r j
  | k+1,i,h,j => From I p r i ∪ sectionMap p r k (h 0) (Fin.tail h) j
lemma contains (p : I → Site c) (r n : ℕ) (x : Site c) (i : I) (h : Fin n→I) (j : I) :
    x∈sectionMap p r n i h j ↔ x∈From I p r i ∨ x∈From I p r j ∨ ∃ v,x∈From I p r (h v) := by
  induction n generalizing i with
  | zero => simp [sectionMap]
  | succ n ih =>
    rw [sectionMap,Finset.mem_union,ih,Fin.exists_fin_succ]; simp only [Fin.tail, or_left_comm]
lemma centered (p : I → Site c) (r n : ℕ) (i : I) (h : Fin n→I) (j : I) : p i ∈ sectionMap p r n i h j := by
  rw [contains]; exact Or.inl (halo_subset r _ (Finset.mem_singleton_self _))
lemma spread_exact (S : StepData c f) (r n : ℕ) (i : Bond f) (h : Tracks (Bond f) n) (j : Bond f) :
    sectionMap (home S) r (n+1) i h j=spread S r (.inr ⟨n,(i,j),h⟩) := by ext; rw [contains,belongs]; simp [clues,halo_spec]
lemma spread_first (S : StepData c f) (r : ℕ) (i : Bond f) : spread S r (.inl i)=halo r {home S i} := by ext; rw [belongs,halo_spec]; simp [clues]

def length (p : I → Site c) : (n : ℕ) → I → (Fin n→I) → I → ℕ
  | 0,i,_,j => separation (p i) (p j)
  | n+1,i,h,j => separation (p i) (p (h 0)) + length p n (h 0) (Fin.tail h) j

def steps (u : Full I) : ℕ := u.elim (fun _=>0) (fun u=>u.1+2)
def traveled (p : I→Site c) (u : Full I) : ℕ := u.elim (fun _ => 0) (fun ⟨n,⟨i,j⟩,h⟩ => length p (n+1) i h j)
def plan (p : I→Site c) (r : ℕ) (u : Full I) : ℕ := (steps u+1) * (1+r+traveled p u)


def tilePrice (m : ℕ) := (m+m+1)^4 + 2

lemma tariff_sum (p : I → Site c) (B m : ℕ) (hB : 0<B) (n : ℕ) (i : I) (h : Fin n→I) (j : I) :
    (coverNumber B (sectionMap p (m*B) n i h j):ℝ) ≤ (n+2:ℝ)*tilePrice m + (length p n i h j:ℝ)/(B+1) := by
  have hT i := show (coverNumber B (From I p (m*B) i):ℝ) + 2 ≤ tilePrice m by
    exact_mod_cast Nat.add_le_add_right (Corona.tile (p i) m B hB) 2
  have hi i := halo_subset (m*B) _ (Finset.mem_singleton_self (p i))
  have hh u : (Connector.toll B u:ℝ) ≤ u/(B+1)+2 := (Connector.ratio B u).trans
    (add_le_add_right (show (if u=0 then (0:ℝ) else 2) ≤ 2 by split_ifs <;> norm_num) _)
  induction n generalizing i with
  | zero =>
    have he := Nat.cast_le (α:=ℝ).mpr (Connector.added (hi i) (hi j) B)
    push_cast at *; unfold sectionMap length; linarith [hh (separation (p i) (p j)),hT i,hT j]
  | succ n ih =>
    have he := Nat.cast_le (α:=ℝ).mpr (Connector.added (hi i) (centered p (m*B) n (h 0) (Fin.tail h) j) B)
    rw [sectionMap,length]; push_cast at *; rw [add_div]
    linarith only [he,hh (separation (p i) (p (h 0))),ih (h 0) (Fin.tail h),hT i]




def award (v : Charges) (G : Gauge) (p : I→Site c) (x : ℝ) (u : Full I) :=
  u.elim (fun _ => v.ink G * v.coin x) (fun ⟨m,⟨i,j⟩,h⟩ => v.ink G^(m+2)*v.coin x^(m+1)* rate (-v.toll) (length p (m+1) i h j))
lemma award_nn (v : Charges) (G : Gauge) (p : I→Site c) (x : ℝ) (u : Full I) : 0 ≤ award v G p x u := by
  unfold award; have h₁:= v.ink_pos G; have h₂:=v.coin_pos x
  rcases u with i|⟨n,⟨i,j⟩,h⟩
  · exact mul_nonneg h₁.le h₂.le
  exact mul_nonneg (by positivity) (rate_pos ..).le
lemma reprint (v : Charges) (G : Gauge) (L : J→I) (p : I → Site c) (x : ℝ) (u : Full J) :
    award v G p x (rename L u)=award v G (p ∘ L) x u := by
  rcases u with i|⟨m,⟨i,j⟩,h⟩
  · rfl
  have he (k : ℕ) (i : J) (h : Fin k → J) : length (p ∘ L) k i h j = length p k (L i) (L ∘ h) (L j) := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih => exact congr_arg₂ Nat.add rfl (ih (h 0) (Fin.tail h))
  exact congr_arg _ (congr_arg _ (he (m+1) i h).symm)
lemma priced_walk (v : Charges) (G : Gauge) (n : ℕ) (i : Active A x F) (h : Fin n→Active A x F) (j : Active A x F) :
    v.walkRate x A F G n i h j = v.ink G ^ (n+1) * v.coin x ^ n * rate (-v.toll) (length site n i h j) := by
  induction n generalizing i with
  | zero => simp only [Nat.zero_add,length,pow_one,pow_zero,mul_one]; rfl
  | succ n ih =>
    unfold Charges.walkRate Trail.tread
    rw [show Trail.tread .. = _ from ih (h 0) (Fin.tail h),length,pow_succ (v.ink G),pow_succ (v.coin x)]
    simp only [Charges.tap,Charges.hop,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul,rate,Nat.cast_add,mul_add,Real.exp_add]
    ring
lemma award_pay (u : Full (Active A x F)) : v.pay x A F G u=award v G site x u := by
  rcases u with i|⟨m,⟨i,j⟩,h⟩
  · rfl
  exact priced_walk ..
end YM.PhysicalNext.JointLoad.Folio
