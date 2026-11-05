import YM.Push.LOOP_COEFFICIENT.Pullback
import YM.Push.LOOP_COEFFICIENT.Vector
import YM.Push.LOOP_COEFFICIENT.Vertex
import YM.Work.B04

/-!
# Vertex words and interpreting them on a real-position analytic germ
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Lattice Laurent RG Wilson Bloch Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {a b c d J E F H : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype J] [Fintype E] [Fintype F] [Fintype H] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [DecidableEq J] [DecidableEq E] [DecidableEq F] [DecidableEq H]
  {n : Side} {A : Grid n J d} {B : Grid n E a} {D : Grid n F b} {S : Grid n H c}

namespace Vertex
def id : Vertex d a a := const fun _ => 1

def pow (X : Vertex d a a) (k : ℕ) : Vertex d a a := match k with
  | 0 => Vertex.id
  | n+1 => (X.pow n).mul X

def upper (X : Vertex d a a) (k : ℕ) : Vertex d a a := match k with
  | 0 => Vertex.const 0
  | n+1 => (X.upper n).add (X.pow (n+1))
def roll (X : Vertex d a a) := Vertex.id.add (X.upper depth)
def excess (X : Vertex d a a) := let H := X.upper depth; H.add (H.add (H.mul H))
end Vertex

/-- Actual matrix smoothness near flat AND literal routed-jet representation.
Not a bounds condition and not on stationary scalar Taylor coefficients. -/
structure Models (A : Grid n J d) (B : Grid n E a) (D : Grid n F b) (X : (J → ℝ) → Matrix E F ℝ) (V : Vertex d a b) : Prop where
  smooth : ContDiffAt ℝ ω X 0
  sync : Synced A B D (actualMatrix X) V
namespace Models
variable {X X' : (J → ℝ) → Matrix E F ℝ} {U U' : Vertex d a b}

omit [Fintype b] [DecidableEq E] [DecidableEq F] in
lemma const {M : Matrix E F ℝ} {V : Momentum → Matrix a b ℂ} (h : ∀ i k, Matches k i → Routed B D i i (cmat M) (V k)) : Models A B D (fun _ => M) (Vertex.const V) := ⟨contDiffAt_const,by rw [actualMatrix,actual_const]; exact Synced.const h⟩
omit [Fintype b] [DecidableEq E] [DecidableEq F] in
lemma zero : Models A B D (fun _ => 0) (Vertex.const 0) := Models.const fun _ _ _ => by rw [cmat.map_zero]; exact Routed.zero
lemma identity : Models A B B (fun _ => 1) Vertex.id := Models.const fun _ _ _ => by rw [cmat_one]; exact Routed.one
omit [Fintype b] [DecidableEq E] [DecidableEq F] in
lemma add (h : Models A B D X U) (h' : Models A B D X' U') : Models A B D (fun z => X z+X' z) (U.add U') := ⟨h.smooth.add h'.smooth,by change Synced _ _ _ (actual cmat (X+X')) _; rw [actual_add cmat h.smooth h'.smooth]; exact h.sync.add h'.sync⟩
omit [Fintype b] [DecidableEq E] [DecidableEq F] in
lemma smul (h : Models A B D X U) (r : ℝ) : Models A B D (fun z => r • X z) (U.smul (r:ℂ)) := ⟨h.smooth.const_smul _,by convert! (actual_push cmat cmat (r • ContinuousLinearMap.id ℝ (Matrix E F ℝ)) (LinearMap.lsmul ℂ _ (r:ℂ)) h.smooth (by intro x; ext i j; change Complex.ofReal (r*x i j)=_; exact ofReal_mul ..)).symm ▸ h.sync.smul (r:ℂ)⟩
omit [Fintype c] [DecidableEq E] [DecidableEq F] [DecidableEq H] in
lemma mul {Y V} (h : Models A B D X U) (h' : Models A D S Y V) : Models A B S (fun z => X z*Y z) (U.mul V) := ⟨smooth_mul h.smooth h'.smooth,by rw [actualMatrix_mul h.smooth h'.smooth]; exact h.sync.mul h'.sync⟩
omit [DecidableEq E] in
lemma transpose (h : Models A B D X U) : Models A D B (fun z => (X z).transpose) U.transpose := by
  let L := (Matrix.transposeLinearEquiv E F ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨smooth_transpose h.smooth,?_⟩; change Synced _ _ _ (actual cmat (L ∘ X)) _; erw [actual_push cmat cmat L (Matrix.transposeLinearEquiv E F ℂ ℂ).toLinearMap h.smooth (fun _ => rfl)]; exact h.sync.transpose
lemma inv {X U} (h : Models A B B X U) (hU : ∀ k i, Matches (n:=n) k i → IsUnit (U.base k)) : Models A B B (fun z => (X z)⁻¹) U.inv := by
  have he : IsUnit (X 0) := by
    have hv := Routed.isUnit (fun i => h.sync.base (mon_matches i)) (fun i => hU _ i (mon_matches i))
    change IsUnit (Complex.ofRealHom.mapMatrix (X 0)) at hv
    rw [isUnit_iff_isUnit_det,← RingHom.map_det, isUnit_iff_ne_zero] at hv
    exact (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (fun he => hv (by rw [he,map_zero])))
  exact ⟨(inv_contDiffAt _ ((isUnit_iff_isUnit_det _).mp he)).comp 0 h.smooth,by rw [actualMatrix_inv h.smooth he]; exact h.sync.inv (cmat_unit he) hU⟩
lemma pow {X U} (h : Models A B B X U) (k : ℕ) : Models A B B (fun z => X z ^ k) (U.pow k) := by induction k with
                                                                                               | zero => simpa only [pow_zero] using! identity
                                                                                               | succ k ih => simpa only [pow_succ] using! ih.mul h

def higher (k : ℕ) (M : Matrix E E ℝ) : Matrix E E ℝ := match k with | 0 => 0 | n+1 => higher n M + M^(n+1)
lemma higher_tail (k : ℕ) (M : Matrix E E ℝ) : 1+higher k M = tail M k := by induction k with
  | zero => simp [tail,higher]
  | succ k ih => rw [higher, ← add_assoc, ih,tail,tail,Finset.sum_range_succ (n:=k+1)]
lemma upper {X U} (h : Models A B B X U) (k : ℕ) : Models A B B (fun z => higher k (X z)) (U.upper k) := by induction k with
                                                                                                       | zero => exact Models.zero
                                                                                                       | succ k ih => exact ih.add (h.pow _)
lemma roll {X U} (h : Models A B B X U) : Models A B B (fun z => tail (X z) depth) U.roll := by simp_rw [← higher_tail]; exact identity.add (h.upper _)
lemma excess {X U} (h : Models A B B X U) : Models A B B (fun z => (tail (X z) depth)^2 - 1) U.excess := by
  let he := h.upper depth
  convert! (he.add (he.add (he.mul he))) using 1; funext z; rw [← higher_tail]; noncomm_ring
end Models
end YM.Push.Loops
