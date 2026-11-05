import YM.Extra.FREE_DETECTOR_ALGEBRA.Dialog

set_option warningAsError false

/-!
# Filtered section (rank/writing)

The range of `observable` is exactly bounded G-invariant polynomials in
Maxwell solution jet variables, also if tracking both gradings. The
unrestricted polynomial change-of-variables section is compatible with the
invariant restriction. `Ad` not any independent color copies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Set Filter Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace

section polys
open MvPolynomial
variable {α β M : Type*} [AddCommMonoid M]

lemma powersMove (a : α → M) (b : β → M) (F : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial β ℂ)
    (hf : ∀ i : α, IsWeightedHomogeneous b (F (X i)) (a i)) (p : α →₀ ℕ) (c : ℂ) :
    IsWeightedHomogeneous b (F (monomial p c)) (Finsupp.weight a p) := by
  classical
  rw [monomial_eq, Finsupp.weight_apply,_root_.map_mul, show F (C c)=C c from F.commutes c]
  unfold Finsupp.prod Finsupp.sum
  rw [_root_.map_prod]
  apply IsWeightedHomogeneous.C_mul
  apply IsWeightedHomogeneous.prod
  intro i _
  rw [_root_.map_pow]; exact (hf i).pow _

lemma gradeMove (a : α → M) (b : β → M) (F : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial β ℂ)
    (hf : ∀ i : α, IsWeightedHomogeneous b (F (X i)) (a i)) (p : MvPolynomial α ℂ) (m : M)
    (he : IsWeightedHomogeneous a p m) : IsWeightedHomogeneous b (F p) m := by
  classical
  rw [p.as_sum,_root_.map_sum]; apply IsWeightedHomogeneous.sum
  intro i hi; exact he (mem_support_iff.mp hi) ▸ powersMove a b F hf i (p.coeff i)

/-- Filter by ordinary/support weights (allows any requested small set
of multiple grades). -/
def byWeight (a : α → M) (s : Set M) : Submodule ℂ (MvPolynomial α ℂ) :=
    restrictSupport _ {b : α →₀ ℕ | Finsupp.weight a b ∈ s}

lemma filterMove (a : α → M) (b : β → M) (F : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial β ℂ)
    (hf : ∀ i : α, IsWeightedHomogeneous b (F (X i)) (a i)) {p : MvPolynomial α ℂ} {s : Set M} (hp : p∈byWeight a s) : F p∈byWeight b s := by
  classical
  rw [p.as_sum,_root_.map_sum]
  apply Submodule.sum_mem
  intro i hi
  refine (mem_restrictSupport_iff ℂ).mpr fun m hm => ?_
  change Finsupp.weight b m ∈ s
  rw [powersMove a b F hf i (p.coeff i) (mem_support_iff.mp hm)]
  exact (mem_restrictSupport_iff ℂ).mp hp hi
end polys

variable {G : Gauge} {j d : ℕ}

def emblem (G : Gauge) (j : ℕ) (P : Taylor G j→ₗ[ℝ] ℝ) : Labels.Pol G :=
    ∑ i, MvPolynomial.C ((↑(P (Labels.axes G j i))):ℂ) * MvPolynomial.X ⟨j,i⟩

theorem emblem_read (p : Jet G) (f : Taylor G j→ₗ[ℝ] ℝ) : Labels.read p (emblem G j f) = (f (p j) : ℂ) := by
  unfold emblem
  conv_rhs => rw [← (Labels.axes G j).sum_repr (p j)]
  simp only [Labels.read,_root_.map_sum,_root_.map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
    Algebra.algebraMap_self,RingHom.id_apply, map_smul, Complex.ofReal_sum,Labels.coord,smul_eq_mul, Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def reroute (X : Jet G) : TaylorTower G := fun i => sendTo G i (X i)

/-- Section of restriction. -/
def writeRaw : WickPol G →ₐ[ℂ] Labels.Pol G := MvPolynomial.aeval fun i =>
    emblem _ i.1 ((coordinateLeg i).comp (sendTo G i.1))

theorem writeRaw_read (J : Jet G) (x : WickPol G) : Labels.read J (writeRaw x) = probe (reroute J) x := by
  have he : (Labels.read J).comp writeRaw = probe (reroute J) := by
    ext i; rw [AlgHom.comp_apply,writeRaw,MvPolynomial.aeval_X, emblem_read,probe,MvPolynomial.aeval_X]; rfl
  exact DFunLike.congr_fun he x

theorem writeRaw_after (X : WickPol G) : reduceEq (writeRaw X)=X := by
  apply equalPol; intro A; rw [jet_value,writeRaw_read,show reroute (fun i => gaugeJet (A i))=A by funext i; exact sends_back _]

open MvPolynomial (IsWeightedHomogeneous)
section grades
variable {M : Type*} [AddCommMonoid M] (w : ℕ → M)

lemma gradientReduce (i : Labels.Key G) : IsWeightedHomogeneous (fun i : Slot G => w i.1) (reduceEq (MvPolynomial.X i)) (w i.1) := by
  rw [reduceEq,MvPolynomial.aeval_X]; apply IsWeightedHomogeneous.sum
  intro a _; apply MvPolynomial.IsWeightedHomogeneous.C_mul; exact MvPolynomial.isWeightedHomogeneous_X ..

lemma gradientEmblem (P : Taylor G j→ₗ[ℝ] ℝ) : IsWeightedHomogeneous (fun i : Labels.Key G => w i.1) (emblem G j P) (w j) := by
  unfold emblem; apply IsWeightedHomogeneous.sum; intro a _; apply IsWeightedHomogeneous.C_mul; exact MvPolynomial.isWeightedHomogeneous_X ..

lemma gradientWrite (i : Slot G) : IsWeightedHomogeneous (fun i : Labels.Key G => w i.1) (writeRaw (MvPolynomial.X i)) (w i.1) := by
  rw [writeRaw,MvPolynomial.aeval_X]; exact gradientEmblem ..
end grades

def costKey (i : Slot G) := i.1+2
def through (G : Gauge) (d : ℕ) := byWeight (costKey (G:=G)) (Set.Iic d)

def stain (u : G.El) (P : TaylorTower G) : TaylorTower G := fun i => actionG u i (P i)

/-- Invariant on the on-shell sector. -/
def secret (p : WickPol G) := ∀ (u : G.El) (V : TaylorTower G), probe (stain u V) p=probe V p


end YM.Extra.FD
