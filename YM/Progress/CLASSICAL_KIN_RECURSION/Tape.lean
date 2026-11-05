import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Laurent.Eval

set_option warningAsError false

/-!
# Laurent tape. This one has arbitrary finite numbers of independent variables
and passive real Banach-space coefficients. Widths enter and leave explicitly.
We need quantitative solvability in three and four legs before allocating the
classical invoices in the cap tables.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Spools
open Lattice RG Laurent
open scoped BigOperators Topology

variable {ι X : Type} [Fintype ι] [NormedAddCommGroup X]

/-- convenient point bound in coefficient (NOT symbol) convention. Convert to and
from l1 budgets, paying a width fraction when summing. -/
def Drops (σ M : ℝ) (u : On ι X) : Prop := ∀ x, ‖u x‖ ≤ M*Real.exp (-σ*size x)
lemma Drops.nonneg {σ M : ℝ} {u : On ι X} (h : Drops σ M u) : 0≤M := by
  have ht := (norm_nonneg _).trans (h (0:Shift ι)); simpa [size] using ht

lemma Drops.mono {σ M σ' M' : ℝ} {u : On ι X} (h : Drops σ M u) (ht : σ'≤σ) (hh : M≤M') : Drops σ' M' u := by
  intro x
  refine (h x).trans <| mul_le_mul hh (Real.exp_monotone ?_) (Real.exp_pos _).le (h.nonneg.trans hh)
  exact mul_le_mul_of_nonneg_right (neg_le_neg ht) (by positivity)

lemma Drops.zero (σ : ℝ) : Drops σ 0 (0:On ι X) := by simp [Drops]

lemma Drops.plus {σ M N : ℝ} {u v : On ι X} (h : Drops σ M u) (g : Drops σ N v) : Drops σ (M+N) (u+v) := by
  intro x
  rw [add_mul]; exact (norm_add_le _ _).trans (add_le_add (h x) (g x))








variable [NormedSpace ℝ X]
lemma Drops.scale {σ M : ℝ} {u : On ι X} (h : Drops σ M u) (t : ℝ) : Drops σ (|t| *M) (t • u) := by
  intro i; rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_assoc]; exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

variable (ι X) in
/-- Analytic lifetime; inherited submodule operations. -/
def tape : Submodule ℝ (On ι X) where
  carrier := { f | ∃ σ M : ℝ,0 < σ ∧ Drops σ M f }
  add_mem' := fun  ⟨σ,M,hσ,hM⟩ ⟨τ,C,hτ,hC⟩ =>
    ⟨min σ τ,M+C,lt_min hσ hτ,(hM.mono (min_le_left ..) le_rfl).plus (hC.mono (min_le_right ..) le_rfl)⟩
  zero_mem' := ⟨1,0,one_pos,Drops.zero _⟩
  smul_mem' t _ := fun ⟨σ,M,hσ,hM⟩ => ⟨σ,|t| *M,hσ,hM.scale _⟩

variable (ι X) in
abbrev Reel := ↥(tape ι X)
lemma Reel.life (A : Reel ι X) : ∃ σ M : ℝ,0 < σ ∧ Drops σ M A.val := A.property



section
variable {S : Type*}
@[simp] lemma Reel.sum_val (V : Finset S) (A : S → Reel ι X) (x) : (∑ i∈V,A i).val x=∑ i∈V,(A i).val x := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | insert i V hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,Submodule.coe_add,Pi.add_apply,ih]
end

/-- Shift action is multiplication by z^d on Laurent coefficients. -/
def push (d : Shift ι) (u : On ι X) : On ι X := fun x => u (x-d)
omit [NormedSpace ℝ X] in
lemma Drops.push {σ M : ℝ} {u : On ι X} (h : Drops σ M u) (d : Shift ι) (hh : 0≤σ) :
    Drops σ (Real.exp (σ*size d)*M) (push d u) := by
  intro x; unfold Spools.push; rw [mul_comm (Real.exp _) M,mul_assoc,← Real.exp_add]
  refine (h (x-d)).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.nonneg)
  have he : (size x:ℝ)≤↑(size (x-d))+(size d:ℝ) := by exact_mod_cast (show size x≤_ from
    (show size x=size ((x-d)+d) by rw [sub_add_cancel]).le.trans (size_add _ _))
  nlinarith

def spool (d : Shift ι) : Reel ι X →ₗ[ℝ] Reel ι X where
  toFun u := ⟨push d u.val,by obtain ⟨σ,M,h,g⟩:=u.life; exact ⟨σ,_,h,g.push _ h.le⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

lemma spool_comm (u : Reel ι X) (d f : Shift ι) : spool d (spool f u)=spool f (spool d u) := by
  apply Subtype.ext; funext x
  change u.val (x-d-f)=u.val (x-f-d); rw [sub_right_comm]

def hitch (d : Shift ι) : Reel ι X →ₗ[ℝ] Reel ι X := spool d - LinearMap.id

lemma hitches (u : Reel ι X) (d) : hitch d u=spool d u-u := rfl

lemma hitch_comm (u : Reel ι X) (d f : Shift ι) : hitch d (hitch f u)=hitch f (hitch d u) := by
  simp_rw [hitches,map_sub]; rw [spool_comm]; abel
end YM.Progress.ClassicalKin.Spools
