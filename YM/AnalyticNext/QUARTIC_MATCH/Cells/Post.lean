import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Analysis.Polydisc
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Boundary
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


/-!
# Finite closure and periods on actual curvature cochains

Ungraded tensor-test helpers. Cost and adjoint are for ordinary physical
oriented counting. No orthonorm claim of Cover bundles. Color invariance
carried as a coefficient-module restriction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Matrix Precision RG Function Filter Topology Finset Bid Tensor
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}

/-- No Lie connectedness required. -/
def eligible (G : Gauge) (n : ℕ) : Submodule ℝ (Tensor.T G.Color ℝ n) where
  carrier := {x | ∀ (u : G.El) (F : Fin n → G.Color), x (fun i => G.adjoint u (F i)) = x F}
  add_mem' {_x _y} hx hy u F := congr_arg₂ (·+·) (hx u F) (hy u F)
  zero_mem' _ _ := rfl
  smul_mem' s _x hx u F := congr_arg (s • ·) (hx u F)

abbrev ColorPart (G : Gauge) (n : ℕ) := ↥(eligible G n)
variable {n : ℕ} {c : Side}

abbrev Ink (G : Gauge) (c : Side) := Cell (Per c) → G.Color

def diffDir (a : Axis) (F : Ink G c) (X : Cell (Per c)) : G.Color := if a∈X.2 then
    sign X.2 a • (F (X.1+step a,X.2.erase a)-F (X.1,X.2.erase a)) else 0
def track (F : Ink G c) : Ink G c := ∑ i, diffDir i F

def post (A : ArrayC (Fin n) (Per c) (ColorPart G n)) (F : Fin n → Ink G c) : ℝ :=
    ∑ X, (A X).val (fun i => F i (X i))

private def toggle (a : Axis) : Equiv.Perm (Finset Axis) where
  toFun S := if a∈S then S.erase a else insert a S
  invFun S := if a∈S then S.erase a else insert a S
  left_inv S := by by_cases h : a∈S <;> simp [h]
  right_inv S := by by_cases h : a∈S <;> simp [h]

private lemma one_payment (a : Axis) (L : Cell (Per c) → G.Color →L[ℝ] ℝ) (F : Ink G c) :
    ∑ x : Cell (Per c), (sect a L x) (F x) = ∑ x : Cell (Per c), L x (diffDir a F x) := by
  classical
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm,← Equiv.sum_comp (toggle a)]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a∈b
  · simp [toggle, h,diffDir,sect_at]
  have he : (toggle a) b=insert a b := if_neg h
  simp_rw [he, sect_at, diffDir]
  simp only [h,↓reduceIte,mem_insert_self,sign_insert b a h, erase_insert h, _root_.smul_apply,map_sub,
    map_smul,_root_.sub_apply,← smul_sum,sum_sub_distrib]
  congr 2
  let e := Equiv.subRight (step a : Site c)
  have hx (x : Site c) : F (x,b)= F (e x+step a,b) := by rw [show e x+_=x from sub_add_cancel ..]
  exact (sum_congr rfl fun x _ => congr_arg _ (hx x)).trans (Equiv.sum_comp e (fun x => L (x,insert a b) (F (x+step a,b))))

private lemma all_payment (L : Cell (Per c) → G.Color →L[ℝ] ℝ) (F : Ink G c) :
    ∑ x : Cell (Per c), (rim L x) (F x) = ∑ x : Cell (Per c), L x (track F x) := by
  simp_rw [rim_at, track, Finset.sum_apply,map_sum, _root_.sum_apply]
  rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => one_payment ..

theorem scatter {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] (l : ι) (f : (ι→V)→ℝ) :
    ∑ X : ι→V, ∑ i, f (update X l i)= Fintype.card V • ∑ X,f X := by
  let e : Equiv.Perm ((ι→V)×V) := {
    toFun p := (update p.1 l p.2,p.1 l), invFun p := (update p.1 l p.2,p.1 l),
    left_inv p := by simp, right_inv p := by simp }
  have he := Equiv.sum_comp e fun q => f q.1
  simp_rw [Fintype.sum_prod_type] at he
  simp only [Finset.sum_const,Finset.card_univ,← Finset.smul_sum] at he
  exact he

/-- Duality with the sign conventions of Lattice.d, finite counting. -/
theorem transfers (j : Fin n) (A : ArrayC (Fin n) (Per c) (ColorPart G n)) (F : Fin n → Ink G c) :
    post (lower j A) F=post A (update F j (track (F j))) := by
  let L := update F j (track (F j))
  have hW (Z : ArrayC (Fin n) (Per c) (ColorPart G n)) (F : Fin n → Ink G c) :=
    scatter (V:=Cell (Per c)) j (fun X => (Z X).val (fun i => F i (X i)))
  apply (smul_right_injective ℝ (Nat.cast_ne_zero.mpr (Fintype.card_pos (α:=Cell (Per c))).ne' :
    (↑(Fintype.card (Cell (Per c))) : ℝ) ≠ 0))
  dsimp only; rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, post,post, ← hW,← hW]
  refine Finset.sum_congr rfl fun X _ => ?_
  let B := peek j X A
  let a (i) := F i (X i)
  let D (y : Cell (Per c)) : G.Color →L[ℝ] ℝ := (B y).val.toContinuousLinearMap a j
  have hh Q (y : Cell (Per c)) : (peek j X (lower j A) y).val (update a j Q)=rim D y Q := by
    rw [peek_lower,rim_at,rim_at, _root_.sum_apply]
    change ((eligible G n).subtype (∑ i : Axis,sect i (peek j X A) y)) (update a j Q) = _
    rw [map_sum,_root_.sum_apply]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [sect_at,sect_at]; split; · rfl
    simp only [map_smul,map_sub, _root_.smul_apply, _root_.sub_apply]; rfl
  calc
    _ = ∑ y : Cell (Per c), rim D y (F j y) := by
      apply Finset.sum_congr rfl; intro y _
      change (peek j X (lower j A) y).val _=_
      rw [← hh]; congr 1; funext i; by_cases h : i=j <;> simp [h,a]
    _ = ∑ y : Cell (Per c), D y (track (F j) y) := all_payment D (F j)
    _ = _ := by
      apply Finset.sum_congr rfl; intro y _
      change (A _).val (update _ _ _) = _
      congr 1; funext i; by_cases h : i=j <;> simp [h,a]

lemma post_recovers (A : ArrayC (Fin n) (Per c) (ColorPart G n)) (F : Fin n → G.Color) (X) :
    post A (fun i => Pi.single (X i) (F i))=(A X).val F := by
  unfold post; rw [Finset.sum_eq_single X]
  · congr; funext; simp
  · intro i _ hi
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hi
    exact (A i).val.map_coord_zero j (by simp [hj])
  simp

/-- `liftField` for the finite duality, zeros in UNUSED degrees. -/
def liftField (r : ℕ) (F : fieldDir G c r) : Ink G c := fun x =>
    if h : x.2.card=r then F (x.1,⟨x.2,h⟩) else 0

def shape (r : ℕ) (b : Body r c) : Cell (Per c) := (b.1,b.2.val)



lemma lifted_shape (r : ℕ) (F : fieldDir G c r) (b : Body r c) : liftField r F (shape r b)=F b := by
  unfold shape liftField; rw [dif_pos b.2.property]

lemma track_shape (r : ℕ) (F : Ink G c) (b : Body (r+1) c) : track F (shape _ b) =
    dColor G c r (F ∘ shape r) b := by
  ext i
  unfold track dColor parts d; simp only [discrete,Finset.sum_apply]; change (∑ x : Axis, diffDir x F (shape _ b)) i=_
  apply Eq.trans ?_ (Finset.sum_congr rfl (f:=fun x : Axis => diffDir x F (shape _ b) i) ?_)
  · let P := (((WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ))).toLinearMap : G.Color →ₗ[ℝ] G.ColorIndex → ℝ)
    exact (map_sum ((LinearMap.proj (R:=ℝ) (φ:=fun _ => ℝ) i).comp P) (fun x => diffDir x F (shape _ b)) Finset.univ)
  intro x _; unfold diffDir; split
  · rename_i hi; rw [dif_pos (show x∈b.2.val from hi)]; rfl
  rename_i hi; rw [dif_neg (show ¬ x∈b.2.val from hi)]; rfl
end YM.AnalyticNext.QuarticMatch.BoxChain
