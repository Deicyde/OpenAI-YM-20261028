import YM.UVExtension.Lamppost.Luster
import YM.UVExtension.Lamppost.Capsule
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Lifting a finite number of angular jets. A different lift at each point/basis
      can restrict the real vehicle. Products evaluated BEFORE taking suprema. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Metric Filter Topology Set BoundedContinuousFunction Complex RG
open scoped BigOperators ContDiff Classical
variable {A Z E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup Z] [NormedSpace ℂ Z]
variable {j k : ℕ} {x:E} {X X' Y Y': E→ℂ} {F : A → E→ℂ} {T:Opening A Z}

structure Foil (x:E) (k:ℕ) (f g : E→ℂ):Prop where
    top : ContDiffAt ℝ (↑k) f x
    congr : ∀ i≤k,iteratedFDeriv ℝ i f x=iteratedFDeriv ℝ i g x

namespace Foil
lemma small (h : Foil x k X X') (p : j≤ k) : Foil x j X X' := ⟨h.top.of_le (by exact_mod_cast p), fun i hi=> h.congr i (hi.trans p)⟩
lemma masks (h : Foil x k X X') (hp:Y=ᶠ[𝓝 x] X) (hx:Y'=ᶠ[𝓝 x] X') : Foil x k Y Y' :=
    ⟨h.top.congr_of_eventuallyEq hp,fun i hi=> (hp.iteratedFDeriv (𝕜:=ℝ) i|>.eq_of_nhds).trans ((h.congr i hi).trans ((hx.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds.symm))⟩
lemma values (h : Foil x k X X'): X x=X' x:=by
  have he:= congr_arg (fun u:E [×0]→L[ℝ] ℂ=> u fun _=>0) (h.congr 0 (Nat.zero_le _)); simpa using he
lemma plus (h : Foil x k X X') (p : Foil x k Y Y') (hv : ContDiffAt ℝ (↑k) X' x) (he : ContDiffAt ℝ (↑k) Y' x) :
    Foil x k (fun i=> X i+Y i) (fun i=>X' i+Y' i):= by
  refine ⟨h.top.add p.top,fun i hi=>?_⟩; change iteratedFDeriv ℝ i (X+Y) x=iteratedFDeriv ℝ i (X'+Y') x
  rw [iteratedFDeriv_add_apply (h.small hi).top (p.small hi).top,iteratedFDeriv_add_apply (hv.of_le (by exact_mod_cast hi))
    (he.of_le (by exact_mod_cast hi)),h.congr i hi,p.congr i hi]
lemma inspire (h : Foil x (k+1) X X') (hv : ContDiffAt ℝ (↑(k+1:ℕ)) X' x) (w:E) : Foil x k (fun i=> fderiv ℝ X i w) (fun i=> fderiv ℝ X' i w) := by
  refine ⟨(h.top.fderiv_right (by simp : (k:WithTop ℕ∞)+1 ≤ _)).clm_apply contDiffAt_const,fun i hi=> ?_⟩; ext m; rw [Luster.fade (h.top.of_le (by exact_mod_cast show i+1 ≤ _ from Nat.add_le_add_right hi 1)),
    Luster.fade (hv.of_le (by exact_mod_cast show i+1≤_ from Nat.add_le_add_right hi 1)), h.congr (i+1) (by omega)]
lemma times (h : Foil x k X X') (p : Foil x k Y Y') (hv : ContDiffAt ℝ (↑k) X' x) (he : ContDiffAt ℝ (↑k) Y' x) :
    Foil x k (fun i=> X i*Y i) (fun i=>X' i*Y' i) := by
  induction k generalizing X X' Y Y' with
  | zero =>
    refine ⟨h.top.mul p.top,fun i hi=>?_⟩; have h':i=0:=by omega
    subst i; ext m; simp [h.values,p.values]
  | succ k ih =>
    have hp' : ContDiffAt ℝ (↑k) Y' x:=he.of_le (by simp)
    have hv' : ContDiffAt ℝ (↑k) X' x:=hv.of_le (by simp)
    let Z i:=X i*Y i; let U i:=X' i*Y' i
    have hZ := h.top.mul p.top; have hW:=hv.mul he
    have hT (v:E): Foil x k (fun i=> fderiv ℝ Z i v) (fun i=> fderiv ℝ U i v):= by
      have hh:= (ih (h.small (by omega)) (p.inspire he v) hv' ((he.fderiv_right (by simp : (k:WithTop ℕ∞)+1 ≤ _)).clm_apply contDiffAt_const))
      have hΨ:= (hv.fderiv_right (by simp : (k:WithTop ℕ∞)+1 ≤ _)).clm_apply (contDiffAt_const (c:=v))
      apply (hh.plus (ih (p.small (by omega)) (h.inspire hv v) hp' hΨ) (hv'.mul ((he.fderiv_right (by simp : (k:WithTop ℕ∞)+1 ≤ _)).clm_apply contDiffAt_const)) (hp'.mul hΨ)).masks
      · filter_upwards [Luster.adjacent h.top,Luster.adjacent p.top] with y hy hy'; unfold Z; rw [fderiv_fun_mul hy hy']; rfl
      filter_upwards [Luster.adjacent hv,Luster.adjacent he] with y hy hy'; unfold U; rw [fderiv_fun_mul hy hy']; rfl
    refine ⟨hZ,?_⟩; rintro (_|i) hi
    · ext m; simp [h.values,p.values]
    ext m
    have hh':i≤k:=by omega
    have hf:= congr_arg (fun u:E [×i]→L[ℝ] ℂ=>u (Fin.init m)) ((hT (m (Fin.last _))).congr i hh')
    rw [Luster.fade (hZ.of_le (by exact_mod_cast hi)),Luster.fade (hW.of_le (by exact_mod_cast hi)),Fin.snoc_init_self] at hf; exact hf
end Foil
end YM.UVExtension.Lamppost
