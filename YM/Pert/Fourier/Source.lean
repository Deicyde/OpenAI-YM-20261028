import YM.Pert.Fourier.Adjoint
import YM.Pert.Fourier.Inversion
/-! Fourier inversion of the orbital free covariance on links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice Complex Function BigOperators
variable {G : Gauge} {n : Side}

def formElem (l : Links n) (u : G.Color) : Module.Dual ℝ ↥(LinkP G n) where
  toFun A := inner ℝ (A.val l) u
  map_add' A B := inner_add_left ..
  map_smul' r A := real_inner_smul_left ..
/-- Green gradient link inverse for a unit *point* forcing on orbit. -/
def ghostLink (l : Links n) (u : G.Color) (b : Links n) := if b.2=l.2 then ((Full.toroid (b.1-l.1)).re) • u else 0
lemma ghost_image (l b : Links n) (u : G.Color) : ghostLink l u (image b)=ghostLink (image l) u b := by
  unfold ghostLink image; dsimp
  split
  next h => congr 1; rw [show -b.1-step b.2-l.1 = -(b.1-(-l.1-step l.2)) by rw [h]; abel]; apply Full.toroid_even
  next => rfl

def response (l : Links n) (u : G.Color) : ↥(LinkP G n) := ⟨ghostLink l u - ghostLink (image l) u, fun b => show _ by simp [Pi.sub_apply,ghost_image,image_image]⟩
lemma re_nfour : ((n.val:ℂ)^(-4:ℤ)).re = (n.val:ℝ)^(-4:ℤ) := by rw [show (n.val:ℂ)^(-4:ℤ) = ((n.val:ℝ)^(-4:ℤ):ℝ) by simp,Complex.ofReal_re]
lemma lap_shift (a : Site n) : lap (fun y : Site n => (Full.toroid y).re) a = -(if a=0 then 1 else 0) + (n.val:ℝ)^(-4:ℤ) := by
  have he := congrArg reCLM (Full.lap_eq a)
  simp only [map_sum,map_add,map_sub,apply_ite reCLM _, two_smul,reCLM_apply,one_re,zero_re,neg_re,re_nfour] at he
  simpa only [lap,two_smul,apply_ite Complex.re _ , zero_re,one_re] using he
lemma lap_ghost (a : Links n) (u : G.Color) (i : Axis) (b : Site n) : lap (fun z : Site n => ghostLink a u (z,i)) b =
    -(if b=a.1 ∧ i=a.2 then u else 0) + (if i=a.2 then ((n.val:ℝ)^(-4:ℤ)) • u else 0) := by
  unfold ghostLink; dsimp
  by_cases h : i=a.2
  · simp only [h, if_true, and_true]
    unfold lap; simp only [← add_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← sub_smul, ← Finset.sum_smul]
    suffices hz : ((∑ l : Axis, ((Full.toroid (b+step l-a.1)).re +(Full.toroid (b-step l-a.1)).re - (2:ℝ)*(Full.toroid (b-a.1)).re)) : ℝ) = -(if b=a.1 then 1 else 0) + (n.val:ℝ)^(-4:ℤ) by split <;> simp_all only [if_true, if_false, and_true, and_false, ↓reduceIte, Nat.cast_ofNat,add_smul] <;> simp
    let e := lap_shift (b-a.1)
    have h1 (l : Axis) : b+step l-a.1=b-a.1+step l := by abel
    have h2 (l : Axis) : b-step l-a.1=b-a.1-step l := by abel
    simpa only [lap,h1,h2,nsmul_eq_mul,sub_eq_zero,Nat.cast_ofNat] using! e
  simp [h,lap]
lemma inverse_eq (a : Links n) (u : G.Color) : kernelEquiv G n (response a u) = formElem a u := by
  ext1 v
  change form (response a u) v = inner ℝ (v.val a) u
  rw [form_symm]; unfold form; change ((∑ x : Site n, ∑ i : Axis, ∑ j : Axis, _) + ∑ x : Site n, _) / 2 = _
  change ((∑ x : Site n, ∑ i : Axis, ∑ j : Axis, if i<j then inner ℝ (cur _ x i j) (cur (response a u).val x i j) else 0) + ∑ x : Site n, inner ℝ (divB v.val x) (divB _ x)) / 2 = _
  rw [total]
  have hr (i : Axis) (x : Site n) : lap (row (response a u).val i) x = -(if x=a.1 ∧ i=a.2 then u else 0) + (if x=(image a).1 ∧ i=(image a).2 then u else 0) := by
    have eqv (F H : Site n → G.Color) : lap (F-H) x=lap F x - lap H x := by unfold lap; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; dsimp; rw [smul_sub]; abel
    rw [show row _ i = ((row (ghostLink a u) i)-(row (ghostLink (image a) u) i)) from rfl, eqv];  change lap (fun z => ghostLink a u (z,i)) x - (lap (fun z => ghostLink (image a) u (z,i)) x) = _; rw [lap_ghost, lap_ghost,show (image a).2=a.2 from rfl]; abel
  have hv : inner ℝ (v.val (image a)) u = - inner ℝ (v.val a) u := by rw [v.property,inner_neg_left]
  simp only [hr,inner_add_right,inner_neg_right,Finset.sum_neg_distrib,Finset.sum_add_distrib]; rw [← Finset.sum_neg_distrib]
  have he (a : Links n) : (∑ x, ∑ i, inner ℝ (v.val (x,i)) (if x=a.1 ∧ i=a.2 then u else 0)) = inner ℝ (v.val a) u := by
    rw [Finset.sum_eq_single a.1]; rw [Finset.sum_eq_single a.2]
    all_goals simp_all
  simp only [Finset.sum_neg_distrib,neg_add_rev,neg_neg]; rw [he,he,hv]; ring
lemma covar_link (a b : Links n) (u t : G.Color) : covar (formElem a u) (formElem b t) =
   inner ℝ u t * (if b.2=a.2 then (Full.toroid (b.1-a.1)).re - (Full.toroid (b.1+ a.1+step a.2)).re else 0) := by
   rw [covar,←inverse_eq a u,LinearEquiv.symm_apply_apply]
   dsimp [formElem,response,ghostLink]; rw [show b.1 - (image a).1 = b.1+a.1+step a.2 from by dsimp [image]; rw [show (-a.1-step a.2)=-(a.1+step a.2) by simp [neg_add,sub_eq_add_neg,add_comm],sub_neg_eq_add,add_assoc]]
   split <;> simp_all [show (image a).2=a.2 from rfl, inner_sub_left,real_inner_smul_left]; ring
end YM.Pert.Orb
