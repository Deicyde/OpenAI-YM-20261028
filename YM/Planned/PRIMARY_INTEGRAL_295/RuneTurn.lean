import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Next.FREE_KERNELS.Amend
import YM.Next.FREE_KERNELS.Pulled
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06

/-!
# Covariance of the alias head under signed axes with bond origins

In particular a reversal is a **negative** reordered 1-cochain with a
one-link shift; analytic multipliers record this shift from initial-vertex
convention. Entire block/op and label transformations have to use the same
action, not pass a diagonal field bill and retune the leading columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Filter Function Set Lattice Laurent Bloch Exterior RG Next.Free Next.Free.Flight
open scoped Topology BigOperators ContDiff ComplexConjugate Matrix.Norms.Frobenius
variable {L : Side} {j t : ℕ}

def aspect (s : Signed) (p : Momentum) (a : Axis) : ℂ := if s.flip a then -twirl (p a) 1 else 1
lemma aspect_ne (s : Signed) (p : Momentum) (a : Axis) : aspect s p a ≠ 0 := by unfold aspect twirl; split <;> simp [Complex.exp_ne_zero]
lemma aspect_cancel (s : Signed) (p : Momentum) (a : Axis) : aspect s p a * aspect s (-p) a = 1 := by
  unfold aspect; split; swap; · exact mul_one _
  simp only [neg_mul_neg,Pi.neg_apply,twirl_neg]; rw [← twirl_add,add_neg_cancel,twirl_nil]

def reed (s : Signed) (p : Momentum) (a : TypeFace 1) := aspect s p (axisEquiv.symm a)
def chartIso (s : Signed) : Equiv.Perm (TypeFace 1) := (axisEquiv.symm.trans s.perm).trans axisEquiv
@[simp] lemma chart_at (s : Signed) (a : Axis) : chartIso s (coord a)=coord (s.perm a) := by
  change chartIso s (axisEquiv a)=axisEquiv _; simp only [chartIso,Equiv.trans_apply, axisEquiv.symm_apply_apply]
@[simp] lemma reed_at (s : Signed) (p : Momentum) (a : Axis) : reed s p (coord a)=aspect s p a := by
  change aspect s p (axisEquiv.symm (axisEquiv a))=_; rw [axisEquiv.symm_apply_apply]

private lemma chip_swap (s : Signed) (p : Momentum) (i : Axis) : aspect s p i * chip ((s.act p) (s.perm i))=chip (p i) := by
  rw [Signed.act_at,aspect]; split; swap; · exact one_mul _
  unfold chip; have he (a : ℂ) : Complex.exp (Complex.I*a)=twirl a 1 := by simp [twirl]
  simp only [he,twirl_neg]; have hh : twirl (p i) 1*twirl (p i) (-1)=1 := by rw [← twirl_add,add_neg_cancel,twirl_nil]
  rw [mul_sub,neg_mul,hh]; ring

private lemma chip_sample (M : Side) (p : Momentum) (i : Axis) (a : TypeFace 0) :
    signal M 0 p (coord i) a=tripQ M p i := by
  rw [vac_only a]; unfold signal wedge
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single i]; swap
  · intro b _ hb; simp [left,coord,hb]
  swap; · simp
  have he : Finset.filter (fun a => a < i) ({i} : Finset Axis)=∅ := by ext; simp; rintro rfl; rfl
  simp [coord,left,parity,Exterior.pre,remove,vac,he]

private lemma shift_rail (P : Flight j t) (p : Momentum) (l : Site P.L) (a : Axis) :
    let z := aliasAt p l a
    twirl z 1 * rail P.L z=rail P.L (-z)*twirl (p a) 1 := by
  intro z
  have he : twirl (p a) 1= twirl z P.L.val := by
    have hz : ((P.L.val:ℂ)*z)=p a+2*(Real.pi:ℂ)*(lift l a) := by
      have hh := congr_fun (alias_scale p l) a; simpa only [z,nsmul_eq_mul, Pi.mul_apply,Pi.natCast_apply,
        Pi.add_apply,reciprocal] using hh
    conv_lhs => rw [← twirl_period (p a) (lift l a) 1,← hz]
    simpa using (twirl_scale z P.L.val 1)
  let m := mid P.L
  have hp := mid_double P.L P.odd
  have hu (a : ℤ) (s : ℂ) : twirl s a*twirl s (-a)=1 := by rw [← twirl_add,add_neg_cancel,twirl_nil]
  have hv := plank_even P.L P.odd z
  unfold plank at hv; rw [twirl_neg,neg_neg] at hv
  rw [he]
  apply mul_left_cancel₀ (show twirl z (-(m+1))≠0 from Complex.exp_ne_zero _)
  conv_rhs => rw [mul_comm (rail P.L _),← mul_assoc,← twirl_add]
  rw [← mul_assoc,← twirl_add, show (-(m+1)+(1:ℤ))=-m by omega, show -(m+1)+(P.L.val:ℤ)=m by unfold m; omega]; exact hv.symm

private lemma mask_swap (s : Signed) (p : Momentum) (f g : Axis → ℂ) (h : ∀ i, g (s.perm i)=f i) (a b : TypeFace 1) :
    reed s p a * mask 1 g (chartIso s a) (chartIso s b)=mask 1 f a b * reed s p b := by
  simp_rw [mask_value, (chartIso s).injective.eq_iff]; by_cases H : a=b
  · subst b; rw [if_pos rfl,if_pos rfl]; change _ * g (axisEquiv.symm (axisEquiv _)) = _; rw [axisEquiv.symm_apply_apply,Equiv.trans_apply,h]; exact mul_comm ..
  simp [H]

-- spectral square: endpoint weights and their transformed frequencies
private def Square {m n : Type*} (T B : Matrix m n ℂ) (u : Equiv.Perm m) (v : Equiv.Perm n) (x : m→ℂ) (y : n→ℂ) :=
    ∀ a b, x a * B (u a) (v b)=T a b*y b

namespace Square
variable {m n k : Type*} {u : Equiv.Perm m} {v : Equiv.Perm n} {w : Equiv.Perm k}
    {x : m → ℂ} {y : n→ℂ} {z : k→ℂ} {T B Q R : Matrix m n ℂ}

private lemma add (h : Square T B u v x y) (g : Square Q R u v x y) : Square (T+Q) (B+R) u v x y := by
  intro a b; simp only [Matrix.add_apply,mul_add,h a b,g a b,add_mul]
private lemma sub (h : Square T B u v x y) (g : Square Q R u v x y) : Square (T-Q) (B-R) u v x y := by
  intro a b; simp only [Matrix.sub_apply,mul_sub,h a b,g a b,sub_mul]
private lemma scale (h : Square T B u v x y) (c : ℂ) : Square (c • T) (c • B) u v x y := by
  intro a b; simp only [Matrix.smul_apply,smul_eq_mul]; rw [mul_left_comm,h]; ring
private lemma mul [Fintype n] {S A : Matrix n k ℂ} (h : Square T B u v x y) (g : Square S A v w y z) :
    Square (T*S) (B*A) u w x z := by
  classical
  intro a b
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp v (fun i => x a*(B (u a) i * A i (w b)))]
  exact Finset.sum_congr rfl fun i _ => by rw [← mul_assoc,h,mul_assoc,g,← mul_assoc]
end Square

section Bond
variable (s : Signed) (p : Momentum) (P : Flight j t)

private lemma scope (A : Side) : Square (signal A 0 p) (signal A 0 (s.act p)) (chartIso s) (.refl _) (reed s p) (fun _=>1) := by
  intro a b
  obtain ⟨a,h⟩ := axisEquiv.surjective a; rw [coord_map] at h; subst h
  rw [chart_at,chip_sample,chip_sample, reed_at,tripQ,mul_left_comm, chip_swap, tripQ,mul_one]

private lemma negative_scope (A : Side) : Square (mirage A 0 p) (mirage A 0 (s.act p)) (.refl _) (chartIso s) (fun _=>1) (reed s p) := by
  intro a b; unfold mirage; rw [← Signed.act_neg]
  have hv := scope s (-p) A b a
  simp only [Equiv.refl_apply,mul_one] at hv
  have hh : reed s p b * reed s (-p) b=1 := aspect_cancel s p _
  dsimp only [Matrix.transpose_apply,Equiv.refl_apply]
  calc 1*_ = (reed s p b*reed s (-p) b)*_ := by rw [hh]
       _ = _ := by rw [mul_assoc,show reed s (-p) b * _ = _ from hv]; ring

private lemma filter_signed (P : Flight j t) (p : Momentum) : massFilter P.patch (s.act p)=massFilter P.patch p := by
  unfold massFilter; rw [Train.area_signed P.patch.L P.patch.odd_side]

set_option maxHeartbeats 600000 in
private lemma flux_swap (l : Site P.L) : let q := aliasAt p l
    Square (flux P 1 q) (flux P 1 (s.act q)) (chartIso s) (chartIso s) (reed s q) (reed s p) := by
  intro q a b
  unfold flux hinges; simp only [Matrix.transpose_smul,mask_trans,Matrix.smul_apply,smul_eq_mul,
    ← Signed.act_neg,filter_signed]
  simp_rw [mask_value,(chartIso s).injective.eq_iff]
  by_cases h : a=b; swap; · simp [h]
  subst b; rw [if_pos rfl,if_pos rfl]
  obtain ⟨b,hb⟩ := axisEquiv.surjective a; subst a
  simp only [reed, chartIso,Equiv.trans_apply, axisEquiv.symm_apply_apply,Signed.act_at]
  unfold aspect; dsimp only [Pi.neg_apply]; split; swap; · ring
  rw [neg_neg, mul_left_comm, neg_mul,show twirl (q b) 1*rail _ _ = _ from shift_rail P p l b]; ring

private lemma tons (k : ℝ) : tabE k P (s.act p)=tabE k P p ∧ ∀ q : Momentum, weightsE k P (s.act p) (s.act q)=weightsE k P p q := by
  have ht q : total k P (s.act q)= total k P q := by
    unfold total; rw [← Equiv.sum_comp s.perm]; refine Finset.sum_congr rfl fun i _ => ?_
    unfold scaleD; rw [Train.D_signed]
  have he : tabE k P (s.act p)= tabE k P p := by
    unfold tabE; rw [← Equiv.sum_comp (s.actEquiv (R:=Per P.L)).toEquiv]; refine Finset.sum_congr rfl fun i _ => ?_
    change yen _ (aliasAt (s.act p) (s.act i))*total k P (aliasAt (s.act p) (s.act i))=_
    rw [alias_signed P.odd,ht]; unfold yen; simp only [← Signed.act_neg,filter_signed]
  refine ⟨he,fun q => ?_⟩; unfold weightsE; rw [← Signed.act_neg s q, filter_signed,ht,he]

variable (k : ℝ) (hk : 0 < k)
private lemma focus (A : Side) {j} (B : Train j) :
    Square (fieldD A k B p) (fieldD A k B (s.act p)) (chartIso s) (chartIso s) (reed s p) (reed s p) ∧
      Square (fieldI A k B p) (fieldI A k B (s.act p)) (chartIso s) (chartIso s) (reed s p) (reed s p) := by
  have he (i : Axis) : scaleD A k B (s.act p) (s.perm i)=scaleD A k B p i := by unfold scaleD; rw [Train.D_signed]
  exact ⟨mask_swap s p _ _ he,mask_swap s p _ _ (fun i => congr_arg Inv.inv (he i))⟩
include hk in
/-- Exact alias covariance even on flips or p=0. -/
theorem perspective (l : Site P.L) (hp : p∈baseCube) (a b : Axis) :
    aspect s (aliasAt p l) a * pilot k P (s.act p) (s.act l) (coord (s.perm a)) (coord (s.perm b)) =
      pilot k P p l (coord a) (coord b)*aspect s p b := by
  let K (p : Momentum) := reed s p
  let u := chartIso s
  suffices H : Square (pilot k P p l) (pilot k P (s.act p) (s.act l)) u u (K (aliasAt p l)) (K p) by
    simpa only [K,u,chart_at, reed_at] using H (coord a) (coord b)
  by_cases h : p=0
  · subst p; intro i j; rw [Signed.act_zero]
    by_cases he:l=0
    · subst l; rw [Signed.act_zero,P.pilot_origin,show aliasAt (0:Momentum) (0:Site P.L) = 0 from toe_zero P] -- aliasAt? reduce
      simp_rw [Matrix.one_apply,u.injective.eq_iff]; split <;> simp [*]
    rw [pilot_none P k he,pilot_none P k (fun H => he (s.act_injective (H.trans s.act_zero.symm)))]; simp
  have hz := signed_base hp s
  have he : s.act p ≠ 0 := fun H => h (s.act_injective (H.trans s.act_zero.symm))
  have h1 := base_subset_realCube zone_pos hp; have h2 := base_subset_realCube zone_pos hz
  rw [pilot_match k hk P h1 h,pilot_match k hk P h2 he,alias_signed P.odd]
  let q := aliasAt p l
  let r := rotor 1 k P.land
  have hR : scaleR 1 k P.land (s.act p)=scaleR 1 k P.land p := by unfold scaleR; rw [dollar_sign]
  have hg := focus s p k 1 P.land
  have hP := negative_scope s p 1
  have hr : Square (r p) (r (s.act p)) u u (K p) (K p) := by
    unfold r; rw [rotor_law 1 k hk P.land h2 he, rotor_law 1 k hk P.land h1 h,hR]
    exact (hg.2.sub ((((hg.2.mul (scope s p 1)).mul hP).mul hg.2).scale _))
  unfold scriptA; rw [(tons s p P k).2]
  unfold pipe; rw [hR]
  exact (((focus s q k _ P.wing).1.mul (flux_swap s p P l)).mul hr).add (((scope s q P.L).mul ((hP.mul hg.2).scale _)).scale _)
end Bond
end YM.Planned.PrimaryIntegral295.Carrier
