import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import YM.Bid.Drops
import YM.Bid.Loan
import YM.Next.MAXWELL.House
import YM.Next.MAXWELL.Pole
import YM.Pressure.Seeds
import YM.Work.A13

/-! # Proper quarter turns inside Signed, the internal parameter action -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free.Corners
open Set Function Filter Tensor Analysis MeasureTheory Wick
open Ortho Org
open scoped ContDiff Topology BigOperators InnerProductSpace

def quarter (a b : Axis) : Signed := ⟨Equiv.swap a b,fun i => decide (i=a)⟩

open scoped Matrix.Norms.Frobenius in
lemma fact (s : Ortho.Skew) (t r : ℝ) : oneParameter s (t+r) = oneParameter s t * oneParameter s r := by
  apply Subtype.ext; change NormedSpace.exp ((t+r) • s.val)= _ * _
  rw [add_smul]
  have h : Commute (t • s.val) (r • s.val) := by simp [Commute,SemiconjBy,smul_comm t]
  exact NormedSpace.exp_add_of_commute h

lemma sendsTime (a b : Axis) (h : a≠b) : (quarter a b).ortho = oneParameter (Ortho.plane a b) (Real.pi/2) := by
  apply Ortho.ext; intro x
  have H := Work.A13.plane_givens h x (Real.pi/2)
  dsimp only at H
  rw [Real.sin_pi_div_two, Real.cos_pi_div_two] at H
  apply PiLp.ext; intro i
  obtain ⟨ha,hb,hc⟩ := H
  by_cases ht : i=a
  · subst i; rw [ha]; simp [quarter,Signed.ortho_move, Signed.act,h.symm]
  by_cases hv : i=b
  · subst i; rw [hb]; simp [quarter,Signed.ortho_move, Signed.act]
  rw [hc _ ht hv]; simp [quarter, Signed.ortho_move, Signed.act, Equiv.swap_apply_of_ne_of_ne ht hv,ht]

lemma quarter_house (a b : Axis) (h : a≠b) (r : ℝ) (hr : 0<r) :
    house ((-r) • basis a) * house (basis a+basis b) = (quarter a b).ortho := by
  apply Ortho.ext; intro x; rw [Ortho.move_mul]
  have ht : ‖basis a+basis b‖^2 = 2 := by rw [norm_add_sq_real]; simp [h]; norm_num
  have he (y : E4) : Ortho.move (house ((-r) • basis a)) y = Ortho.move (Signed.reflect a) y := by
    apply PiLp.ext; intro i
    change M4.move (houseM _) _ _= _; rw [house_on ((-r) • basis a) y];
    simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hr, real_inner_smul_left, basis_inner, basis_norm,mul_one]
    by_cases H : i=a
    · subst i; simp; field_simp; ring
    simp [H]
  rw [he,sendsTime a b h]
  have hu := Work.A13.plane_givens h x (Real.pi/2)
  apply PiLp.ext; intro i
  obtain ⟨ha,hb,hc⟩ := hu
  by_cases h1 : i=a
  · subst i; rw [ha,show Ortho.move (house _) x = _ from house_on (basis a+basis b) x]
    simp [ht,inner_add_left,h]
  by_cases h2 : i=b
  · subst i; rw [hb,show Ortho.move (house _) x = _ from house_on (basis a+basis b) x]
    simp [ht,inner_add_left,h.symm]
  rw [hc _ h1 h2,show Ortho.move (house _) x = _ from house_on (basis a+basis b) x]
  simp [h1,h2]

theorem proper (a b : Axis) (h : a≠b) : (quarter a b).matrix.det=1 := by
  let K := Ortho.plane a b
  have he : (quarter a b).ortho=oneParameter K (Real.pi/2) := sendsTime a b h
  let t := Real.pi/2/2
  let T := oneParameter K t
  rw [show (quarter a b).matrix=T.val*T.val from (congr_arg (fun p : Ortho => p.val) (show (quarter a b).ortho=T*T from by
    rw [he,show T*T=oneParameter K (t+t) from (fact K t t).symm, add_halves]))]
  rw [Matrix.det_mul]
  have hv := congr_arg Matrix.det (Ortho.transp T); rwa [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at hv

lemma bracket_orient (g : Signed) (a b : Axis) : orients g (Ortho.plane a b) =
    ((if g.flip a then (-1:ℝ) else 1) * if g.flip b then (-1:ℝ) else 1) • Ortho.plane (g.perm a) (g.perm b) := by
  apply Subtype.ext
  let P := g.ortho.val
  have he (a b : Axis) : P*Matrix.single a b 1*star P =
      ((if g.flip a then (-1:ℝ) else 1) * if g.flip b then (-1:ℝ) else 1) • Matrix.single (g.perm a) (g.perm b) 1 := by
    apply Matrix.ext; intro i j
    have hp : (P*Matrix.single a b 1*star P : M4) i j = P i a * P j b := by
      rw [Matrix.mul_apply]
      have ht k : (P * Matrix.single a b 1 : M4) i k = if k=b then P i a else 0 := by
        rw [Matrix.mul_apply]; by_cases h : k=b <;> simp_all [Matrix.single_apply,mul_ite,Ne.symm]
      simp only [ht,ite_mul, zero_mul]; rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ _)]; rfl
    rw [hp]; simp only [P,Signed.ortho, Signed.matrix_at, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
    by_cases h1 : g.perm a=i <;> by_cases h2 : g.perm b=j <;> simp_all [Ne.symm]
  change P*(_-_)*star P=_
  rw [mul_sub,sub_mul,he,he,mul_comm (if g.flip b then (-1:ℝ) else 1),← smul_sub]; rfl

private lemma commute_inv_apply {M : Type*} [AddCommGroup M] [Module ℝ M]
    (T : Ortho.Skew →ₗ[ℝ] Ortho.Skew →ₗ[ℝ] M) (hp : ∀ a b (u v : Ortho.Skew), a≠b →
      T (orients (quarter a b) u) (orients (quarter a b) v) = T u v)
    (p q : Axis) (he : p≠q) (a b i l : Axis) :
      T (orients (quarter p q * quarter p q) (Ortho.plane a b))
        (orients (quarter p q * quarter p q) (Ortho.plane i l))=
        T (Ortho.plane a b) (Ortho.plane i l) := by
  have hm (g k : Signed) (K : Ortho.Skew) : orients (g*k) K=orients g (orients k K) := by
    have he : (g*k).ortho=g.ortho*k.ortho := map_mul Signed.inclusionO ..
    apply Subtype.ext; change (g*k).ortho.val*K.val*star (g*k).ortho.val=
      g.ortho.val*(k.ortho.val*K.val*star k.ortho.val)*star g.ortho.val
    rw [he];
    change (g.matrix*k.matrix)*K.val*star (g.matrix*k.matrix)=_
    simp only [star_mul,mul_assoc]; congr
  rw [hm,hm,hp _ _ _ _ he,hp _ _ _ _ he]

theorem none {M : Type*} [AddCommGroup M] [Module ℝ M]
    (T : Ortho.Skew →ₗ[ℝ] Ortho.Skew →ₗ[ℝ] M) (h : ∀ u,T u u=0) (hp : ∀ a b (u v : Ortho.Skew), a≠b →
      T (orients (quarter a b) u) (orients (quarter a b) v)=T u v) : T=0 := by
  have halt (u v) : T v u= - T u v := by
    have he := h (u+v); simp only [map_add, LinearMap.add_apply, h, add_zero,zero_add] at he
    exact eq_neg_of_add_eq_zero_left he
  have hz {x : M} (hx : x= -x) : x=0 := by
    apply (smul_right_injective M (by norm_num : (2:ℝ)≠0));
    change (2:ℝ) • x = (2:ℝ) • 0; rw [two_smul,smul_zero]; nth_rw 1 [hx]; simp
  have ht (a b c : Axis) (ha : a≠b) (hb : a≠c) : T (Ortho.plane a b) (Ortho.plane a c)=0 := by
    by_cases hk : b=c
    · subst c; exact h _
    obtain ⟨d, hd, hv, hi⟩ : ∃ d : Axis,d≠a ∧ d≠b ∧ d≠c := by
      exact (show ∀ i j k : Fin 4, ∃ l : Fin 4, l≠i ∧ l≠j ∧ l≠k from by decide) a b c
    let s := quarter c d * quarter c d
    have hs (i j) : orients s (Ortho.plane i j) = _ := bracket_orient s i j
    apply hz
    conv_lhs => rw [← show T (orients s (Ortho.plane a b)) (orients s (Ortho.plane a c)) = _ from commute_inv_apply T hp c d hi.symm a b a c]
    simp only [hs]
    simp [s, quarter,Equiv.swap_apply_def,hb,hd,hv,hi,hk,Ne.symm]
  have hd (a b i l : Axis) (hab : a ≠ b) (hai : a≠i) (hal : a≠l) (hbi : b≠i) (hbl : b≠l) (hil : i≠l) :
      T (Ortho.plane a b) (Ortho.plane i l)=0 := by
    apply hz
    conv_lhs => rw [← hp a i _ _ hai]
    have heta : orients (quarter a i) (Ortho.plane a b)= -Ortho.plane i b := by rw [bracket_orient]; simp [quarter,Equiv.swap_apply_def,hab,hbi,Ne.symm]; exact neg_one_smul ℝ (Ortho.plane i b)
    have heib : orients (quarter a i) (Ortho.plane i l)= Ortho.plane a l := by rw [bracket_orient]; simp [quarter,Equiv.swap_apply_def,hai,hal,hil,Ne.symm]
    rw [heta,heib,map_neg,LinearMap.neg_apply]; congr 1
    conv_lhs => rw [← hp b l _ _ hbl]
    have Hta : orients (quarter b l) (Ortho.plane i b)= -Ortho.plane i l := by rw [bracket_orient]; simp [quarter,Equiv.swap_apply_def,hbi,hil,Ne.symm]; exact neg_one_smul ℝ (Ortho.plane i l)
    have Htz : orients (quarter b l) (Ortho.plane a l)= Ortho.plane a b := by rw [bracket_orient]; simp [quarter,Equiv.swap_apply_def,hab,hal,hbl,Ne.symm]
    rw [Hta,Htz,map_neg,LinearMap.neg_apply,halt (Ortho.plane a b), neg_neg]
  have hh (a b : Axis) : Ortho.plane b a = -Ortho.plane a b := Subtype.ext (neg_sub _ _).symm
  have hk (a b i l : Axis) : T (Ortho.plane a b) (Ortho.plane i l)=0 := by
    have hu (a) : Ortho.plane a a=0 := Subtype.ext (sub_self _)
    rcases eq_or_ne a b with he|he
    · subst b; simp [hu]
    rcases eq_or_ne i l with h1|h1
    · subst l; simp [hu]
    by_cases h' : a=i
    · subst i; exact ht a b l he h1
    by_cases h'' : a=l
    · subst l; rw [hh a i]; simp only [map_neg,ht a b i he h1.symm,neg_zero]
    by_cases hb : b=i
    · subst i; rw [hh b a]; simp only [map_neg,LinearMap.neg_apply,ht b a l he.symm h1, neg_zero]
    by_cases hl : b=l
    · subst l; rw [hh b a,hh b i]; simp only [map_neg,LinearMap.neg_apply,ht b a i he.symm h1.symm,neg_zero]
    exact hd a b i l he h' h'' hb hl h1
  apply LinearMap.ext_on Spin.spans; rintro x ⟨p,rfl⟩; apply LinearMap.ext_on Spin.spans; rintro y ⟨q,rfl⟩; exact hk ..
end YM.Maxwell.Free.Corners
