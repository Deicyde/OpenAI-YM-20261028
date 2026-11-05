import Mathlib.Analysis.Calculus.Taylor
import YM.Analysis.SmoothJets
import YM.Heat.Rows

/-!
# Polar jets without multivar formal chain composition

If sums ∀ θ hold with all collinear jets, use regular PDE coefficient t≠0.
Only transverse jets fed to Analytic f lemma. No assumption bracket.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PDE
open Function Set Filter YM.Analysis
open scoped Topology InnerProductSpace ContDiff BigOperators

abbrev V := ℝ × ℝ
def e : V := (1,0)
def i : V := (0,1)
def side : Set V := {z | 0 < z.1}
lemma opens : IsOpen side := isOpen_lt continuous_const continuous_fst

def C (f : V → ℂ) := ∀ x ∈ side, ContDiffAt ℝ ∞ f x
lemma C.change {f g : V → ℂ} (hf : C f) (h : EqOn f g side) : C g := fun _ hx => (hf _ hx).congr_of_eventuallyEq
  ((eventuallyEq_of_mem (opens.mem_nhds hx) h).symm)
lemma C.add {f g : V → ℂ} (h : C f) (hg : C g) : C (fun x => f x+g x) := fun x hx => (h x hx).add (hg x hx)
lemma C.diff {f g : V → ℂ} (h : C f) (hg : C g) : C (fun x => f x-g x) := fun x hx => (h x hx).sub (hg x hx)
lemma C.incl {f} (h : C f) u : C (D u f) := fun x hx => dSmooth (h x hx) u (by simp)
lemma C.able {f} (H : C f) {x} (h : x ∈ side) : DifferentiableAt ℝ f x := (H x h).differentiableAt (by simp)
lemma C.swaps {f} (H : C f) u v {x} (hx : x∈side) : D u (D v f) x=D v (D u f) x :=
  commuteD ((H x hx).of_le (WithTop.coe_le_coe.mpr le_top)) u v

def tower (f : V → ℂ) (n : ℕ) := (D i)^[n] f
@[simp] lemma root (f) : tower f 0=f := rfl
lemma tower_step (f : V → ℂ) (n) : tower f (n+1)=D i (tower f n) := by rw [tower,iterate_succ_apply',tower]
lemma tower_clock (f : V → ℂ) (n) : tower f (n+1)=tower (D i f) n := by rw [tower, iterate_succ_apply,tower]
lemma C.limbs {f} (h : C f) (n : ℕ) : C (tower f n) := by induction n with
 | zero => exact h
 | succ n hn => rw [tower_step]; exact hn.incl _

lemma D_add {f g : V → ℂ} (hf : C f) (hg : C g) {x} (hx : x∈side) (u : V) :
    D u (fun y => f y+g y) x=D u f x+D u g x := by rw [D, fderiv_fun_add (hf.able hx) (hg.able hx)]; rfl
lemma D_sub {f g : V → ℂ} (hf : C f) (hg : C g) {x} (hx : x∈side) (u : V) :
    D u (fun y => f y-g y) x=D u f x-D u g x := by rw [D, fderiv_fun_sub (hf.able hx) (hg.able hx)]; rfl

lemma vanishing {f g : V → ℂ} (h : EqOn f g side) (n : ℕ) : EqOn (tower f n) (tower g n) side := by
  induction n with
  | zero => exact h
  | succ n hn => intro x hx; rw [tower_step,tower_step]; exact GermD i (eventuallyEq_of_mem (opens.mem_nhds hx) hn)

lemma addJet {f g} (hf : C f) (hg : C g) (n : ℕ) : EqOn (tower (fun x => f x+g x) n)
    (fun x => tower f n x+tower g n x) side := by
  induction n with
  | zero => intro x hx;rfl
  | succ n hn => intro x hx; simp only [tower_step]; rw [GermD i (eventuallyEq_of_mem (opens.mem_nhds hx) hn)]; exact D_add (hf.limbs _) (hg.limbs _) hx i
lemma diffJet {f g} (hf : C f) (hg : C g) (n : ℕ) : EqOn (tower (fun x => f x-g x) n)
    (fun x => tower f n x-tower g n x) side := by
  induction n with
  | zero => intro x hx;rfl
  | succ n hn => intro x hx; simp only [tower_step]; rw [GermD i (eventuallyEq_of_mem (opens.mem_nhds hx) hn)]; exact D_sub (hf.limbs _) (hg.limbs _) hx i


def tangent (f : V → ℂ) (x : V) : ℂ := x.1 • D i f x-x.2 • D e f x
lemma C.tangentC {f} (hf : C f) : C (tangent f) := fun x hx =>
  ((contDiff_fst.contDiffAt).smul (hf.incl i x hx)).sub ((contDiff_snd.contDiffAt).smul (hf.incl e x hx))

lemma flow_one {f} (hf : C f) {x} (h : x∈side) : D i (tangent f) x=tangent (D i f) x-D e f x := by
  unfold tangent
  rw [D_sub (show C (fun x : V => x.1 • D i f x) from fun t ht => contDiff_fst.contDiffAt.smul (hf.incl _ t ht))
    (show C (fun x : V => x.2 • D e f x) from fun t ht => contDiff_snd.contDiffAt.smul (hf.incl _ t ht)) h]
  have hu : D i (fun x => x.1 • D i f x) x=x.1 • D i (D i f) x := by
    rw [D, fderiv_fun_smul differentiableAt_fst ((hf.incl _).able h), fderiv_fst]; simp [D,i]
  have hv : D i (fun x => x.2 • D e f x) x=x.2 • D i (D e f) x+D e f x := by
    rw [D, fderiv_fun_smul differentiableAt_snd ((hf.incl _).able h), fderiv_snd]; simp [D,i]
  rw [hu,hv,hf.swaps i e h]; abel

lemma vector {f} (_ : C f) {x} (_ : x∈side) : tangent f x = D (-x.2 • e+x.1 • i) f x := by
  unfold D tangent
  simp [D,sub_eq_add_neg, add_comm]

lemma flow_step {f} (hf : C f) (n : ℕ) {x} (h : x∈side) :
    tower (tangent f) (n+1) x = tangent (tower f (n+1)) x-(n+1) • D e (tower f n) x := by
  induction n generalizing x with
  | zero => rw [tower_step,tower_step f,root,root]; simpa using flow_one hf h
  | succ n hn =>
    rw [tower_step (tangent _),GermD i (eventuallyEq_of_mem (g := fun t => tangent (tower f (n+1)) t-(n+1) • D e (tower f n) t) (opens.mem_nhds h) (fun x h => hn h)),
      D_sub (hf.limbs (n+1)).tangentC (show C (fun x => (n+1) • D e (tower f n) x) from fun t ht => by
        simp_rw [← Nat.cast_smul_eq_nsmul ℝ]; exact contDiffAt_const.smul ((hf.limbs n).incl _ _ ht)) h]
    rw [flow_one (hf.limbs _) h]
    have hw : D i (fun y => (n+1) • D e (tower f n) y) x=(n+1) • D i (D e (tower f n)) x := by
      simp_rw [← Nat.cast_smul_eq_nsmul ℝ]
      rw [D, fderiv_fun_const_smul ((hf.limbs n).incl e |>.able h)]; rfl
    rw [hw,(hf.limbs _).swaps i e h,← tower_step f n, tower_step f (n+1),add_smul];simp;ring

lemma climbing {x : V} (h : x ∈ side) {f : V → ℂ} (hf : C f) : HasDerivAt (fun t : ℝ => f (t,x.2)) (D e f x) x.1 := by
  have he : HasDerivAt (fun u : ℝ => (u,x.2)) e x.1 := (hasDerivAt_id x.1).prodMk (hasDerivAt_const ..)
  exact (hf.able h).hasFDerivAt.comp_hasDerivAt x.1 he
lemma strafe {x : V} (h : x ∈ side) {f : V → ℂ} (hf : C f) : HasDerivAt (fun t : ℝ => f (x.1,t)) (D i f x) x.2 := by
  have he : HasDerivAt (fun u : ℝ => (x.1,u)) i x.2 := (hasDerivAt_const ..).prodMk (hasDerivAt_id x.2)
  exact (hf.able h).hasFDerivAt.comp_hasDerivAt x.2 he
lemma actual {f} (h : C f) {x : V} (hx : x∈side) (n : ℕ) : iteratedDeriv n (fun y => f (x.1,y)) x.2=tower f n x := by
  induction n generalizing f with
  | zero => simp
  | succ n hn =>
    rw [iteratedDeriv_succ', show deriv (fun y => f (x.1,y))=(fun y => D i f (x.1,y)) from funext fun y => (strafe (x := (x.1,y)) hx h).deriv,
      hn (h.incl _), tower_clock]
lemma lean {f} (h : C f) (n : ℕ) (H : ∀ t : ℝ, 0<t → tower f n (t,0)=0) (t : ℝ) (ht : 0<t) :
    D e (tower f n) (t,0)=0 := by
  have he := climbing (x := (t,0)) ht (h.limbs n)
  apply he.unique
  refine (hasDerivAt_const t 0).congr_of_eventuallyEq ?_
  exact Eventually.mono (p := fun i => 0< i) (Ioi_mem_nhds ht) $ fun i hi => H i hi

variable {I : Type*} (l r : I → I)
def law (S : I → V → ℂ) (a : I) (x : V) := S (l a) x+ S (r a) x+ tangent (S a) x
lemma regular {S} (hf : ∀ i, C (S i)) (j) : C (law l r S j) := ((hf _).add (hf _)).add (hf j).tangentC
lemma linear {S T} (hs : ∀ i, C (S i)) (hT : ∀ i, C (T i)) (j : I) {x : V} (hx : x∈side) :
    law l r S j x - law l r T j x = law l r (fun i x => S i x-T i x) j x := by
  unfold law tangent; rw [D_sub (hs _) (hT _) hx,D_sub (hs _) (hT _) hx]; simp only [smul_sub]; abel

theorem sure {F} (hc : ∀ j : I, C (F j))
    (h : ∀ j n t, 0<t → tower (law l r F j) n (t,0)=0)
    (hh : ∀ j t, 0<t → F j (t,0)=0) (n : ℕ) (t : ℝ) (ht : 0<t) (j : I) :
    tower (F j) n (t,0)=0 := by
  induction n using Nat.strong_induction_on generalizing t j with
  | h n ih =>
    cases n with
    | zero => exact hh j t ht
    | succ n =>
      let x := (t,(0:ℝ))
      have he : tower (law l r F j) n x=tower (F (l j)) n x+tower (F (r j)) n x+tower (tangent (F j)) n x := by
        unfold law; rw [addJet ((hc _).add (hc _)) (hc j).tangentC n (show x ∈ side from ht)]; dsimp only; rw [addJet (hc _) (hc _) n (show x∈side from ht)]
      have hv : tangent (tower (F j) n) x=t • tower (F j) (n+1) x := by simp [tangent,x,tower_step]
      have hy := h j n t ht
      change tower (law l r F j) n x=0 at hy
      rw [he, ih n n.lt_succ_self _ ht, ih n n.lt_succ_self _ ht,zero_add,zero_add] at hy
      cases n with
      | zero => exact (smul_eq_zero_iff_right ht.ne').mp (hv.symm.trans hy)
      | succ n =>
        rw [flow_step (hc j) n (show x∈side from ht), lean (hc j) n (fun t h => ih n (by omega) _ h _) t ht,smul_zero,sub_zero,hv] at hy
        exact (smul_eq_zero_iff_right ht.ne').mp hy
end YM.PDE
