import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Depot
import YM.AnalyticNext.QUARTIC_MATCH.Local.Angles
import YM.Push.PRICE_COMPILER.Canonical


/-!
# Whole signed action on per-site kernels

Per-cell growth estimates on actual path-labelled formulas. Base grants
fund even nonlinear ell slots; can narrow R3/R4 but not throw away windings
when doing so.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Knot Pre.Centered
open Joint Estimate Estimate.Purse Estimate.Village Estimate.Logfee
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n l : Side} {ι : Type} [DecidableEq ι]
namespace Rotate

def total (p : Clip) (W : PathData G) (x : Site n) (a : Dir G n) := (∑ j : PlaqAxes, expense p W j x a) + atend W.cubic x a+atend W.quartic x a
lemma total_energy (p : Clip) (W : PathData G) (a : Dir G n) :
    ∑ x,total p W x a = quadratic p W (represent a)+uncut W.cubic (represent a)+uncut W.quartic (represent a) := by
  unfold total quadratic; rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Fintype.sum_prod_type]; rfl

def byStage (p : Clip) (W : PathData G) (x : Site n) (a : Dir G n) := Patch.average fun s : Signed => total p W (s⁻¹.act x) (shifts s 0 a)
lemma unroll (p : Clip) (W : PathData G) (a : Dir G n) : mainTerm p W (represent a)=∑ x, byStage p W x a := by
  have hh (s : Signed) := Equiv.sum_comp (s⁻¹.actEquiv (R:=Per n)).toEquiv (fun x => total p W x (shifts s 0 a))
  unfold mainTerm byStage Patch.average
  rw [← Finset.mul_sum,Finset.sum_comm]
  apply congr_arg; refine Finset.sum_congr rfl fun i _ => ?_; simp only [← rep_shifts]
  exact (hh i |>.trans (total_energy ..)).symm

section analytic
variable {p : Clip} {W : PathData G} {σ C Λ} (hW : W.Bounds p σ C Λ)
include hW
lemma total_rate (x : Site n) (a : Dir G n) : ContDiffAt ℝ ω (total p W x) a :=
    ((ContDiffAt.sum fun i _ => expense_rate hW i x a).add (atend_rate _ hW.width hW.three x a)).add (atend_rate _ hW.width hW.four x a)
lemma stage_rate (x : Site n) (a : Dir G n) : ContDiffAt ℝ ω (byStage p W x) a :=
    contDiffAt_const.mul (ContDiffAt.sum fun s _ => (total_rate hW (s⁻¹.act x) (shifts s 0 a)).comp a (shifts s (0:Site n)).contDiff.contDiffAt)
end analytic

def Curves (W : PathData G) (σ C : ℝ) : Prop := ∀ p, SumBudget (fun i => |(W.row p i).1| * Real.exp (σ*(W.row p i).2.length)) C

def Ink {k : ℕ} (A : ℕ→Atom G k) (σ R : ℝ) := SumBudget (fun i => (A i).budget σ) R

/-- Use the blank rule on output quartic. This separates widths independent
of base price, when exact cubic purchase is not available *at same width*. -/
inductive Access {k : ℕ} (A : ℕ→Atom G k) (l : Side) (n : ℕ) (η R : ℝ) : Prop
| clears {σ} : 0 < σ → 5*n*η≤ σ*l.val → Ink A σ R → Access A l n η R
| quiet : n < k → 0 ≤ R → Access A l n η R
| missing : (∀ i,(A i).coeff=0) → 0 ≤ R → Access A l n η R

lemma nonneg {α : Type*} {A : α→ℝ} {C} (h : SumBudget A C) : 0 ≤ C := (tsum_nonneg h.1).trans h.2.2
lemma Access.fee {k : ℕ} {A : ℕ→Atom G k} {n : ℕ} {η R} (h : Access A l n η R) : 0 ≤ R := by
  cases h with
  | clears _ _ ht => exact nonneg ht
  | quiet _ h | missing _ h => exact h

structure Led {G : Gauge} (W : PathData G) (l : Side) (n : ℕ) (η σ u C D : ℝ) : Prop where
  down : 0 < σ
  repute : 5*n*η ≤ σ*l.val
  curves : Curves W σ u
  three : Access W.cubic l n η C
  four : Access W.quartic l n η D

lemma outcast {k : ℕ} {A : ℕ→Atom G k} (h : ∀ i,(A i).coeff=0) : ∀ x : Site n, atend A x=fun _ => 0 := by
  intro x; funext y; simp only [atend,Cargo.effect,Atom.unmasked, Atom.poly, h,Pi.zero_apply,zero_mul,Finset.sum_const_zero,tsum_zero]

variable {k m : ℕ} {Q : Purse ι (Site n)} {d : ι→Dir G n} {η C σ u r U R3 R4 : ℝ}
section stipend
local notation "L" => (l.val:ℝ)
variable (h : Linkbill l Q d) (he : tollRate Q l η) (hp : 0 < η) (hb : Plaque.BendBill l Q d) {S : Finset ι} (hv : S.card ≤ m)
include h he hp hb hv

open Plaque in
def compensation (G : Gauge) (η : ℝ) (m : ℕ) := 2^m*(mailCharge G η m*allotted G η m)
omit h he hp hb hv in
lemma compensation_pos (G : Gauge) (η : ℝ) (m : ℕ) : 0<compensation G η m := mul_pos (by positivity) (mul_pos (Plaque.mailCharge_pos ..) (Plaque.allotted_pos ..))

open Plaque in
theorem appraisal {k : ℕ} {W : ℕ→Atom G k} (hR : Access W l m η C) (he' : Ink W u r) (hu : 0<u) :
    Q.Jets S d (atend W) 0 ((compensation G η m/L^2)^k*C) := by
  have hx : 0 ≤ C := hR.fee
  have hp' : 0 ≤ (compensation G η m/L^2)^k*C := by have ht := compensation_pos G η m; positivity
  cases hR with
  | quiet h' _ => exact (start_zero _ _ (hv.trans_lt h') hu he').mono hp'
  | clears hσ hq hh =>
    let M := allotted G η m
    convert! atom_budget W h he hp 0 (by simp) S m hv hq (M/L^2)
      (fun i T ht => collectBudget h he hp.le T m ((Finset.card_le_card ht).trans hv) hb i) (by unfold M; have h := allotted_pos G η m; positivity) hσ hh using 1
    unfold compensation M; ring
  | missing h' _ => unfold Jets; simp_rw [outcast h', empty_price]; exact Pays.zero hp'

omit h he hp hb hv in
lemma weighted_base {p : Clip} {W : PathData G} {τ u Λ} (hP : W.Bounds p τ u Λ) (η R : ℝ) (m : ℕ) :
    baseCash G m η p.direct R ≤ baseCash G m η 1 R :=
    add_le_add (mul_le_mul_of_nonneg_right (YM.Push.PriceCompiler.Canonical.direct_le_one hP.metric)
      (by have h := G.colorScale_pos; positivity)) le_rfl
open Plaque

def straight (G : Gauge) (η R : ℝ) (m : ℕ) := Fintype.card PlaqAxes * (baseCash G m η 1 R * allotted G η m ^ 2)
omit h he hp hb hv in
lemma straight_nonneg (G : Gauge) (η R : ℝ) (m : ℕ) : 0 ≤ straight G η R m := by
  have ht := G.colorScale_pos; unfold straight baseCash; positivity

variable {p : Clip} {W : PathData G} {τ K Λ R} (hP : W.Bounds p τ K Λ) (hx : Led W l m η σ R R3 R4)
include hP hx
theorem expenses : Q.Jets S d (total p W) 0 (straight G η R m / L^4 + compensation G η m^3/L^6 * R3 +
    compensation G η m^4/L^8 * R4) := by
  let D := compensation G η m/L^2
  let U := allotted G η m
  have hu : 0 ≤ U / L^2 := div_nonneg (allotted_pos ..).le (sq_nonneg _)
  have h3 : Q.Jets S d (atend W.cubic) 0 (D^3*R3) := appraisal h he hp hb hv hx.three hP.three hP.width
  have h4 : Q.Jets S d (atend W.quartic) 0 (D^4*R4) := appraisal h he hp hb hv hx.four hP.four hP.width
  have hm a : Q.Jets S d (expense p W a) 0 (baseCash G m η 1 R*(U / L^2)^2) :=
    (base_card hP h he hp _ (show ‖(0:Dir G n)‖<1 by simp) _ m hv hx.repute _
      (fun a T hu => collectBudget h he hp.le T m ((Finset.card_le_card hu).trans hv) hb a) a hu hx.down (hx.curves a)).mono
        (mul_le_mul_of_nonneg_right (weighted_base hP η R m) (sq_nonneg _))
  let f i (x : Dir G n) := ∑ j : PlaqAxes, expense p W j i x
  have hb' (i) : ContDiffAt ℝ ω (f i) 0 := ContDiffAt.sum fun j _ => expense_rate hP j i _
  have hG := Jets.allotted Finset.univ (expense p W (n:=n)) (fun i _ j => expense_rate hP i j _) (fun i _ => hm i)
  have he3 (i : Site n) := atend_rate _ hP.width hP.three i 0
  exact (Jets.adding (fun i => (hb' i).add (he3 i)) (fun i => atend_rate _ hP.width hP.four i 0) (Jets.adding hb' he3 hG h3) h4).mono
    (le_of_eq (by rw [Finset.sum_const]; unfold D U straight; rw [nsmul_eq_mul,Finset.card_univ]; ring))
end stipend

section all
local notation "L" => (l.val:ℝ)
def totalBill (G : Gauge) (η R : ℝ) (m : ℕ) := Real.exp (2*η)^m*(straight G η R m+compensation G η m^3+compensation G η m^4)
lemma totalBill_pos (G : Gauge) (η R : ℝ) (m : ℕ) : 0<totalBill G η R m := by
  apply mul_pos (pow_pos (Real.exp_pos _) _) (add_pos (add_pos_of_nonneg_of_pos (straight_nonneg ..) (pow_pos (compensation_pos ..) _)) (pow_pos (compensation_pos ..) _))

theorem tally (h : Linkbill l Q d) (he : tollRate Q l η) (hp : 0<η) (hb : Plaque.BendBill l Q d) {S : Finset ι} (hv : S.card ≤ m)
    {p : Clip} {W : PathData G} {τ K Λ R} (hP : W.Bounds p τ K Λ) (hx : Led W l m η σ R R3 R4) :
    Q.Jets S d (byStage p W) 0 (totalBill G η R m*(1+R3/L^2+R4/L^4)/L^4) := by
  let b := straight G η R m; let d' := compensation G η m; let C := b/L^4+d'^3/L^6*R3+d'^4/L^8*R4
  let f s (x : Site n) (a : Dir G n) := total p W (s⁻¹.act x) (shifts s 0 a)
  let a := Real.exp (2*η)
  have hu : 1≤a := Real.one_le_exp (by positivity)
  let v := a^m*C
  have hf (s : Signed) : Q.Jets S d (f s) 0 v := by
    have h := expenses (bonds s he hp.le h) (stays s he) hp (bending s he hp.le hb) hv hP hx
    refine ((restores s h).mono (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hu hv) h.1)).under fun i =>
      (congr_arg (‖·‖) (Depot.lin_rate (shifts s 0) _ d (total_rate hP (s⁻¹.act i) 0) S)).le
  have he' (s i) : ContDiffAt ℝ ω (f s i) 0 := (total_rate hP (s⁻¹.act i) (shifts s 0 (0:Dir G n))).comp _ (shifts s (0:Site n)).contDiff.contDiffAt
  let w := fun i z => ∑ s,f s i z
  have hw (i) : ContDiffAt ℝ ω (w i) 0 := ContDiffAt.sum fun s _ => he' s i
  apply (Jets.rate (Jets.allotted Finset.univ f (fun s _ i => he' s i) (fun s _ => hf s)) _ hw).mono
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, show |(Fintype.card Signed:ℝ)⁻¹| * (_*v)=v from by rw [abs_of_nonneg (by positivity)]; field_simp]
  let e := R3 / L^2; let f₁ := R4/L^4
  have hr : 0≤e := div_nonneg hx.three.fee (by positivity); have hR : 0≤f₁ := div_nonneg hx.four.fee (by positivity)
  have he := (straight_nonneg G η R m); have hp := compensation_pos G η m
  unfold v totalBill; rw [mul_assoc, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hu) _)
  change C ≤ (b+d'^3+d'^4)*(1+e+f₁) / L^4; rw [le_div_iff₀ (pow_pos (side_pos l) _)]
  rw [show C*L^4=b+d'^3*e+d'^4*f₁ by unfold C e f₁; field_simp]
  rw [add_mul, add_mul];
  refine add_le_add (add_le_add (le_mul_of_one_le_right he (by linarith)) (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hp.le _)))
    (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hp.le _)) <;> linarith
end all
end Rotate
end YM.AnalyticNext.QuarticMatch.Local
