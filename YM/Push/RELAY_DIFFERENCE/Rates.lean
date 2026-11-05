import YM.Next.EXTRACTION.Tails
import YM.Work.B06
import YM.Work.D01
import YM.Work.I04

/-!
# Cost of a quantitative Relay comparison

Use the **same order** on (mesh N, period p) as in the extraction.

Eventuality
on its fuse is not a mesh limit at every period.

Use `Slow` for a numeric or
coefficient budget bounded IN NORM by `exp (ε * C.S.scale N)` in this sense,
for each ε>0.

No sign constraint by default.

Some concrete costs proved here,
not an assumption of slow costs from a producer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Filter Extraction Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators

abbrev Cutoffs := ℕ × ℕ
variable {G : Gauge} {C : Family G} {f : Order} {d : ℕ}

lemma cutoff_grows (f : Order) : Tendsto (fun j : Cutoffs => j.1) f.fuse atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  rw [Order.fused]
  exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop b

lemma scale_grows (C : Family G) (f : Order) : Tendsto (fun j : Cutoffs => C.S.scale j.1) f.fuse atTop :=
  C.S.divergent.comp (cutoff_grows f)

def flight (C : Family G) (ε : ℝ) (j : Cutoffs) : ℝ := Real.exp (ε * C.S.scale j.1)

lemma cost_grows {ε : ℝ} (hε : 0 < ε) : Tendsto (flight C ε) f.fuse atTop :=
  Real.tendsto_exp_atTop.comp ((scale_grows _ _).const_mul_atTop hε)

lemma flight_lands {ε : ℝ} (hε : 0 < ε) : Tendsto (flight C (-ε)) f.fuse (𝓝 0) := by
  have hx : flight C (-ε) = fun j => (flight C ε j)⁻¹ := by
    funext j
    rw [flight, neg_mul, Real.exp_neg]; rfl
  rw [hx]
  exact tendsto_inv_atTop_zero.comp (cost_grows hε)

lemma flight_add (a b : ℝ) (j : Cutoffs) : flight C a j * flight C b j = flight C (a+b) j := by
  rw [flight, flight, flight, add_mul, Real.exp_add]

section Slow
variable {X Y : Type*} [Norm X] [Norm Y]

def Slow (C : Family G) (f : Order) {X : Type*} [Norm X] (w : Cutoffs → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ j in f.fuse, ‖w j‖ ≤ flight C ε j

variable {w : Cutoffs → X} {v : Cutoffs → Y}

lemma Slow.const (x : X) : Slow C f (fun _ => x) :=
  fun _ hε => (cost_grows hε).eventually_ge_atTop ‖x‖

lemma Slow.reduce (h : Slow C f w) (hq : ∀ᶠ i in f.fuse, ‖v i‖ ≤ ‖w i‖) : Slow C f v := by
  intro ε hε
  filter_upwards [hq,h _ hε] with i hi hv using hi.trans hv
end Slow

section SlowOp
variable {X : Type*} [SeminormedAddCommGroup X] {w v : Cutoffs → X}

lemma Slow.norm (h : Slow C f w) : Slow C f fun i => ‖w i‖ := by
  exact h.reduce (Eventually.of_forall fun _ => by simp)

private lemma sum_le_flight (ε : ℝ) (he : 0 < ε) : ∀ᶠ j in f.fuse,
    flight C (ε/2) j + flight C (ε/2) j ≤ flight C ε j := by
  filter_upwards [(cost_grows (C:=C) (half_pos he)).eventually_ge_atTop 2] with i hi
  have hx : flight C (ε/2) i * flight C (ε/2) i = flight C ε i := by rw [flight_add,add_halves]
  nlinarith only [hi,hx]

lemma Slow.add (h : Slow C f w) (H : Slow C f v) : Slow C f fun i => w i + v i := by
  intro ε hε
  filter_upwards [h _ (half_pos hε), H _ (half_pos hε), sum_le_flight ε hε] with i hi hv he using
    (norm_add_le ..).trans ((add_le_add hi hv).trans he)





lemma Slow.sum {ι : Type*} (s : Finset ι) (w : ι → Cutoffs → X) (h : ∀ i ∈ s, Slow C f (w i)) :
    Slow C f fun j => ∑ i∈s, w i j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (by simpa only [Finset.sum_empty] using Slow.const (C:=C) (f:=f) (0:X))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

private lemma norm_product_slow {Y Z : Type*} [SeminormedAddCommGroup Y] [Norm Z]
    (h : Slow C f w) {r : Cutoffs → Y} {p : Cutoffs → Z} (H : Slow C f r)
    (he : ∀ᶠ i in f.fuse, ‖p i‖ ≤ ‖w i‖ * ‖r i‖) : Slow C f p := by
  intro ε hε
  filter_upwards [h _ (half_pos hε), H _ (half_pos hε), he] with i hi hv hx
  apply hx.trans
  refine (mul_le_mul hi hv (norm_nonneg _) (show 0 ≤ flight _ _ _ from (Real.exp_pos _).le)).trans_eq ?_
  rw [flight_add,add_halves]

lemma Slow.smul {c : Cutoffs → ℂ} [NormedSpace ℂ X] (H : Slow C f c) (h : Slow C f w) :
    Slow C f fun i => c i • w i :=
  norm_product_slow H h (Eventually.of_forall fun _ => norm_smul_le ..)
end SlowOp

lemma Slow.mul {X : Type*} [NormedRing X] {c p : Cutoffs → X} (h : Slow C f c) (H : Slow C f p) :
    Slow C f fun i => c i * p i :=
  norm_product_slow h H (Eventually.of_forall fun _ => norm_mul_le ..)

lemma Slow.pow {c : Cutoffs → ℝ} (h : Slow C f c) (n : ℕ) : Slow C f fun i => c i ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using Slow.const (C:=C) (f:=f) (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul h

lemma Slow.below {w v : Cutoffs → ℝ} (h : Slow C f w) (he : ∀ᶠ i in f.fuse, 0 ≤ v i ∧ v i ≤ w i) :
    Slow C f v := by
  apply h.reduce
  filter_upwards [he] with i hi
  rw [Real.norm_of_nonneg hi.1, Real.norm_of_nonneg (hi.1.trans hi.2)]
  exact hi.2

lemma Slow.est {w : Cutoffs → ℝ} (h : Slow C f w) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in f.fuse, w i ≤ flight C ε i := by
  filter_upwards [h _ hε] with i hi using (Real.le_norm_self _).trans hi

/-- Expenditure times a rate of exponential decay in the UV: choose any
 strictly smaller decay exponent. -/
lemma Slow.sink {w : Cutoffs → ℝ} (h : Slow C f w) {a b : ℝ} (he : a < b) :
    ∀ᶠ i in f.fuse, w i * flight C (-b) i ≤ flight C (-a) i := by
  filter_upwards [h.est (sub_pos.mpr he)] with i hi
  refine (mul_le_mul_of_nonneg_right hi (show 0 ≤ flight C (-b) i from (Real.exp_pos _).le)).trans_eq ?_
  rw [flight_add]; ring_nf

lemma Slow.down {X : Type*} [Norm X] {w : Cutoffs → X} {g : Order} (h : Slow C f w)
    (H : YM.Next.Extract.Tails g f) : Slow C g w :=
  fun ε hε => Filter.Eventually.filter_mono H.fused (h ε hε)

lemma dollar_slow (w : Rowe C d) : dollar C f w ↔
    Slow C f (fun j => (C.factory d j.1 j.2).terminal.symm (w j)) := Iff.rfl

lemma columns_slow : Slow C f (fun j => (C.path.levels.params j.1).columns) := by
  let a := C.path.levels
  intro ε he
  filter_upwards [(cutoff_grows f).eventually (Work.D01.columnLogs_le a ε he),
    (cutoff_grows f).eventually (eventually_gt_atTop 0)] with j hi hj
  have hp : 0 < (a.params j.1).columns := zero_lt_one.trans_le (a.params _).columns_ge
  change ‖(a.params j.1).columns‖ ≤ _
  rw [Real.norm_of_nonneg hp.le, flight]
  apply (Real.log_le_iff_le_exp hp).mp
  change Work.D01.columnLogs a j.1 ≤ _ at hi
  refine le_trans ?_ hi
  generalize hh : j.1 = k at hj ⊢
  change 0 < k at hj
  cases k with
  | zero => simp at hj
  | succ m => rw [Work.D01.columnLogs_succ]; exact le_add_of_nonneg_left (Work.D01.columnLogs_nonneg a m)

/-- Hat powers (fixed powers subsequently by `Slow.pow`; not powers
chosen after seeing N). `Fits` not a premise about limits of observables. -/
lemma beta_slow (h : G.Simple) : Slow C f (fun j => C.path.levels.clock.hatBeta j.1) := by
  let a := C.path.levels
  intro ε he
  have hw := (Work.I04.hat_receipt a h).def he
  filter_upwards [(cutoff_grows f).eventually hw] with i hi
  have hp : 0 < a.clock.hatBeta i.1 := zero_lt_one.trans (a.fits.delayed _)
  change ‖Real.log (a.clock.hatBeta i.1)‖ ≤ _ at hi
  rw [Real.norm_of_nonneg (RG.Shoot.scale_nn a _)] at hi
  change ‖a.clock.hatBeta i.1‖ ≤ _
  rw [Real.norm_of_nonneg hp.le, flight]
  exact (Real.log_le_iff_le_exp hp).mp ((Real.le_norm_self _).trans hi)

lemma coupling_price (h : G.Simple) : Slow C f (fun j => (C.path.levels.clock.hatCoupling j.1)⁻¹) := by
  refine (beta_slow h).below (Eventually.of_forall fun i => ?_)
  let a := C.path.levels
  let x := a.clock.hatBeta i.1
  have hp : 1 < x := a.fits.delayed _
  change 0 ≤ (Real.sqrt x)⁻¹⁻¹ ∧ _ ≤ x
  change 0 ≤ (Real.sqrt x)⁻¹⁻¹ ∧ (Real.sqrt x)⁻¹⁻¹ ≤ x
  rw [inv_inv]
  constructor
  · exact Real.sqrt_nonneg x
  nlinarith only [hp, Real.sq_sqrt (zero_lt_one.trans hp).le]

lemma threshold_price (h : G.Simple) : Slow C f (fun j => (C.path.levels.budget j.1).threshold⁻¹) := by
  refine (coupling_price h).below (Eventually.of_forall fun i => ?_)
  let a := C.path.levels
  let x := a.clock.hatCoupling i.1
  have hp : 0 < x := inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans (a.fits.delayed _)))
  refine ⟨(inv_pos.mpr (a.budget _).threshold_pos).le, inv_anti₀ hp ?_⟩
  exact le_mul_of_one_le_right hp.le (Real.one_le_exp (sq_nonneg _))


end YM.Push.RelayDifference
