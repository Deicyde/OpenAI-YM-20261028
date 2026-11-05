import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Det

/-!
# Through turn gains for density ledger. Keep δ^n buys under all jets.

Covariance rotations differ. Use Touch only on JOINT stencil and pay rank N
 of it, not full-period cardinal price. `slogan` supplies determinants under
 adequate scaled discrepancy. K positivity assumptions MATERIAL on each margin
before comparison. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Prism
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {n : ℕ} {v d N Q K D : ℝ}

section det
variable {B C : E→ Matrix ι ι ℝ} {Y : Matrix ι ι ℝ}
variable [Fintype ι]
lemma holding (N : ℝ) (h : (Fintype.card ι:ℝ) ≤ N) (hp : ∀ i j,|Y i j| ≤ v) (a : ι → Site c) (hv : 0≤v) :
    Price a a Y 0 (N*v) := by
  constructor <;> intro i <;> simp_rw [wt, zero_mul, Real.exp_zero,one_mul]
  all_goals refine (Finset.sum_le_sum (g:=fun _=>v) fun j _=> ?_).trans ?_
  · exact hp _ _
  · rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right h hv
  · exact hp j i
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right h hv

lemma matures (h : EdgePay B n v d x) (hn : (Fintype.card ι:ℝ) ≤ N) (a : ι→Site c) (hv : 0≤v) (hd : 0≤d) :
    Tablet n 0 (N*v) d B a a x := by
  refine ⟨le_rfl,hd,mul_nonneg ((Nat.cast_nonneg (Fintype.card _)).trans hn) hv, Matrix.of (fun _ _=>v),h,
    holding N hn (fun _ _=>?_) a hv⟩; exact (abs_of_nonneg hv).le

-- Stage with *both* K inverse explicit in leases so can transport score safely.
variable [DecidableEq ι]

def banner (v N : ℝ) (n : ℕ) := token n (N*v) (N*v)*(1+driftP n 1)^n
lemma banner_pos (n : ℕ) (hv : 0≤v) (hn : 0≤ N) : 0 ≤ banner v N n := by
  unfold banner; have h : 0≤ driftP n 1 := by unfold driftP; positivity
  unfold token; positivity
structure Holds (B : E→ Matrix ι ι ℝ) (x:E) (v:ℝ) (n:ℕ) : Prop where
  liable : EdgePay B n v 1 x
  back i j : ‖(B x)⁻¹ i j‖≤v
  sane : (B x).PosDef

lemma broken (a : ι→ Site c) (p : Holds B x v n) (hn : (Fintype.card ι:ℝ) ≤ N) (hv : 0≤v) : EdgePay (fun i => (B i)⁻¹) n (banner v N n) 1 x :=
  fun i j=> (((matures p.liable hn a hv zero_le_one).inverter (isUnit_iff_ne_zero.mpr p.sane.det_pos.ne') (holding _ hn p.back a hv) (mul_nonneg ((Nat.cast_nonneg _).trans hn) hv)).singular i j).trim

omit [DecidableEq ι] in
lemma sail_total {f : ι→E→ℝ} (h : (Fintype.card ι:ℝ) ≤ N) (hv : 0 ≤ v) (hd : 0 ≤ d) (hp : ∀ i,Brush n v d (f i) x) :
    Brush n (N*v) d (fun x=> ∑ i,f i x) x :=
  (Brush.spree _ _ _ hd (fun i (_:i∈Finset.univ)=> hp i)).climb (by rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right h hv) le_rfl

def freight (n : ℕ) (N f g:ℝ) := (N*(f*g))*(1+(1+1))^n
lemma freight_pos {f g:ℝ} (hf : 0≤f) (hg : 0≤g) (n : ℕ) (h : 0 ≤ N) : 0 ≤ freight n N f g := by unfold freight; positivity
set_option linter.unusedSectionVars false in
lemma billed (hn : (Fintype.card ι:ℝ) ≤ N) (hv : 0≤v) (hd : 0 ≤ d) (h : EdgePay B n v 1 x) (he : EdgePay C n d 1 x) :
    EdgePay (B*C) n (freight n N v d) 1 x := by
  intro i j
  change Brush _ _ _ (fun z => ∑ k,B z i k*C z k j) x -- via simp
  exact (sail_total hn (mul_nonneg hv hd) (add_nonneg zero_le_one zero_le_one) (fun k=> (h i k).paints (he k j))).trim

variable (hb : Holds B x Q n) (hc : Holds C x Q n) (Δ : EdgePay (C-B) n D 1 x)
    (hn : (Fintype.card ι:ℝ) ≤ N) (hd : 0≤D) (hq : 0≤ Q) (a : ι→ Site c)
-- C minus B; compute ratio B / C for chip on C compared to B0. signs.
def hoop (D Q N : ℝ) (n:ℕ):= freight n N D (banner Q N n)
def gear (D Q N : ℝ) (n:ℕ):= N^2 * hoop D Q N n
def sail (D Q N : ℝ) (n:ℕ):= N * gear D Q N n * (1+N)^n

include hc Δ hn hd hq a
lemma bays (hh : gear D Q N n ≤ 1) : Brush n (sail D Q N n) 1 (fun y=> (B y).det/(C y).det-1) x := by
  let V y:= (C y)⁻¹; let p:= (-(C-B))*V
  have hN:= (Nat.cast_nonneg _).trans hn; have hV:= banner_pos n hq hN; have hf:= billed hn hd hV
    (show EdgePay (-(C-B)) n D 1 x from fun i j=> (Δ i j).opposite) (broken a hc hn hq)
  refine ((dry_sail (B:=p) hf (freight_pos hd hV _ hN) hn hh).trim).shimmy ?_
  filter_upwards [(determinant (fun i j=> (hc.liable i j).smooth)).continuousAt.eventually_ne hc.sane.det_pos.ne'] with y hy
  have he : p y+1=B y*(C y)⁻¹ := by
    change (-(C y-B y))*(C y)⁻¹+_=_; rw [neg_sub,Matrix.sub_mul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy),sub_add_cancel]
  rw [he,det_mul, Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; ring

include hb

def revs (D Q N : ℝ) (n : ℕ) := freight n N (banner Q N n) (hoop D Q N n)
lemma inback : EdgePay (fun u=> (B u)⁻¹-(C u)⁻¹) n (revs D Q N n) 1 x := by
  let b u:= (B u)⁻¹; let c u:= (C u)⁻¹; have hN := (Nat.cast_nonneg _).trans hn
  have hk:= banner_pos n hq hN; have he : EdgePay (b*((C-B)*c)) n (revs D Q N n) 1 x := billed hn hk (freight_pos hd hk n hN) (broken a hb hn hq) (billed hn hd hk Δ (broken a hc hn hq))
  intro i j; refine (he i j).shimmy ?_
  filter_upwards [(determinant (fun i j=> (hb.liable i j).smooth)).continuousAt.eventually_ne hb.sane.det_pos.ne',
    (determinant (fun i j=> (hc.liable i j).smooth)).continuousAt.eventually_ne hc.sane.det_pos.ne'] with y hy ht
  change (b y-c y) i j=(b y*((C y-B y)*c y)) i j; rw [sub_mul,mul_sub,show C y*c y=1 from Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht),mul_one,← mul_assoc,show b y*B y=1 from Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy),one_mul]
end det
end YM.PhysicalNext.Repeat.Prism
