import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Glisten

/-!
# Tax includes Jacobian as well as normalized C price: rough on budget

Rank effects polynomial over AFTER-L clock for nonsingular **key** covariance
 change at either presentation. Actual log and exponential metrics in
 Density, all poles. Also from E6 `Mesoglea` style at anchor (via Pendant).
 NO charge from singular gauges to healthy. Use through j derivative mostly
 on polynomial stencil; complement with Mark retained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Prism
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {n : ℕ} {v d N Q K D w : ℝ}
section stress
variable [DecidableEq ι] [Fintype ι] {B C : E→ Matrix ι ι ℝ} {Y Y' : E→ Gaussian.Vec ι}
variable (hb : Holds B x Q n) (hc : Holds C x Q n) (Δ : EdgePay (C-B) n D 1 x)
    (hn : (Fintype.card ι:ℝ) ≤ N) (hd : 0≤D) (hq : 0≤ Q) (a : ι→ Site c)
    (hB : ∀ᶠ y in 𝓝 x, (B y).PosDef) (hC : ∀ᶠ y in 𝓝 x, (C y).PosDef) (ht : Moves x n Y Q) (hh : Moves x n Y' Q) (hy : Moves x n (Y-Y') D)
    (A : Anthem n)

include hb hn hq A hB
-- (det C0/C); C = B in THIS formula. Use (det B / det B0) for `jewels`.
def tally0 (n : ℕ) (N Q : ℝ) := (↑(n+1:ℕ):ℝ)*(1+N)^n*(n.factorial*(1+(freight n N Q Q +1))^n)
def reck (A : Anthem n) (N Q : ℝ) := ((n.factorial:ℝ)*A.gold)*(1+(1+tally0 n N Q)*n)^n
omit hB in
lemma wagers : Brush n (reck A N Q) 1 (fun y=> Real.log ((B y).det/(B x).det)) x := by
  let T y:= B y*(B x)⁻¹
  have he : T x=1:= Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb.sane.det_pos.ne')
  let C y:= T y-1
  have hp : C x=0 := by unfold C; rw [he,sub_self]
  let t:= freight n N Q Q; have hN := (Nat.cast_nonneg _).trans hn; have hz:= freight_pos hq hq n hN
  have hk: EdgePay T n t 1 x:= billed hn hq hq hb.liable (C:=fun _=> (B x)⁻¹) fun i j=> (Brush.certified zero_le_one _).climb (hb.back ..) le_rfl
  have hc i j:Brush n (t+1) 1 (fun x=> C x i j) x := (hk i j).separating ((Brush.certified zero_le_one _).climb (show ‖(1:Matrix ι ι ℝ) i j‖≤1 by 
    by_cases hi:i=j
    · subst j; simp
    simp [hi]) le_rfl)
  let b:=fun z=> (C z+1).det; have hx : b x=1:= by unfold b; rw [hp,zero_add,det_one]
  have ht: Brush n (tally0 n N Q) n b x := by
    refine (jewels hc hp (add_nonneg hz zero_le_one)).climb ?_ le_rfl
    unfold tally0; gcongr
  refine (ht.pine (show Brush n A.gold 1 Real.log (b x) from hx.symm ▸ A.log_ok)).trim |>.shimmy ?_
  refine Eventually.of_forall fun i=>?_ ; dsimp only; unfold b C; rw [sub_add_cancel]; apply congr_arg Real.log; rw [show (T i).det=(B i).det * ((B x)⁻¹).det from det_mul ..,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; ring

include a ht
def line (A : Anthem n) (N Q : ℝ) := reck A N Q+ (rail n N Q (banner Q N n) Q + rail n N Q (banner Q N n) Q)
def Bpower (A : Anthem n) (N Q : ℝ) := ((n.factorial:ℝ)*A.silver)*(1+(1+line A N Q))^n
lemma preliminary : Brush n (Bpower A N Q) 1 (fun y=> Density.replace (B y) (B x) (Y y-Y x) (Y x)) x := by
  let q y:= Real.log ((B y).det/(B x).det)/2; let T y:= force (B y) (Y y)/2; let f y:= -q y+(T x-T y)
  have hF := semi (wagers hb hn hq A)
  have hT : Brush n (rail n N Q (banner Q N n) Q) 1 T x:= semi (lineCost hn hq hq (banner_pos n hq ((Nat.cast_nonneg _).trans hn)) ht (broken a hb hn hq) ht)
  have hp : Brush n (line A N Q) 1 f x := hF.opposite.gathering (((Brush.certified zero_le_one _).climb hT.bound le_rfl).separating hT)
  have he : f x=0:= by unfold f q; rw [div_self hb.sane.det_pos.ne', Real.log_one]; ring
  have hf := (hp.pine (show Brush n A.silver 1 Real.exp (f x) from he.symm ▸ A.exp_ok)).trim; rw [mul_one] at hf
  refine hf.shimmy (hB.mono fun y hy=>?_); unfold Density.replace; dsimp only; rw [Density.chip_income _ _ hy hb.sane,← Real.exp_add,Density.spice,add_sub_cancel]
  unfold f q T; rw [show (B x).det/(B y).det=((B y).det/(B x).det)⁻¹ by simp,Real.log_inv]; ring_nf
include hc Δ hd hC hh hy

def tensor0 (A : Anthem n) (D N Q : ℝ) := (Bpower A N Q * (A.expE * plumage A N Q D))*(1+(1+1))^n

theorem proceeds0 (hg : gear D Q N n ≤ 1) (hj : sail D Q N n ≤ 1/2) (hp : plumage A N Q D ≤ 1) :
    Brush n (tensor0 A D N Q) 1 (fun y=> Density.replace (C y) (B x) (Y' y-Y x) (Y x) - Density.replace (B y) (B x) (Y y-Y x) (Y x)) x := by
  have hc' := angle hb hc Δ hn hd hq a (hB.and hC) ht hh hy A hg hj hp
  refine (((preliminary hb hn hq a hB ht A).paints hc').trim).shimmy (hB.mono fun y hy=>?_)
  dsimp only; rw [mul_sub,mul_one,mul_comm]
  rw [show Density.replace (C y) (B y) (Y' y-Y y) (Y y) * Density.replace (B y) (B x) (Y y-Y x) (Y x)=_ from ?_]
  · have hh := Density.replace_cocycle (C y) (B y) (B x) hy (Y' y-Y y) (Y y-Y x) (Y x); rw [add_sub_cancel,sub_add_sub_cancel] at hh; exact hh
end stress
end YM.PhysicalNext.Repeat.Prism
