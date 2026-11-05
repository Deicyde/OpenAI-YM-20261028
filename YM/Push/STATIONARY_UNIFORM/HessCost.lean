import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Push.STATIONARY_UNIFORM.LCharge
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15
import YM.Work.B04
import YM.Work.F01
import YM.Work.F02
import YM.Work.F03


/-!
# Real Hessian at zero from symbolic free pricing

Don't even need Floor or Sworn for a gap: use the *actual* direct coefficient
and path sum properties, Hessian is literally a price of all the curls under
rotations and these same linearized paths, plus a noise price of all the
rooted predictor cochains. Then a symbolic free shell estimate (F01 port and
our quantitative L refinement) gives a gap directly here in actual counting.
No Fourier inversion at nonzero modes only. Includes global holonomies on each
tree. This part doesn't use capacities of PathData numerically (later inverse
and uniform neighborhood estimates certainly do).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid
open Work.F03 Work.F01
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} (B : Forest S.ratio) (t : S.Choices)
variable {μ C D Z Λ : ℝ} {p : Clip} {R : PathData G}

/-- Formula for flat Hessian without representing it by `Bed`. Charges signed
average in ordinary physical color units. -/
def wheel (p : Clip) (R : PathData G) (z : In G f) :=
  ∑ x : Face (Per f), (p.direct * ‖faceCurl x z‖^2 + ‖ellLine R x z‖^2)

def flatPrice (S : StepData c f) (p : Clip) (R : PathData G) (z : Logs G c f) : ℝ :=
  (Patch.average fun s => wheel p R (pulled z.2 s)) +
    S.kernel.penalty * (∑ b, ‖residual S z b‖^2)

lemma gear_limit (hb : R.Bounds p μ C Λ) (z : In G f) :
    Tendsto (fun t : ℝ => quadratic p R (represent (t • z))/t^2) (𝓝[≠] 0) (𝓝 (wheel p R z / 2)) := by
  unfold quadratic wheel; simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun x _ => ?_
  -- actual path row: variant of F03.quadratic_limit independent of Bed
  have he := ((ell_limit R hb x z).norm.pow 2).div_const 2
  have hp := (price_limit (G:=G) (V:=fun t : ℝ => faceValue (represent (t • z)) x)
    (by rw [zero_smul]; exact stroll_zero ..) (face_deriv x z)).const_mul p.direct
  rw [add_div,mul_div_assoc]
  refine (hp.add he).congr' (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_smul,mul_pow, Real.norm_eq_abs,sq_abs, inv_pow]; ring

lemma wheel_limit (hb : R.Bounds p μ C Λ) (h : S.patch.Branches S.kernel G) (z : Logs G c f) :
    Tendsto (fun u : ℝ => flat S t p R (u • z)/u^2) (𝓝[≠] 0) (𝓝 (flatPrice S p R z/2)) := by
  have hs (s : Signed) := ((gear_limit hb (pulled z.2 s)).add
    (uncut_limit (k:=0) (pulled z.2 s) R.cubic hb.width hb.three)).add
    (uncut_limit (k:=1) (pulled z.2 s) R.quartic hb.width hb.four)
  simp only [add_zero] at hs
  have hA : Tendsto (fun u : ℝ => mainTerm p R (represent (u • z.2))/u^2) (𝓝[≠] 0)
      (𝓝 ((Patch.average fun s => wheel p R (pulled z.2 s))/2)) := by
    unfold mainTerm Patch.average
    simp_rw [mul_div_assoc,Finset.sum_div,add_div,represent_pulled]
    exact (tendsto_finsetSum _ fun s _ => hs s).const_mul _
  have hN := noise_limit h t z
  simp_rw [real_inner_self_eq_norm_sq] at hN
  simp_rw [flat, flatPrice,add_div]; exact hA.add hN

lemma price_identity (hb : R.Bounds p μ C Λ) (h : S.patch.Branches S.kernel G) :
    let F := uncurry (tested B t p R)
    ContDiffAt ℝ ω F 0 ∧ F 0=0 ∧ fderiv ℝ F 0=0 ∧
      ∀ y, iteratedFDeriv ℝ 2 F 0 ![y,y]=flatPrice S p R (y.1,stretch (S:=S) B y) := by
  let f := flat S t p R; let T := uncurry (tested B t p R); let g := inclusion B (G:=G)
  have hA := flat_smooth h t (Work.F02.answer G p R _ _ _ hb)
  have hm : ContDiffAt ℝ 2 f 0 := hA.of_le le_top
  have hd y : ContDiffAt ℝ 2 (fun s : ℝ => f (s • y)) 0 :=
    (show ContDiffAt ℝ 2 f ((0:ℝ) • y) by rwa [zero_smul]).comp (f:=fun s : ℝ => s • y) 0 (contDiffAt_id.smul contDiffAt_const)
  have hq y := Work.F03.value_slope_of_sq_limit (hd y).continuousAt (wheel_limit t hb h y)
  have hf0 : f 0=0 := by simpa only [zero_smul] using (hq 0).1
  have hD : fderiv ℝ f 0=0 := ContinuousLinearMap.ext fun y => (Push.side f (hA.differentiableAt (by simp)) y).unique (hq y).2
  have hp (y : Logs G c _) : iteratedFDeriv ℝ 2 f 0 ![y,y]=flatPrice S p R y := by
    have H := tendsto_nhds_unique (taylor_limit_two (hd y) (hq y).1 (hq y).2.deriv) (wheel_limit t hb h y)
    rw [line_second hm hD] at H; linarith
  have hs : T =ᶠ[𝓝 0] f ∘ g := from_flat B t R p
  have hg : ContDiffAt ℝ ω g 0 := inclusion_smooth B
  have h0 : g 0=0 := inclusion_zero B
  have he : ContDiffAt ℝ ω (f ∘ g) 0 := (h0.symm ▸ (show ContDiffAt ℝ ω f 0 from hA)).comp 0 hg
  have ht := hessian_comp h0 hm (hg.of_le le_top) hD
  refine ⟨he.congr_of_eventuallyEq hs, hs.eq_of_nhds.trans (by rw [Function.comp_apply,h0,hf0]), hs.fderiv_eq.trans ht.1,fun y => ?_⟩
  change iteratedFDeriv ℝ 2 T _ _ = _
  rw [(hs.iteratedFDeriv ℝ 2).eq_of_nhds, ht.2,hp, show fderiv ℝ g 0 y=_ from inclusion_deriv B y]

def spoke (p : Clip) := (Fintype.card Signed:ℝ)⁻¹*p.direct
lemma spoke_pos (p : Clip) : 0 < spoke p := mul_pos (by positivity) p.quadratic_pos

lemma wallet (v : AxisChart G B) (hb : R.Bounds p μ C Λ) (h : S.patch.Branches S.kernel G) :
    let z := stretch (S:=S) B (0,v)
    spoke p * (∑ i, ‖dColor G f 1 z i‖^2)+ S.kernel.penalty * (∑ i, ‖bills S z i‖^2) ≤
      iteratedFDeriv ℝ 2 (tested B t p R 0) 0 ![v,v] := by
  let z := stretch (S:=S) B (0,v); let b : ChartVars B G := (0,v)
  dsimp only
  rw [vertical_hessian B t (h:=fun t => (price_identity B t hb h).1) v, (price_identity B t hb h).2.2.2]
  unfold flatPrice; dsimp only
  have hx : residual S (0,z)=-bills S z := zero_sub _
  change _ ≤ _ + S.kernel.penalty * ∑ i, ‖residual S (0,z) i‖^2
  rw [hx]; simp_rw [Pi.neg_apply,norm_neg]; gcongr ?_ + _
  have hw (z : In G f) : 0 ≤ wheel p R z := by unfold wheel; have := p.quadratic_pos; positivity
  unfold Patch.average spoke
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans _ (Finset.single_le_sum (f:=fun s => wheel p R (pulled z s)) (fun i _ => hw _) (Finset.mem_univ 1))
  have hp : pulled z 1=z := by
    funext i; rcases i with ⟨i,u⟩; obtain ⟨k,rfl⟩ := axisEquiv.surjective u
    simp [pulled,Step.used,posDir,show axisEquiv.symm (coord k)=k from axisEquiv.symm_apply_apply _,affine]
  rw [hp]; change p.direct*(∑ i, ‖dColor G f 1 z i‖^2) ≤ _
  rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (a:=p.direct*‖faceCurl i z‖^2) (sq_nonneg _)

def zeroGap (P : Patch) (Q : KernelChoices) (p : Clip) (C D : ℝ) :=
  min (spoke p) Q.penalty / (1+curlFactor P.L (box (macroR P)) (linkCost Q C D P.L) + probeFactor P.L)
lemma zeroGap_pos (P : Patch) (Q : KernelChoices) (p : Clip) (C D : ℝ) : 0 < zeroGap P Q p C D := by
  unfold zeroGap; apply div_pos (lt_min (spoke_pos _) Q.penalty_pos); unfold curlFactor probeFactor; positivity

lemma symbolic_gap (hb : R.Bounds p μ C Λ) (h : Larger (G:=G) S) (hg : Harness G S.patch.J S.kernel Z D) :
    PriceGap B p R (zeroGap S.patch S.kernel p Z D) := by
  intro t v
  let x := stretch (S:=S) B (0,v); let X := box (macroR S.patch)
  let e := linkCost S.kernel Z D S.patch.L
  have he := (linkCost_pos S.kernel hg.1 hg.2.1 S.patch.L).le
  let Y : Bond f → ℝ := fun i => ‖collect G x i‖
  have hh (i) (hi : i∈B.trunks) : collect G x i=0 := by unfold x; rw [collect_vertical, dif_pos hi]
  have hs := sum_estimate S.ratio X (fun i => ‖dColor G f 1 x i‖) (fun i => ‖bills S x i‖)
    Y e (fun i => norm_nonneg _) (fun i => link_bound S h.1 B t x hh _ he i
    (fun U hU hk => hg.2.2 S rfl rfl h.2.1 B U hU i t hk))
  let a := zeroGap S.patch S.kernel p Z D
  have ha := zeroGap_pos S.patch S.kernel p Z D
  have ht : (∑ i : B.Free, ‖v i‖^2) ≤ ∑ i, Y i ^2 := by
    have he (i : B.Free) : Y i.val = ‖v i‖ := by unfold Y x; rw [collect_vertical,dif_neg i.property]
    simp_rw [← he]
    calc
      _ = ∑ i∈Finset.univ.filter (fun i => i∉B.trunks), Y i ^2 := by
        rw [Finset.sum_subtype _ (p:= fun i => i ∉ B.trunks) (by simp)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  apply (mul_le_mul_of_nonneg_left (ht.trans hs) ha.le).trans; apply le_trans _ (wallet B t v hb h.1)
  rw [mul_add, ← mul_assoc,← mul_assoc]
  have hu : 0 ≤ curlFactor S.patch.L X e := by unfold curlFactor; positivity
  have hv : 0 ≤ probeFactor S.patch.L := by unfold probeFactor; positivity
  have hZ : a*(1+curlFactor S.patch.L X e+probeFactor S.patch.L)=min (spoke p) S.kernel.penalty :=
    div_mul_cancel₀ _ (by positivity)
  have h₁ := mul_le_mul_of_nonneg_left (show curlFactor S.patch.L X e ≤ 1+curlFactor S.patch.L X e+probeFactor S.patch.L by linarith) ha.le
  have h₂ := mul_le_mul_of_nonneg_left (show probeFactor S.patch.L ≤ 1+curlFactor S.patch.L X e+probeFactor S.patch.L by linarith) ha.le
  exact add_le_add (mul_le_mul_of_nonneg_right ((h₁.trans_eq hZ).trans (min_le_left ..)) (Finset.sum_nonneg fun i _ => sq_nonneg _))
    (mul_le_mul_of_nonneg_right ((h₂.trans_eq hZ).trans (min_le_right ..)) (Finset.sum_nonneg fun i _ => sq_nonneg _))
end YM.Push.Uniform
