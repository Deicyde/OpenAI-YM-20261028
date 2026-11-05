import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Tariff
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.HeadSwitch
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Lens
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Borel
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Intake
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.TwoWindows
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Projection
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.FacePrice
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Ratios
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Common
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Marginal


/-!
# Payment for a grain in the interacting comparison

L¹ after pointwise estimates on the local prices of the pre-expansion.
Hard U links after transport in the *actual* chart can still be
tested e.g. by standardized Z thresholds even on large masks.

One payment interface: accept pointwise stamps against a finite menu
of anisotropic Gaussian tilts with energy/excursion estimates. Density
itself and any concomitant trials MUST pay by the same inequality.
Flexible for a history supplier (e.g. for the other, unrestarted chart);
our constructed variant downstream for restarted sectors just uses
`crop_pays`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Filter MeasureTheory Function
    Next.SectorChange Matrix Finset Next.SectorChange.Gaussian SectorTools.PhysicalGaussianSwitch
    AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussianLaws.Local
open scoped Topology BigOperators Classical ENNReal
namespace Tilt
variable {ι : Type} [DecidableEq ι] [Fintype ι]

def powerAt (w z : Vec ι) := ∑ i,w i * z i^2
omit [DecidableEq ι] in
private lemma power_cont (w : Vec ι) : Continuous (powerAt w) := by unfold powerAt; fun_prop
structure Cert (Q : Gaussian.Table ι) where
  funds : ℝ
  cov : Gaussian.Table ι
  paid : cov.PosDef
  bias : Vec ι
  w : Vec ι
  v : Vec ι
  gentle : 0≤w
  minor : 0≤v
  grant : ℝ
  earns : 0≤funds
  norm i : ∑ j,(w+v) j* |cov i j| ≤ 1/8

private lemma Gaussian_earn {C : Gaussian.Table ι} (hC : C.PosDef) {w : Vec ι}
    (h : 0 ≤ w) (H : ∀ i,∑ j,w j * |C i j| ≤ 1/8) :
    Integrable (fun z=>Real.exp (powerAt w z)) (Gaussian.cloud C) ∧ (∫ z,Real.exp (powerAt w z) ∂Gaussian.cloud C) ≤ Real.exp (2*∑ i,w i*C i i) := by
  let r : Unit→ Vec ι:= fun _=>w
  let B : Finset Unit:= {()}
  have hP : Primitives.GCC.Common.pool B C r:= by constructor; exact fun _ _ _=> h _; simp only [B,r,Finset.sum_singleton]; exact H
  obtain ⟨h1,h2⟩:= Primitives.GCC.Moment.amount (Primitives.GCC.Common.pool_enough C hC.posSemidef hP)
  simp_rw [Primitives.GCC.Common.common_due C hC.posSemidef, Primitives.GCC.Moment.sumCharge,B,r,Finset.sum_singleton] at h2
  unfold Primitives.GCC.Moment.sumCharge B at h1; simp_rw [Finset.sum_singleton] at h1
  obtain ⟨h,hx⟩:= pay_pull (Primitives.GCC.Common.paid_one C) (fun z=> Real.exp (powerAt w z)) (Real.continuous_exp.comp (power_cont w)).aestronglyMeasurable
  exact ⟨h.mp h1,hx.symm.trans_le h2⟩
variable {Q : Gaussian.Table ι} (C : Cert Q)

def capacity := C.funds * Real.exp (2*∑ i,(C.w+C.v) i*C.cov i i - C.grant)
private def promoted (Q P : Gaussian.Table ι) (m : Vec ι) (g : Vec ι→ℝ) (z : Vec ι) :=
    let δ:= -m+z; Gaussian.ratio P δ / Gaussian.ratio Q z*g δ

def rangeCost := { z : Vec ι| C.grant ≤ powerAt C.v z }
private def normCost := (rangeCost C).indicator (fun z => C.funds * Real.exp (powerAt C.w z))
/-- A real local density envelope, relative to the TRUE cloud. -/
def tariff := promoted Q C.cov C.bias (normCost C)


private lemma promoted_price (hQ : Q.PosDef) (g : Vec ι→ℝ) :
    (Integrable (promoted Q C.cov C.bias g) (cloud Q) ↔ Integrable g (cloud C.cov)) ∧
    (∫ z,promoted Q C.cov C.bias g z∂cloud Q)=∫ z,g z∂cloud C.cov:= by
  let p:= -C.bias
  let v z:=ratio C.cov z*g z
  let E : Vec ι≃ᵐVec ι:= MeasurableEquiv.addLeft p
  have hx : MeasurePreserving E volume volume:= measurePreserving_add_left ..
  have he z : (ENNReal.ofReal (ratio Q z)).toReal • promoted Q C.cov C.bias g z = v (p+z) := by
    unfold promoted; dsimp only; unfold v p; rw [ENNReal.toReal_ofReal (ratio_pos hQ _).le, smul_eq_mul]; field_simp [(ratio_pos hQ _).ne']
  have hn z : (ENNReal.ofReal (ratio C.cov z)).toReal • g z=v z:= by unfold v; rw [ENNReal.toReal_ofReal (ratio_pos C.paid _).le,smul_eq_mul]
  have hm (Q : Gaussian.Table ι) := (measurable_ratio Q).ennreal_ofReal
  have ht (Q : Gaussian.Table ι) : ∀ᵐ z : Vec ι ∂volume, ENNReal.ofReal (ratio Q z)<⊤:= Eventually.of_forall fun _=>ENNReal.ofReal_lt_top
  rw [Gaussian.cloud_formula hQ, Gaussian.cloud_formula C.paid,integral_withDensity_eq_integral_toReal_smul (hm Q) (ht Q), integral_withDensity_eq_integral_toReal_smul (hm _) (ht _), integrable_withDensity_iff_integrable_smul' (hm Q) (ht Q), integrable_withDensity_iff_integrable_smul' (hm _) (ht _)]
  simp_rw [he,hn]; exact ⟨hx.integrable_comp_emb (g:=v) E.measurableEmbedding, hx.integral_comp' v⟩
lemma tallied (hQ : Q.PosDef) : Integrable (tariff C) (cloud Q) ∧ (∫ z,tariff C z∂cloud Q) ≤ capacity C := by
  let a:=C.funds * Real.exp (-C.grant); let g z:= Real.exp (powerAt (C.w+C.v) z)
  have he z : 0≤ normCost C z ∧ normCost C z≤ a*g z := by
    have hb : 0≤C.funds:= C.earns; have hz : 0 ≤ a:= mul_nonneg hb (Real.exp_pos _).le
    unfold normCost; by_cases hs:z∈rangeCost C
    · rw [Set.indicator_of_mem hs]; refine ⟨mul_nonneg hb (Real.exp_pos _).le,?_⟩
      unfold a g; rw [mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hb
      apply Real.exp_monotone; have hx : powerAt (C.w+C.v) z=powerAt C.w z+powerAt C.v z:= by unfold powerAt; simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
      linarith only [hx,show C.grant ≤ powerAt C.v z from hs]
    rw [Set.indicator_of_notMem hs]; exact ⟨le_rfl,mul_nonneg hz (Real.exp_pos _).le⟩
  have hg:= Gaussian_earn C.paid (add_nonneg C.gentle C.minor) C.norm
  have hm : Measurable (normCost C):= (measurable_const.mul ((power_cont _).measurable.exp)).indicator (measurableSet_le measurable_const (power_cont _).measurable)
  have hi : Integrable (normCost C) (cloud C.cov):= (hg.1.const_mul a).mono' hm.aestronglyMeasurable (Eventually.of_forall fun z=> (Real.norm_of_nonneg (he z).1).trans_le (he z).2)
  have ht:= promoted_price C hQ (normCost C)
  refine ⟨ht.1.mpr hi,ht.2.trans_le ((integral_mono hi (hg.1.const_mul a) (fun i=>(he i).2)).trans ?_)⟩
  rw [integral_const_mul]; apply (mul_le_mul_of_nonneg_left hg.2 (show 0 ≤ a from mul_nonneg C.earns (Real.exp_pos _).le)).trans_eq; unfold a capacity; rw [mul_assoc,← Real.exp_add,sub_eq_add_neg,add_comm]
lemma tariff_nn (hQ : Q.PosDef) (z) : 0≤ tariff C z :=
  mul_nonneg (div_nonneg (ratio_pos C.paid _).le (ratio_pos hQ _).le) (Set.indicator_nonneg (fun _ _=> mul_nonneg C.earns (Real.exp_pos _).le) _)

/-- Each axis read is a subset of actual Sector z indices. Empty and
full tilts permitted as well. -/
structure Lift (Q : Gaussian.Table ι) where
  screen : Finset ι
  coin : Cert (Q.submatrix (fun i : ↥screen=>i.val) (fun i : ↥screen=>i.val))
def Notify (L : Lift Q) (z : Vec ι) := tariff L.coin fun i=>z i.val
def Plan (Q : Gaussian.Table ι) := List (Lift Q)

def banner (L : Plan Q) (z : Vec ι) := ((L : List (Lift Q)).map (fun i=>Notify i z)).sum
def total (L : Plan Q) := ((L : List (Lift Q)).map (fun i=>capacity i.coin)).sum
lemma certified_earn (hQ : Q.PosDef) (P : Plan Q) : Integrable (banner P) (cloud Q) ∧ (∫ z,banner P z∂cloud Q) ≤ total P := by
  suffices H : ∀ L : List (Lift Q), Integrable (banner L) (cloud Q) ∧ (∫ z,banner L z∂cloud Q) ≤ total L from H P
  intro L; induction L with
  | nil=> constructor
          · exact integrable_zero ..
          simp [banner,total]
  | cons i L ih =>
    let e : ↥(i.screen) → ι:= fun j=>j.val
    let C:= Q.submatrix e e
    have hp : C.PosDef := hQ.submatrix Subtype.val_injective
    have he := AnalyticBridge.Sharp.Projection.cloud_projection hQ e
    obtain ⟨h,H⟩:=tallied i.coin hp
    obtain ⟨h₁,h₂⟩:=pay_pull he (tariff i.coin) h.aestronglyMeasurable
    have ht : Integrable (Notify i) (cloud Q) := h₁.mpr h
    have hf z: banner (Q:=Q) (i::L) z=Notify i z+banner L z:= rfl
    constructor
    · rw [funext hf]; exact ht.add ih.1
    rw [funext hf, integral_add ht ih.1]; exact add_le_add (h₂.trans_le H) ih.2

section trim
variable (P : Plan Q)
omit [Fintype ι] in
lemma lamps_up (y) (hQ : Q.PosDef): 0≤ banner P y:= by
  suffices H:∀ p : List (Lift Q), 0≤ banner p y from H P
  intro L; induction L with
  | nil=> simp [banner]
  | cons i L ih=>exact add_nonneg (tariff_nn i.coin (hQ.submatrix Subtype.val_injective) _) ih
omit [Fintype ι] [DecidableEq ι] in
lemma fractional : 0≤ total P:= by
  suffices H:∀ p : List (Lift Q), 0≤ total p from H P
  intro L; induction L with
  | nil=> simp [total]
  | cons i L ih=>exact add_nonneg (mul_nonneg i.coin.earns (Real.exp_pos _).le) ih
end trim

-- supplier criterion for a whole-part tilt on a single chart
lemma crop_pays {Q : Gaussian.Table ι} (h : Q.PosDef) (w : Vec ι) (hw : ∀ i,0 ≤ w i) (a f : ℝ) (hf : 0≤f)
    (hh : ∀ i, ∑ j,w j*|Q i j|≤ 1/8) : ∃ D : Plan Q,
       (total D) = f*Real.exp (2*∑ i,w i * Q i i - a) ∧
       ∀ x, a≤powerAt w x → f ≤ banner D x := by
  let I:= (univ : Finset ι); let F (i:↥I) := i.val
  let b:= Q.submatrix F F; have ht := h.submatrix Subtype.val_injective (e:=F)
  let C:= w ∘ F
  have hk (f : ι→ℝ): ∑ i:↥I,f (F i)=∑ i,f i:= by exact prod_fee f
  have hx i : ∑ j,(0+C) j*|b i j| ≤ 1/8:= by rw [zero_add]; exact (hk (fun j=>w j*|Q (F i) j|)).trans_le (hh (F i))
  let V : Cert b:=⟨f,b,ht,0,0,C,le_rfl,fun i=>hw _,a,hf,hx⟩
  let p : Lift Q:= ⟨I,V⟩
  refine ⟨[p],?_,fun x hs=>?_⟩
  · change V.funds * Real.exp (2*∑ i,(V.w+V.v) i* b i i - a)+0=_
    rw [add_zero,show V.w+V.v=C from zero_add _]; rw [show (∑ i,C i*b i i)=_ from hk (fun i=>w i* Q i i)]
  let z:= x ∘ F
  change _ ≤ tariff V z + 0
  have hv : powerAt V.v z= powerAt w x:= hk (fun i=> w i*x i^2)
  rw [tariff,promoted]; dsimp only [V]; rw [neg_zero,zero_add, div_self (ratio_pos (C:=b) ht _).ne']
  have hP:z∈rangeCost V := hs.trans_eq hv.symm
  rw [one_mul,add_zero, normCost,Set.indicator_of_mem hP]
  simp [powerAt]
where
  prod_fee (f : ι→ℝ): ∑ i:↥(univ : Finset ι),f i.val=∑ i,f i:= Finset.sum_coe_sort ..
end Tilt
end YM.PhysicalNext.InteractingRank
