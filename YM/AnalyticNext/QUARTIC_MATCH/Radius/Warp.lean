import YM.AnalyticNext.QUARTIC_MATCH.Radius.Slant

/-!
# Vertical physical coordinates throughout root rooms

Use the actual Hessian in the implicit work; this file fixes signs and
basis norms to avoid paying a period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model Work.F05
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Warp
variable {G : Gauge} {c f : Side} (S : StepData c f) (H : Forest S.ratio)
open Green (address wt)

abbrev ColorCost (G : Gauge) := max 1 (Fintype.card G.ColorIndex : ℝ)
lemma color_ge (G : Gauge) : 1≤ColorCost G := le_max_left ..
abbrev code (G : Gauge) : AxisChart G H ≃L[ℝ] (Key H G→ℝ) :=
    (countingBasis H G).equivFun.toContinuousLinearEquiv
lemma reveal (x : AxisChart G H) : x= ∑ i : Key H G, (code S H G x i) • frame H i := by
  simp_rw [← countingBasis_apply]; exact ((countingBasis H G).sum_equivFun x).symm
lemma record (x : AxisChart G H) (i : Key H G) : code S H G x i=x i.1 i.2 := by
  let A : AxisChart G H →L[ℝ] ℝ := (PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) i.2).comp (ContinuousLinearMap.proj i.1)
  have hv j : A (frame H j)= if i=j then (1:ℝ) else 0 := by
    change ((Pi.single j.1 _ : AxisChart G H) i.1) i.2=_
    by_cases h : i.1=j.1
    · rw [h,Pi.single_eq_same]
      simp only [Prod.ext_iff,h,true_and]; by_cases hi : i.2=j.2 <;> simp [hi,EuclideanSpace.basisFun_apply]
    rw [Pi.single_eq_of_ne h,if_neg (by rintro rfl; exact h rfl)]; rfl
  change code S H G x i=A x
  conv_rhs => rw [reveal S H x,map_sum]
  simp [hv]

lemma prints (x : AxisChart G H) (j : H.Free) : ‖x j‖ ≤ ∑ i : G.ColorIndex,‖code S H G x (j,i)‖ := by
  let P := EuclideanSpace.basisFun G.ColorIndex ℝ
  have hh i : P.repr (x j) i=code S H G x (j,i) := by rw [record]; rfl
  have hv : x j=∑ i : G.ColorIndex,(code S H G x (j,i)) • P i := by simp_rw [← hh]; exact (P.sum_repr (x j)).symm
  conv_lhs => rw [hv]
  exact (norm_sum_le ..).trans_eq (by simp [norm_smul])

lemma wallet (i : Site f) (t : ℝ) (x : AxisChart G H) {C : ℝ} (hx : 0≤C) (he : Amount t (address H) i (code S H G x) C) :
    charge S H G t i x (ColorCost G*C) := by
  intro j; refine (prints S H x j).trans ((Finset.sum_le_sum (g:=fun _=> C*wt t j.val.1 i) (fun y _ => he (j,y))).trans ?_)
  rw [Finset.sum_const,nsmul_eq_mul, Finset.card_univ];
  exact (mul_le_mul_of_nonneg_right (le_max_right ..) (mul_nonneg hx (Green.wt_pos ..).le)).trans_eq (mul_assoc ..).symm

variable (p : Clip) (R : PathData G) (θ : S.Choices)
def GArray (x : ChartVars H G) := fun i : Key H G => skew S H p R θ i x
def bend (x : ChartVars H G) := Precision.hessian H θ p R x.1 x.2
variable {F : Site f→ChartVars H G→ℝ} {Q : Purchase} (hp : Q.Applies H p R F) {x : ChartVars H G} (he : ‖x‖<Q.width)
include hp he


lemma reads {i : Key H G} : GArray S H p R θ x i=fderiv ℝ (tested H θ p R x.1) x.2 (frame H i) := by
  let f := uncurry (tested H θ p R)
  have hf := Purchase.works S H p R hp he θ
  let L := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G H); let V (v : AxisChart G H) := (x.1,v)
  have hV : HasFDerivAt V L x.2 := (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  rw [show fderiv ℝ _ x.2= _ from (show HasFDerivAt (tested H θ p R x.1) (fderiv ℝ f x ∘L L) x.2 from
    ((show HasFDerivAt f (fderiv ℝ f x) (V x.2) from (hf.differentiableAt (by simp)).hasFDerivAt).comp x.2 hV)).fderiv]; rfl
lemma axisPair (i j : Key H G) : bend S H p R θ x i j = D (slew S H i) (skew S H p R θ j) x := by
  let w (b : AxisChart G H) := (x.1,b)
  let f x := GArray S H p R θ x j
  have hw : HasFDerivAt w (ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G H)) x.2 := (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have hf : DifferentiableAt ℝ f (w x.2) := ((Purchase.pitch S H p R hp θ he j).differentiableAt (by simp))
  let F := tested H θ p R x.1
  have ht : ContDiffAt ℝ ω F x.2 := Work.F05.hold_jet (Purchase.works S H p R hp he θ)
  have hv : (f ∘ w)=ᶠ[𝓝 x.2] fun b => D (frame H j) F b := (hw.continuousAt.tendsto.eventually
    (nearInside (show ‖w x.2‖ < Q.width from he))).mono fun q h=> reads S H p R θ hp h
  rw [show skew S H p R θ j=f from rfl]
  change iteratedFDeriv ℝ 2 F x.2 ![_,_] = _
  rw [D2_jet]; change D (frame H i) (fderiv ℝ F) x.2 _= _
  rw [← D_left ((ht.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp))]
  change D (frame H i) (fun y=> D (frame H j) F y) x.2 = _; rw [← show D (frame H i) (f ∘ w) x.2= _ from GermD _ hv]
  rw [D, (hf.hasFDerivAt.comp _ hw).fderiv]; rfl
lemma ambient : IsHermitian (bend S H p R θ x) := by
  let V : AxisChart G H→ℝ := tested H θ p R x.1
  have hv : ContDiffAt ℝ ω V x.2 := Work.F05.hold_jet (Purchase.works S H p R hp he θ)
  ext i j; rw [conjTranspose_apply,star_trivial]; change iteratedFDeriv ℝ 2 V x.2 ![_,_] = iteratedFDeriv ℝ 2 V x.2 ![_,_]
  simp_rw [D2_jet]; exact hv.isSymmSndFDerivAt_of_omega ..

lemma payout (v : AxisChart G H) (i : Key H G) : D (0,v) (skew S H p R θ i) x = ((bend S H p R θ x)*ᵥ code S H G v) i := by
  have hh : (0,v)=∑ j, code S H G v j • slew S H j := by
    apply Prod.ext; simp [Prod.fst_sum, slew]
    rw [Prod.snd_sum]; exact reveal S H v
  rw [D, hh,map_sum]; unfold mulVec dotProduct
  apply Finset.sum_congr rfl; intro j _; rw [map_smul]
  have hs : bend S H p R θ x i j=bend S H p R θ x j i := by simpa only [star_trivial] using ((ambient S H p R θ hp he).apply i j).symm
  exact (mul_comm ..).trans (congr_arg (·*code S H G v j) ((hs.trans (axisPair S H p R θ hp he j i)).symm))

end Warp
end YM.AnalyticNext.QuarticMatch.Radius
