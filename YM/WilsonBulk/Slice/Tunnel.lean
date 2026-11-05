import YM.WilsonBulk.Slice.Linear

/-!
# Jacobian-fiber theorem for exact Wick expansion

Purely algebraic (material derivative induction on same expansion clock,
including arbitrary coordinates for spectators and corner gauges). *Through
every fixed order*. Used to obtain invariance under local changes of tree/gauge
in finite periods. Doesn't assert result of moving any window in actual measure.
General : centered quadratic forms given by real symmetric matrices, covariances
G,H separately; no positivity needed beyond regular-gap consumer. Include
relative jac leading normal. External covariance via separate pull statement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical BigOperators
open Function Matrix Finset PowerSeries
variable {α β X ι : Type} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq α]
variable {G H B J V : Matrix α α ℝ} {v T : α → StageD α ι}

-- affine change leading map linear on chamber incl no spectators. Given B,J with T0 regular
-- hzero cancellation for `tide`
abbrev seedQ (ι : Type) (B : Matrix α α ℝ) : StageD α ι:= forceQ B privateName
def contrast (B J : Matrix α α ℝ) (T : α→ StageD α ι) : StageD α ι:= seedQ ι B-switch T (seedQ ι J)
-- expect positivity; abs_det/leading absolute, but keep sign normalization as formal identity (both negative allowed)
def levy (V : Matrix α α ℝ) (T : α → StageD α ι) := (V.det)⁻¹ • (gaugeHess T).det
def customs (B J V : Matrix α α ℝ) (T : α → StageD α ι) (f : StageD α ι) := switch T f * tide (contrast B J T) * levy V T

section
omit [Fintype ι]
-- Leading is steps 1

def Starting (T : α→StageD α ι) (V : Matrix α α ℝ) := ∀ i, Steps 1 (T i) (quill V privateName i)
omit [DecidableEq α] in
lemma steps_initial {A : Type} [CommRing A] (p q : PowerSeries A) : Steps 1 p q ↔ constantCoeff p=constantCoeff q := by simp [Steps]
omit [DecidableEq α] in
lemma Starting.tape (hT : Starting T V) (p : StageD α ι) : Steps 1 (switch T p) (switch (quill V privateName) p) := by
  refine code_agree constantCoeff_X constantCoeff_X ?_ Steps.self Steps.self; intro i; cases i
  · exact hT _
  exact Steps.self
omit [DecidableEq α] in
lemma contrast_empty (hT : Starting T V) (he : V.transpose*J*V=B) : constantCoeff (contrast B J T)=0 := by
  have hh : switch (quill V privateName : α→StageD α ι) (seedQ ι J) = seedQ ι B := by
    rw [seedQ,forceQ_map]; simp_rw [switch_to]; rw [force_transfer, he]
  rw [contrast,map_sub,(steps_initial ..|>.mp (hT.tape _)),hh,sub_self]
lemma Starting.jac (hT : Starting T V) : constantCoeff (gaugeHess T).det = MvPolynomial.C V.det := by
  rw [RingHom.map_det,RingHom.map_det]; congr 1
  ext i j : 1
  change constantCoeff (inflow j (T i))=_
  have hv : Steps 1 (inflow j (T i)) (inflow j (quill V privateName i)) := parallel_agree (hT i) _
  rw [(steps_initial ..).mp hv, inflow_quill, PowerSeries.algebraMap_apply,constantCoeff_C]; rfl
lemma Starting.cover (hT : Starting T V) (hj : V.det≠0) : IsUnit (gaugeHess T).det := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr; rw [hT.jac]; exact IsUnit.map _ (isUnit_iff_ne_zero.mpr hj)
lemma levy_const (hT : Starting T V) (hv : V.det≠0) : constantCoeff (levy V T)=1 := by
  rw [levy,constantCoeff_smul,hT.jac,Algebra.smul_def, ← MvPolynomial.C_eq_algebraMap, ← _root_.map_mul, inv_mul_cancel₀ hv,map_one]
lemma landing (f : StageD α ι) (B J : Matrix α α ℝ) (hT : Starting T V) (hj : V.det≠0) : constantCoeff (customs B J V T f)= constantCoeff (switch (quill V privateName) f) := by simp only [customs,map_mul, levy_const hT hj, tide_const, mul_one]; exact (steps_initial ..).mp (hT.tape f)
end
-- material departure from Gaussian
lemma parting (B J V : Matrix α α ℝ) (v T : α→StageD α ι) (h : ∀ i, flow v (T i)=0) (hc : constantCoeff (contrast B J T)=0) (f : StageD α ι) :
    let g:= customs B J V T f
    clockD _ g= customs B J V T (clockD _ f) + ∑ i,(inflow i (v i*g)- inflow i (seedQ ι B)*(v i*g)) := by
  intro g
  set a:=switch T f; set b:=tide (contrast B J T); set w:=levy V T; set s:= switch T (clockD _ f)
  let Q := seedQ ι B
  have he : (flow v) b=b*(0-∑ i,v i*inflow i Q) := by
    have hu (B : Matrix α α ℝ) : clockD _ (seedQ ι B)=0:= by rw [seedQ,force_top, clock_C]
    rw [flow_tide hc,contrast, map_sub,flow_switch v T h,hu,map_zero,flow_apply,hu]; rw [sub_zero]
    rfl
  have hw : flow v w = w* ∑ i,inflow i (v i) := by unfold w levy; rw [Derivation.map_smul,flow_det v T h,smul_mul_assoc]
  have hG : g=a*b*w := rfl
  have ha : flow v g= s*b*w +∑ i,(g*inflow i (v i)- g* (v i *inflow i Q)) := by
    rw [hG,D_leib,D_leib, hw,he, show flow v a=s from flow_switch v T h f, sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
    ring
  rw [flow_apply,sub_eq_iff_eq_add] at ha; rw [ha]; change s*b*w+_+_=s*b*w+_
  rw [add_assoc,← sum_add_distrib]; refine congr_arg (s*b*w+·) (sum_congr rfl fun i _=>?_); rw [D_leib]; dsimp only [Q]; ring
-- supply covariance relations precisely
lemma warp (f : StageD α ι) (hs : G.IsSymm) (hb : B.IsSymm) (hp : B*G=1) (hT : Starting T V) (hv : V.det≠0)
    (hj : V.transpose*J*V=B) (he : V*G*V.transpose=H) :
    bags ι G (customs B J V T f)= bags ι H f := by
  let v:= breeze T
  have hw (f : StageD α ι) : bags ι G (clockD _ (customs B J V T f)) = bags ι G (customs B J V T (clockD _ f)) := by
    rw [parting B J V v T (breeze_fits T (hT.cover hv)) (contrast_empty hT hj) f]; simp only [map_sum,map_add,IBP G hs hb hp,sum_const_zero,add_zero, seedQ]
  ext1 i; induction i generalizing f with
  | zero=>
    rw [bags_power,coeff_zero_eq_constantCoeff_apply,landing f B J hT hv,← coeff_zero_eq_constantCoeff_apply,← bags_power,linear_shadow f G H V he]
  | succ i ih=>
    refine smul_right_injective _ (show ((i+1:ℕ):ℝ)≠0 by positivity) ?_
    dsimp only; rw [← clock_coeff,← clock_coeff,bags_clock,hw f,bags_clock,ih]
end YM.WilsonBulk.Sheet
