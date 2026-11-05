import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Shoot.Criteria


/-!
# Polydisc analyticity for finite spacetime and analytic rows

Mathlib pin offers `DifferentiableOn.analyticAt` for **one** complex
scalar. Here: direct tower of Cauchy integrals moves every coordinate in
a polydisc. Bundle them in a Banach algebra so kernel analyticity suffices.
No Lebesgue product axis orientation ambiguity. Does not assume power
series regularity without verifying in multi dimensions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PolyDisc
open Filter Function Set Complex MeasureTheory Topology Metric
open scoped ContDiff BigOperators NNReal ENNReal

variable {α : Type} [Fintype α]

abbrev height := Icc (0:ℝ) (2*Real.pi)
abbrev Screen (α : Type) := α → height
abbrev Reel (α : Type) := C(Screen α,ℂ)

def clamps (x : ℝ) : height := projIcc 0 (2*Real.pi) (by positivity) x
instance : CompactSpace height := isCompact_iff_compactSpace.mp isCompact_Icc
instance : Nonempty height := ⟨clamps 0⟩

variable [DecidableEq α] (i : α)

private def snap (F : Reel α) (x : ℝ) : Reel α := {
  toFun := fun z => F (update z i (clamps x))
  continuous_toFun := by
    apply F.continuous.comp (continuous_pi _)
    intro j; by_cases h : j=i <;> simp [h,continuous_apply]; exact continuous_const }

omit [Fintype α] in
private lemma continuous_snap (F : Reel α) : Continuous (snap i F) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  change Continuous (fun z : ℝ × Screen α => F (update z.2 i (clamps z.1)))
  refine F.continuous.comp (continuous_pi ?_)
  intro j; by_cases h : j=i <;> simp [h]
  · exact continuous_projIcc.comp continuous_fst
  exact (continuous_apply _).comp continuous_snd

omit [Fintype α] in
private lemma anytime (F : Reel α) : IntervalIntegrable (snap i F) volume 0 (2*Real.pi) :=
  (continuous_snap ..).intervalIntegrable ..

private def cutout : Reel α →ₗ[ℂ] Reel α where
  toFun F := ∫ x : ℝ in 0..2*Real.pi,snap i F x
  map_add' F G := by
    have hg (x) : snap i (F+G) x=snap i F x+snap i G x := by ext; rfl
    simp_rw [hg, intervalIntegral.integral_add (anytime i F) (anytime i G)]
  map_smul' a F := by
    have he (x) : snap i (a • F) x=a • snap i F x := by ext; rfl
    simp_rw [he, intervalIntegral.integral_smul]
    rfl

def average : Reel α →L[ℂ] Reel α := LinearMap.mkContinuous (cutout i) (2*Real.pi) (fun F => by
  change ‖(∫ x : ℝ in 0.._,snap i F x)‖ ≤ _
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C:=‖F‖) (fun x hx => ?_)).trans_eq (by simp [Real.pi_pos.le,abs_of_nonneg]; ring)
  exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun z => F.norm_coe_le_norm _)

lemma average_act (F : Reel α) (p : Screen α) : average i F p = ∫ x : ℝ in 0..2*Real.pi,F (update p i (clamps x)) :=
    ((ContinuousMap.evalCLM ℂ p).intervalIntegral_comp_comm (𝕜:=ℂ) (anytime i F)).symm

abbrev Plain (α : Type*) := α → ℂ
variable {c : Plain α} {R : ℝ} {f : Plain α → ℂ}

def Accept (c : Plain α) (R : ℝ) (x : Plain α) := ∀ i, x i∈closedBall (c i) R

def Takes (c : Plain α) (R : ℝ) (x : Plain α) := ∀ i, x i∈ball (c i) R

omit [DecidableEq α] in
lemma Takes.at (hr : 0<R) : ∀ᶠ z in 𝓝 c, Takes c R z := eventually_all.mpr fun i =>
    (continuous_apply i).continuousAt.tendsto.eventually (ball_mem_nhds (c i) hr)

structure Eats (c : Plain α) (R : ℝ) (f : Plain α → ℂ) : Prop where
  full : 0 < R
  diff x : Accept c R x → DifferentiableAt ℂ f x

def ride (c : Plain α) (R : ℝ) : Reel α := ⟨fun v => circleMap (c i) R (v i),
    (continuous_circleMap ..).comp (continuous_subtype_val.comp (continuous_apply i))⟩

def speed (c : Plain α) (R : ℝ) : Reel α :=
    ⟨fun v => deriv (circleMap (c i) R) (v i) *(2 * Real.pi * I)⁻¹, by
      simp only [deriv_circleMap]; fun_prop⟩

def denom (c : Plain α) (R : ℝ) (x : Plain α) : Reel α := ride i c R-ContinuousMap.const (Screen α) (x i)

private def unit {x : Plain α} (h : Takes c R x) : (Reel α)ˣ where
  val := denom i c R x
  inv := ⟨fun p => ((circleMap (c i) R (p i) - x i))⁻¹,(continuous_circleMap_inv (h i)).comp (continuous_subtype_val.comp (continuous_apply i))⟩
  val_inv := by
    ext1 p; exact mul_inv_cancel₀ (sub_ne_zero.mpr (circleMap_ne_mem_ball (h i)  (p i)))
  inv_val := by
    ext1 p; exact inv_mul_cancel₀ (sub_ne_zero.mpr (circleMap_ne_mem_ball (h i) _))

def kernel (c : Plain α) (R : ℝ) (x : Plain α) : Reel α := Ring.inverse (denom i c R x) * speed i c R

omit [DecidableEq α] [Fintype α] in
lemma value {x} (h : Takes c R x) (p : Screen α) : kernel i c R x p = (circleMap (c i) R (p i) - x i)⁻¹* speed i c R p := by
  unfold kernel; rw [show denom i c R x=↑(unit i h) from rfl,Ring.inverse_unit]; rfl

omit [DecidableEq α] in
lemma forms (hR : 0<R) : AnalyticAt ℂ (kernel i c R) c := by
  have hh : AnalyticAt ℂ (denom i c R) c := by
    let g := (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _ : α=>ℂ) i) (1:Reel α))
    have hk : denom i c R=(fun x => ride i c R - g x) := by ext x z; simp [denom,g]; try rfl
    rw [hk]
    exact analyticAt_const.sub (g.analyticAt _)
  have he : AnalyticAt ℂ Ring.inverse (denom i c R c) := analyticAt_inverse (𝕜:=ℂ) (unit i (mem_of_mem_nhds (Takes.at hR)))
  exact (he.comp hh).mul analyticAt_const

variable {i}

def choose (s : Finset α) (c : Plain α) (R : ℝ) (p : Plain α) (u : Screen α) (i : α) : ℂ :=
    if i ∈ s then ride i c R u else p i

omit [Fintype α] in
@[fun_prop] lemma choose_cont (s : Finset α) (x : Plain α) : Continuous (choose s c R x) := by
  apply continuous_pi; intro i; unfold choose; split <;> fun_prop

variable (h : Eats c R f)

include h
omit [Fintype α] in
lemma Eats.remains (s : Finset α) {x : Plain α} (u : Takes c R x) (z : Screen α) : Accept c R (choose s c R x z) := by
  intro i; unfold choose; split
  · exact sphere_subset_closedBall (circleMap_mem_sphere (c i) h.full.le _)
  exact ball_subset_closedBall (u i)

def Eats.image (s : Finset α) {x} (u : Takes c R x) : Reel α := {
    toFun := fun p => f (choose s c R x p)
    continuous_toFun := continuous_iff_continuousAt.mpr fun p => (h.diff _ (h.remains s u p)).continuousAt.comp (choose_cont s x).continuousAt }

def Eats.series (s : Finset α) {x} (u : Takes c R x) : Reel α := (∏ i∈s, kernel i c R x) * h.image s u

lemma channel {x : Plain α} (u : Takes c R x) {s : Finset α} (hi : i ∉ s) : average i (h.series (insert i s) u) = h.series s u := by
  classical
  -- fixed background point, specialize Cauchy in ℂ
  ext1 p
  let z := choose s c R x p
  let F w := f (update z i w)
  have he : DifferentiableOn ℂ F (closedBall (c i) R) := by
    intro q hq
    have hy (w) := h.remains s u p w
    have hz : Accept c R (update z i q) := fun k => by by_cases H : k=i; simpa [H] using hq; simpa [H] using hy k
    apply DifferentiableAt.differentiableWithinAt
    refine (h.diff _ hz).comp q (differentiableAt_pi.mpr (fun j => ?_))
    by_cases h : j=i <;> simp [*,differentiableAt_fun_id]
  have hz : update z i (x i)=z := by rw [show x i=z i by simp [z,choose,hi]]; exact update_eq_self _ _
  have hQ := he.circleIntegral_sub_inv_smul (u i)
  unfold circleIntegral at hQ
  rw [show F (x i)=f z by unfold F; rw [hz]] at hQ
  let d := ∏ j∈s,kernel j c R x p
  let K := 2*Real.pi*I
  have hk : K≠0 := by unfold K; simp [Real.pi_ne_zero]
  let g t := deriv (circleMap (c i) R) t • ((circleMap (c i) R t - x i)⁻¹ • F (circleMap (c i) R t))
  have ht : ∀ t : ℝ,t∈ uIcc 0 (2*Real.pi) → h.series (insert i s) u (update p i (clamps t))=d*K⁻¹*g t := by
    intro t ht
    rw [uIcc_of_le (by positivity)] at ht
    let b := update p i (clamps t)
    have h0 : ((b i):ℝ)=t := by simp [b,clamps,Set.projIcc_of_mem _ ht]
    have h1 j (hh : j ∈ s) : kernel j c R x b=kernel j c R x p := by
      have hp : j≠i := fun h => hi (h ▸ hh)
      simp only [value j u, speed,ContinuousMap.coe_mk,b,update_of_ne hp]
    change h.series _ _ b = _
    have h2 : choose (insert i s) c R x b=update z i (circleMap (c i) R t) := by
      ext1 j
      by_cases H : j=i
      · simp only [H,choose,Finset.mem_insert_self,↓reduceIte,update_self]; unfold ride; simp [h0]
      rw [update_of_ne H]; unfold z choose; simp only [Finset.mem_insert,H,false_or]
      split; swap; rfl
      simp [ride,b,H]
    rw [Eats.series, ContinuousMap.mul_apply, ContinuousMap.prod_apply]
    rw [Finset.prod_insert hi, show (∏ j ∈ s, _) = d from Finset.prod_congr rfl fun j hj => h1 j hj]
    rw [Eats.image]; simp only [ContinuousMap.coe_mk]; rw [h2,value i u]
    simp only [speed,g,K,F,ContinuousMap.coe_mk,h0,smul_eq_mul]; ring
  have hr : h.series s u p = d*f z := by rw [Eats.series,ContinuousMap.mul_apply,ContinuousMap.prod_apply]; rfl
  rw [average_act,hr]
  rw [intervalIntegral.integral_congr ht,intervalIntegral.integral_const_mul]
  change (∫ t in (0:ℝ)..2*Real.pi,g t) = K • f z at hQ
  rw [hQ,smul_eq_mul, mul_assoc, inv_mul_cancel_left₀ hk]

lemma Eats.invertor (s : Finset α) : ∃ v : Reel α →L[ℂ] ℂ, ∀ x (u : Takes c R x), v (h.series s u)= f x := by
  induction s using Finset.induction_on with
  | empty =>
    let p : Screen α := fun i => clamps 0
    refine ⟨ContinuousMap.evalCLM ℂ p, fun x u => ?_⟩
    unfold Eats.series
    rw [Finset.prod_empty,one_mul]
    change f (choose ∅ c R x p)=_; rw [show choose ∅ _ _ _ p=x from funext fun i => by simp [choose]]
  | @insert i s hi IH =>
    obtain ⟨v,hv⟩ := IH
    refine ⟨v ∘L average i,fun x u => ?_⟩
    rw [ContinuousLinearMap.comp_apply,channel h u hi,hv]

lemma Eats.hol : AnalyticAt ℂ f c := by
  obtain ⟨v,hv⟩ := h.invertor Finset.univ
  have he : Takes c R c := mem_of_mem_nhds (Takes.at h.full)
  let F (z : Plain α) := (∏ i,kernel i c R z) * h.image Finset.univ he
  have hh : AnalyticAt ℂ F c := (show AnalyticAt ℂ (fun x : Plain α => ∏ i,kernel i c R x) c from
    (by apply Finset.analyticAt_fun_prod; intro i _; exact forms i h.full)).mul analyticAt_const
  refine ((v.analyticAt _).comp hh).congr ?_
  filter_upwards [Takes.at h.full] with x hx
  change v (F x)=f x
  rw [← hv x hx]; apply congr_arg v
  unfold F Eats.series
  congr 1; ext i; simp [Eats.image]; congr 1; funext j; simp [choose]
omit h [DecidableEq α] in
lemma formOf (he : ∀ᶠ x in 𝓝 c, DifferentiableAt ℂ f x) : AnalyticAt ℂ f c := by
  classical
  obtain ⟨R,hR,H⟩ := Metric.mem_nhds_iff.mp he
  refine Eats.hol (c:=c) (R:=R/2) (f:=f) ⟨by linarith,fun x hx => H ?_⟩
  have he : ‖x-c‖ ≤ R/2 := (pi_norm_le_iff_of_nonneg (by linarith)).mpr (fun i => by have ht:=hx i; rw [mem_closedBall,dist_eq_norm] at ht; exact ht)
  rw [Metric.mem_ball,dist_eq_norm]; linarith

omit h in
lemma finiteD {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [FiniteDimensional ℂ Y] (F : X → Y) {x} (H : ∀ᶠ z in 𝓝 x,DifferentiableAt ℂ F z) : AnalyticAt ℂ F x := by
  classical
  let a := (Module.finBasis ℂ X); let b := (Module.finBasis ℂ Y)
  let W := LinearEquiv.toContinuousLinearEquiv a.equivFun; let K := LinearEquiv.toContinuousLinearEquiv b.equivFun
  let f := K ∘ F ∘ W.symm
  have hy (i : Fin (Module.finrank ℂ Y)) : AnalyticAt ℂ (fun p : Plain (Fin (Module.finrank ℂ X)) => f p i) (W x) := by
    apply formOf
    have he := W.symm.continuousAt.tendsto (x:=W x)
    rw [W.symm_apply_apply] at he
    filter_upwards [he.eventually H] with u hu
    change DifferentiableAt ℂ F (W.symm u) at hu
    apply (differentiableAt_pi.mp (show DifferentiableAt ℂ f u from K.differentiableAt.comp u (hu.comp _ W.symm.differentiableAt))) i
  have hF : ContDiffAt ℂ ω f (W x) := contDiffAt_pi.mpr (fun i => (hy i).contDiffAt)
  have ht := K.symm.analyticAt (𝕜:=ℂ) (f (W x)) |>.comp (hF.analyticAt) |>.comp (W.analyticAt (𝕜:=ℂ) x)
  convert! ht using 1; ext; simp [f]
end YM.PolyDisc
