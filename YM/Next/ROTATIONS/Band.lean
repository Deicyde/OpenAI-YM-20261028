import Mathlib.Analysis.Calculus.BumpFunction.Normed
import YM.Next.ROTATIONS.Profile

/-! # Profiles in bounded and annular frequency bands, including smooth division -/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Metric
open scoped ContDiff Topology BigOperators NNReal ENNReal

def Ends (f : Profile) := HasCompactSupport ⇑f
def Far (f : Profile) := Ends f ∧ ⇑f =ᶠ[𝓝 (0:ℝ)] (fun _ => 0)
def Reflects (b : Bool) (f : Profile) := ∀ x, f (-x)=(if b then -f x else f x)
def Plus (f : Profile) := ∀ x, 0 ≤ f x
lemma ends_zero : Ends 0 := HasCompactSupport.zero
lemma Ends.add {f g} (hf : Ends f) (hg : Ends g) : Ends (f+g) := (show HasCompactSupport ⇑f from hf).add hg
lemma Ends.sub {f g} (hf : Ends f) (hg : Ends g) : Ends (f-g) := (show HasCompactSupport ⇑f from hf).sub hg
lemma Ends.scale {f} (hf : Ends f) (z : ℝ) : Ends (z • f) := HasCompactSupport.mul_left (f:=fun _ => z) hf
lemma Ends.width {f : Profile} (hf : Ends f) (w) : Ends (width w f) := by
  unfold _root_.YM.Outer.width
  split
  · simpa using ends_zero
  rename_i h
  exact Ends.scale (f:=SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 w⁻¹ (inv_ne_zero h))) f) (HasCompactSupport.comp_homeomorph hf
      (ContinuousLinearEquiv.toHomeomorph (R₁:=ℝ) (R₂:=ℝ) (ContinuousLinearEquiv.smulLeft (Units.mk0 w⁻¹ (inv_ne_zero h)) : ℝ ≃L[ℝ] ℝ))) _
lemma Far.zero : Far (0 : Profile) := ⟨ends_zero,Eventually.of_forall fun _ => rfl⟩
lemma Far.add {f g} (h : Far f) (l : Far g) : Far (f+g) := by
  refine ⟨h.1.add l.1,?_⟩; filter_upwards [h.2,l.2] with x hx hy
  change f x+g x=0; rw [show f x=0 from hx,show g x=0 from hy,add_zero]
lemma Far.scale {f} (h : Far f) (z : ℝ) : Far (z • f) := by
  refine ⟨h.1.scale z,?_⟩; filter_upwards [h.2] with x hx
  change z*f x=0; rw [show f x=0 from hx,mul_zero]
lemma Far.sum {ι : Type*} (s : Finset ι) {f : ι → Profile} (h : ∀ i∈s,Far (f i)) : Far (∑ i ∈ s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Far.zero
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun x hx => h x (by simp [hx]))
lemma Far.width {f} (h : Far f) (w : ℝ) : Far (width w f) := by
  refine ⟨h.1.width w,?_⟩
  have he : Tendsto (fun x : ℝ => x/w) (𝓝 0) (𝓝 0) := by simpa using (continuous_id.div_const w).continuousAt (x:=0) |>.tendsto
  filter_upwards [he.eventually h.2] with x hx
  rw [width_at,show f (x/w)=0 from hx,mul_zero]
lemma Far.at_zero {f : Profile} (h : Far f) : f 0=0 := h.2.self_of_nhds
lemma Reflects.tall {f b} (h : Reflects b f) (c : ℝ) : Reflects b (width c f) := by
  intro x; rw [width_at,neg_div,h (x/c)]
  cases b <;> simp [width_at]
lemma Reflects.sum {b} {ι : Type*} (s : Finset ι) {f : ι → Profile} (h : ∀ i ∈ s,Reflects b (f i)) : Reflects b (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro; simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    intro x; have ht := ih fun i hi => h i (by simp [hi]); have H := h i (by simp)
    cases b <;> simp only [_root_.add_apply,H x,ht x] <;> simp [add_comm]
lemma Reflects.scale {f : Profile} {b} (h : Reflects b f) (c : ℝ) : Reflects b (c•f) := by
  intro x
  rw [_root_.smul_apply,h x]; cases b <;> simp
lemma Plus.scale {f : Profile} (h : Plus f) (c : ℝ) (hc : 0≤c) : Plus (c • f) := fun x => mul_nonneg hc (h x)
lemma Plus.tall {f : Profile} (h : Plus f) (w : ℝ) (hw : 0 ≤ w) : Plus (width w f) := by
  intro x; rw [width_at]; exact mul_nonneg (by positivity) (h _)

lemma Ends.pumps {f : Profile} (h : Ends f) (j) : Ends (pump j f) := by
  unfold Ends; rw [show ⇑(pump j f) = (fun x : ℝ => x^j) * f from funext fun x => pump_at j f x]; exact HasCompactSupport.mul_left h
lemma Far.pumps {f : Profile} (h : Far f) (j) : Far (pump j f) := by
  refine ⟨h.1.pumps j,?_⟩; filter_upwards [h.2] with x hx
  rw [pump_at,show f x=0 from hx,mul_zero]

lemma Far.puncture {f : Profile} (h : Far f) (j : ℕ) : ∃ g : Profile,Far g ∧ ∀ x, g x=x⁻¹^j*f x := by
  let z (x : ℝ) := x⁻¹^j*f x
  have hi : HasCompactSupport z := HasCompactSupport.mul_left h.1 (f:=fun x : ℝ => x⁻¹^j)
  have he : z =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [h.2] with x hx
    change _*f x=0; simp [show f x=0 from hx]
  have hf : ContDiff ℝ ∞ z := contDiff_iff_contDiffAt.mpr fun x => by
    rcases eq_or_ne x 0 with rfl|hx
    · exact contDiffAt_const.congr_of_eventuallyEq he
    exact ((contDiffAt_id.inv hx).pow j).mul (f.smooth ⊤).contDiffAt
  exact ⟨hi.toSchwartzMap hf,⟨hi,he⟩, fun _ => rfl⟩
open scoped Classical in
def slash (k : ℕ) (f : Profile) : Profile := if h : Far f then (h.puncture k).choose else 0
lemma slash_far {f : Profile} (h : Far f) (j) : Far (slash j f) := by unfold slash; rw [dif_pos h]; exact (h.puncture j).choose_spec.1
lemma slash_at {f : Profile} (h : Far f) (j) (x) : slash j f x=x⁻¹^j*f x := by unfold slash; rw [dif_pos h]; exact (h.puncture j).choose_spec.2 x
lemma tally_odd (b : Bool) (f : Profile) (h : Reflects b f) (j : ℕ) (hx : if b then Even j else Odd j) : tally j f=0 := by
  have he : ∫ x : ℝ,(-x)^j * f (-x) = ∫ x : ℝ,x^j * f x := integral_neg_eq_self (fun x : ℝ => x^j*f x) volume
  have hv (x : ℝ) : (-x)^j*f (-x)=-(x^j*f x) := by
    rw [h x]; cases b
    · rw [(show Odd j by simpa using hx).neg_pow]; simp
    rw [(show Even j by simpa using hx).neg_pow]; simp
  simp_rw [hv,integral_neg] at he
  rw [counts]; linarith

private def someR : ContDiffBump (3/2:ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
private def high : Profile := (someR.hasCompactSupport_normed (μ:=volume)).toSchwartzMap (someR.contDiff_normed (μ:=volume))
lemma make_sun : ∃ f : Profile, Far f ∧ Reflects false f ∧ Plus f ∧ tally 0 f=1 ∧ ∀ x, f x≠0 → 1 ≤ |x| ∧ |x| ≤ 2 := by
  let g := -(width (-1) high)
  have he (x) : g x= high (-x) := by unfold g; simp [width_at,div_eq_mul_inv]
  have hu : Far high := by
    refine ⟨someR.hasCompactSupport_normed (μ:=volume),?_⟩
    filter_upwards [Ioo_mem_nhds (a:=(-1:ℝ)) (b:=1) (by norm_num) (by norm_num)] with x hx
    apply notMem_support.mp
    rw [show support high=_ from someR.support_normed_eq (μ:=volume)]
    have ht := hx.2
    simp only [mem_ball,Real.dist_eq,someR]; intro H
    exact (abs_lt.mp H).1.not_ge (by linarith)
  let f := (1/2:ℝ) • (high + g)
  have hv : Far g := by
    rw [show g = (-1:ℝ) • width (-1) high by simp [g]]; exact (hu.width _).scale _
  have hh (x) : f x = (1/2:ℝ)*(high x+ high (-x)) := by simp [f,he,mul_add]
  have hc (x : ℝ) : 0 ≤ high x := someR.nonneg_normed (μ:=volume) x
  have ht : tally 0 high=1 := by
    rw [counts]; simp only [pow_zero,one_mul]; exact someR.integral_normed (μ:=volume)
  have hl : tally 0 g=tally 0 high := by
    simp_rw [counts,pow_zero,one_mul,he]; exact integral_neg_eq_self high volume
  refine ⟨f,(hu.add hv).scale _,fun x => by rw [hh,neg_neg,hh,add_comm]; rfl,fun x => by rw [hh]; exact mul_nonneg (by norm_num) (add_nonneg (hc _) (hc _)),?_,?_⟩
  · rw [show f= _ from rfl,map_smul,map_add,hl,ht]; norm_num
  intro x hx
  have hf a (h : high a≠0) : 1 ≤ |a| ∧ |a| ≤ 2 := by
    have hz := show a ∈ support high from h
    rw [show support high=ball _ _ from someR.support_normed_eq (μ:=volume)] at hz
    rw [mem_ball,Real.dist_eq] at hz
    obtain ⟨H,G⟩ := abs_lt.mp hz
    dsimp only [someR] at H G
    rw [abs_of_nonneg (by linarith)]; constructor <;> linarith
  by_cases H : high x=0
  · have ha : high (-x) ≠ 0 := fun h => hx (by simp [hh,H,h])
    simpa using hf _ ha
  exact hf _ H

def sun := make_sun.choose
lemma sun_far : Far sun := make_sun.choose_spec.1
lemma sun_even : Reflects false sun := make_sun.choose_spec.2.1
lemma sun_plus : Plus sun := make_sun.choose_spec.2.2.1
lemma sun_mass : tally 0 sun=1 := make_sun.choose_spec.2.2.2.1
lemma sun_pos {x : ℝ} (h : sun x≠0) : 1 ≤ |x| ∧ |x| ≤ 2 := make_sun.choose_spec.2.2.2.2 x h
end YM.Outer
