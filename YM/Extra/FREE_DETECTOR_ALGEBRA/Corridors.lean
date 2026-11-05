import YM.Extra.FREE_DETECTOR_ALGEBRA.AngularLeg
import YM.Extra.FREE_DETECTOR_ALGEBRA.HoldWeights
import YM.Extra.FREE_DETECTOR_ALGEBRA.RanksTwo

set_option warningAsError false

/-! Relay analytic/rational tests. If all real Taylor derivatives
at a *single* separated collinear point are invisible, at that arity
all separated points are. Clears denominators to avoid analytic extension
through coincident arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest Residue OPE Ward Climb MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix ENNReal

variable {G : Gauge} (F : Frames G) {d e n j : ℕ} {x : Points n}
local notation "W" => Table.Field (freeTable F)
local notation "T" => freeTable F
local notation "γ" => writes F

-- ratio of total analytic functions
structure Crossed (f : Points n→ ℂ) : Type where
  p : Points n→ℂ
  q : Points n→ℂ
  good : ContDiff ℝ ω p
  solid : ContDiff ℝ ω q
  safe (x : Points n) (hx : x∈conf n) : q x ≠ 0
  reads (x : Points n) (hx : x∈conf n) : q x * f x=p x

def Enhanced (f : Points n→ℂ) := Nonempty (Crossed f)
lemma EnhConst (c : ℂ) : Enhanced (fun _ : Points n => c) := ⟨⟨fun _ => c,fun _ => 1,contDiff_const,contDiff_const,fun _ _ => one_ne_zero,fun _ _ => one_mul c⟩⟩
lemma EnhPlus {f g : Points n→ℂ} (hf : Enhanced f) (hg : Enhanced g) : Enhanced (fun x => f x+g x) := by
  obtain ⟨A⟩:=hf; obtain ⟨B⟩:=hg
  refine ⟨⟨fun x => A.p x * B.q x+B.p x * A.q x,fun x=>A.q x*B.q x,(A.good.mul B.solid).add (B.good.mul A.solid), A.solid.mul B.solid,fun x h=>mul_ne_zero (A.safe x h) (B.safe x h),fun x h=>?_⟩⟩
  rw [← A.reads x h,← B.reads x h]; ring
lemma EnhProd {f g : Points n→ℂ} (hf : Enhanced f) (hg : Enhanced g) : Enhanced (fun x => f x*g x) := by
  obtain ⟨A⟩:=hf; obtain ⟨B⟩:=hg
  refine ⟨⟨fun x => A.p x*B.p x,fun x=>A.q x*B.q x,A.good.mul B.good, A.solid.mul B.solid,fun x h=>mul_ne_zero (A.safe x h) (B.safe x h),fun x h=>?_⟩⟩
  rw [← A.reads x h,← B.reads x h]; ring
lemma EnhSum {ι : Type*} (s : Finset ι) (f : ι→Points n→ℂ) (h : ∀ i∈s,Enhanced (f i)) : Enhanced (fun x=> ∑ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact EnhConst _
  | insert a s ha ih => simp_rw [Finset.sum_insert ha]; exact EnhPlus (h _ (Finset.mem_insert_self ..)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
lemma EnhPi {ι : Type*} (s : Finset ι) (f : ι→Points n→ℂ) (h : ∀ i∈s,Enhanced (f i)) : Enhanced (fun x=> ∏ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact EnhConst _
  | insert a s ha ih => simp_rw [Finset.prod_insert ha]; exact EnhProd (h _ (Finset.mem_insert_self ..)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma EnhKelvin (P Q : Slot G) (i k : Fin n) (he : i≠k) : Enhanced (fun x : Points n => entry P Q (x i) (x k)) := by
  let f (z : E4) := legKernel (coordinateLeg P) (coordinateLeg Q) z
  let H (x : Points n) := x i-x k
  let j := P.1+Q.1+2
  obtain ⟨L,hL,h⟩ := (show KelvinAng j f from ang_leg ..)
  have hs : ContDiff ℝ ω L := by obtain ⟨P,hP,-⟩ := hL.size.tensor; rw [hP]; exact diag_smooth P ω
  have hu (i : Fin n) : ContDiff ℝ ω (fun x : Points n=>x i) := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n=> E4) i).contDiff
  have ht : ContDiff ℝ ω H := (hu i).sub (hu k)
  refine ⟨⟨fun x => (L (H x):ℂ),fun x=> (↑(‖H x‖^2 : ℝ):ℂ)^(j+1), Complex.ofRealCLM.contDiff.comp (hs.comp ht),(Complex.ofRealCLM.contDiff.comp ((contDiff_norm_sq ℝ).comp ht)).pow _,fun x hx => ?_,fun x hx => ?_⟩⟩
  · have hp := norm_pos_iff.mpr (show H x≠0 from sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne he)); exact pow_ne_zero _ (by exact_mod_cast (show ‖H x‖^2 ≠ 0 by positivity))
  have hp : H x∈away := sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne he)
  change _ * (↑(f (H x)):ℂ)= _; rw [h hp]; change (↑(‖H x‖^2):ℂ)^(j+1)*(↑( (‖H x‖^2)⁻¹^(j+1)*L (H x)):ℂ)= _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,← mul_assoc,← mul_pow,mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)),one_pow,one_mul]

lemma EnhMoment (v : Fin n → WickPol G) : Enhanced (fun x => moment G x v) := by
  simp_rw [sumFormula]; refine EnhSum _ _ fun _ _ => EnhProd (EnhConst _) (EnhSum _ _ fun i _ => EnhPi _ _ fun k _ => EnhKelvin _ _ _ _ (Occ.different i k).symm)

lemma EnhDiagram (P : Climb.Matrix d e T) (v : Fin n → W d) : Enhanced (diagram v P) := by
  rw [funext (beam_diagram F v P)]
  exact EnhSum _ _ fun i _ => EnhMoment _

lemma foreground {f : Points n→ℂ} (A : Crossed f) (hx : x∈conf _) : ContDiffAt ℝ ω f x := by
  have he := A.safe x hx
  have hh : f=ᶠ[𝓝 x] A.p/A.q := by
    filter_upwards [(conf_open _).mem_nhds hx] with y hy
    rw [Pi.div_apply]; apply (eq_div_iff (A.safe y hy)).mpr; rw [mul_comm]; exact A.reads y hy
  rw [div_eq_mul_inv] at hh
  exact ((A.good.contDiffAt (x:=x)).mul ((A.solid.contDiffAt (x:=x)).inv he)).congr_of_eventuallyEq hh


end YM.Extra.FD
