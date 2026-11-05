import YM.Pert.Lattice.Symbol
import Mathlib.Algebra.MvPolynomial.Variables
/-! Add an imaginary independent top-cover linear Wick jet to each local mark and Gaussian-average it *separately inside each mark* (the sign for ordinary Wick subtraction). -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Full
open Lattice Filter MeasureTheory Matrix Set Bare Labels Orb ProbabilityTheory
open Next.SectorChange.Gaussian
open scoped Topology BigOperators ENNReal
variable {G : Gauge} {d : ℕ} {n : Side}
abbrev Aux (G : Gauge) (d : ℕ) := CosKey G d → ℝ
def auxLaw (G : Gauge) (d : ℕ) (a : ℝ) := cloud (shellCov G d a)
lemma auxGaussian (a : ℝ) : IsGaussian (auxLaw G d a) := by
  unfold auxLaw cloud; exact inferInstanceAs (IsGaussian (Measure.map ((WithLp.linearEquiv 2 ℝ (Aux G d)).toContinuousLinearMap) (multivariateGaussian 0 _)))
instance {a : ℝ} : IsProbabilityMeasure (auxLaw G d a) := inferInstanceAs (IsProbabilityMeasure (cloud _))
lemma bareTame_integrable {f : Aux G d → ℂ} (a : ℝ) (h : Tame f) : Integrable f (auxLaw G d a) := by
  haveI := auxGaussian (G:=G) (d:=d) a
  obtain ⟨C,_,k,hK⟩ := h.2
  have hi : Integrable (fun x : Aux G d => (1+‖x‖)^k) (auxLaw G d a) := by
    by_cases hk : k=0; · simp [hk]
    have e := ((IsGaussian.memLp_id (auxLaw G d a) k (by simp)).norm.add (memLp_const (1:ℝ))).integrable_norm_pow hk
    convert! e using 2
    simp only [Pi.add_apply,id_eq,Real.norm_eq_abs]; rw [abs_of_nonneg (by positivity),add_comm]
  exact (hi.const_mul C).mono' h.1.aestronglyMeasurable (Eventually.of_forall hK)
local notation "coef" => (PowerSeries.coeff (R:=ℂ))
def avg (a : ℝ) (f : JetArray (Aux G d)) : PowerSeries ℂ := PowerSeries.mk (fun i => ∫ x : Aux G d, coef i (f x) ∂auxLaw G d a)
lemma avg_add {f g : JetArray (Aux G d)} (a : ℝ) (h : Ready f) (j : Ready g) : avg a (f+g) = avg a f+avg a g := by
  ext1 m; simp only [avg,PowerSeries.coeff_mk,map_add,Pi.add_apply,integral_add (bareTame_integrable a (h m)) (bareTame_integrable a (j m))]
lemma avg_const_mul (z : PowerSeries ℂ) (f : JetArray (Aux G d)) (a) (h : Ready f) : avg a ((fun _ => z)*f) = z * avg a f := by
  ext1 m; simp only [avg,PowerSeries.coeff_mk,PowerSeries.coeff_mul, Pi.mul_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl; intros p hp; rw [integral_const_mul]
  exact fun p _ => (bareTame_integrable a (h p.2)).const_mul _

def ink (x : Aux G d) (z : Key G) : ℂ := Complex.I * ↑(if h : z.1≤d then x (⟨z,h⟩:CosKey G d) else 0)
def pairEval (h : ℝ) (o : Site n) (c : Coords G n) (v : Aux G d) (p : Pol G) := MvPolynomial.eval₂Hom PowerSeries.C (fun z => seriesLex h o c z + PowerSeries.C (ink v z)) p
def dye (q : Pol G) (v : Aux G d) := (PowerSeries.C (MvPolynomial.eval (ink v) q) : PowerSeries ℂ)
def paint (d : ℕ) (h : ℝ) (o : Site n) (p w : Pol G) (x : Coords G n) := avg (d:=d) h (dye w * fun v => pairEval h o x v p)
/-- Wick-subtracted bare input (so its positive-loop corrections include completions of lower-leg columns).
This definition uses no measured nonperturbative values. -/
def column (d : ℕ) (h : ℝ) (o : Site n) (p : Pol G) (x : Coords G n) : PowerSeries ℂ := paint d h o p 1 x

lemma ready_const_iff {D : Type*} [NormedAddCommGroup D] {z : D → ℂ} : Ready (fun v => PowerSeries.C (z v)) ↔ Tame z := by
  unfold Ready; simp_rw [PowerSeries.coeff_C]; exact ⟨fun h => by simpa only [↓reduceIte] using h 0, fun h i => by by_cases h' : i=0 <;> simp only [h',↓reduceIte]; exacts [h, Tame.constant _]⟩
lemma ink_tame (i : Key G) : Tame (fun v : Aux G d => ink v i) := by
  unfold ink; split
  · exact (Tame.constant _).mul (Tame.ofReal (Tame.clm (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : CosKey G d => ℝ) _)))
  exact Tame.constant _
lemma deep_tame (w : Pol G) : Tame (fun v : Aux G d => MvPolynomial.eval (ink v) w) := by
  induction w using MvPolynomial.induction_on
  case C z => simp_rw [MvPolynomial.eval_C]; exact Tame.constant z
  case add p q hp hq => simp only [map_add]; exact Tame.add hp hq
  case mul_X p z hp => simp only [map_mul,MvPolynomial.eval_X]; exact Tame.mul hp (ink_tame z)
lemma dye_ready (w : Pol G) : Ready (dye (d:=d) w) := ready_const_iff.mpr (deep_tame ..)
lemma leg_ready (h : ℝ) (o : Site n) (x) (w : Pol G) : Ready (fun v : Aux G d => pairEval h o x v w) := by
  unfold pairEval; induction w using MvPolynomial.induction_on
  case C c => simp only [MvPolynomial.eval₂Hom_C]; exact Ready.constant _
  case add p q hp hq => simp only [map_add]; exact Ready.add hp hq
  case mul_X p z hp =>
    simp only [map_mul,MvPolynomial.eval₂Hom_X']; exact (hp.mul (Ready.add (Ready.constant _) (ready_const_iff.mpr (ink_tame z))))
lemma paint_sum (h : ℝ) (o : Site n) (p q w : Pol G) : paint d h o (p+q) w = paint d h o p w + paint d h o q w := by
  ext1 x
  refine (congrArg (avg h) (show dye (d:=d) w * (fun v => pairEval h o x v (p+q))= (dye w * (fun v => pairEval h o x v p))+(dye w * (fun v => pairEval h o x v q)) from funext (fun v=> by simp [pairEval,mul_add]))).trans ?_
  apply avg_add (G:=G) (d:=d) h (Ready.mul (dye_ready w) (leg_ready _ _ x p)) (Ready.mul (dye_ready w) (leg_ready _ _ x q))
lemma paint_x (h : ℝ) (o : Site n) (p w : Pol G) (z) : paint d h o (p * MvPolynomial.X z) w = paint d h o p w * (fun x => seriesLex h o x z) + paint d h o p (w * MvPolynomial.X z) := by
  ext1 x
  let F : Aux G d → PowerSeries ℂ := fun v => pairEval h o x v p
  let H (v : Aux G d) := PowerSeries.C (ink v z)
  have hF : Ready F := leg_ready h o x p
  have hH : Ready H := ready_const_iff.mpr (ink_tame z)
  let u := dye (d:=d) w
  have : paint d h o (p * MvPolynomial.X z) w x = avg h ((fun _ => seriesLex h o x z) * (u*F) + (H*u*F)) := congrArg (avg h) (funext (fun v => by change u v * _ = _; simp only [pairEval,map_mul,MvPolynomial.eval₂Hom_X',Pi.add_apply,Pi.mul_apply,H,F]; ring))
  rw [this]
  have hu : H*u*F=dye (w*MvPolynomial.X z)*F := by ext1 v; simp [H,u,dye,mul_comm]
  rw [avg_add,avg_const_mul,hu]; · rw [mul_comm (seriesLex h o x z) _]; rfl
  all_goals repeat' first | apply Ready.mul | exact dye_ready _ | apply Ready.constant | exact hF | exact hH
lemma paint_ready (d : ℕ) (h : ℝ) (o : Site n) (p w : Pol G) : Ready (paint d h o p w) := by
  induction p using MvPolynomial.induction_on generalizing w
  case C c => unfold paint pairEval; simp only [MvPolynomial.eval₂Hom_C]; exact Ready.constant _
  case add p q hp hq => rw [paint_sum]; exact Ready.add (hp w) (hq w)
  case mul_X p z hp => rw [paint_x]; exact Ready.add (Ready.mul (hp w) (Ready.maker (fun k=> tame_scaleJet _ _))) (hp _)
lemma column_ready (h : ℝ) (o : Site n) (p : Pol G) : Ready (column d h o p) := paint_ready d h o p 1
@[simp] lemma column_unit (h : ℝ) (o : Site n) : column d h o (1:Pol G) = 1 := by ext x m; simp [column,paint,dye,pairEval,avg]

variable {I : Type} [DecidableEq I]
def product (cap : I→ℕ) (h : ℝ) (s : Finset I) (o : I→Site n) (q : I→Pol G) : JetArray (Coords G n) := ∏ i∈s,column (cap i) h (o i) (q i)
def amplitude (cap : I→ℕ) (h : ℝ) (s : Finset I) (o : I→Site n) (q : I→Pol G) := normalize (product cap h s o q)
lemma product_ready cap h s o (q : I→Pol G) : Ready (product (n:=n) cap h s o q) := Ready.prod (fun i _ => column_ready (d:=cap i) h (o i) (q i))
@[simp] lemma amplitude_unit (cap : I→ℕ) (h : ℝ) s (o : I→Site n) : amplitude cap h s o (fun _ => (1: Pol G)) = 1 := by
  rw [amplitude,product,show (∏ i ∈ s, column (cap i) h (o i) (1 : Pol G)) = (1 : JetArray _) by simp]; exact normalized_unit
end YM.Pert.Full
