import YM.Pert.Lattice.Blank
/-! Subdiagram horizon compatibility before position conversion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Full
open Lattice Filter MeasureTheory Matrix Set Bare Labels Orb ProbabilityTheory
open Next.SectorChange.Gaussian
open scoped Topology BigOperators ENNReal Matrix.Norms.Frobenius
variable {G : Gauge} {d e : ℕ} {n : Side}
def within (p : Pol G) (d : ℕ) := ∀ i : Key G, i∈p.vars → i.1≤d
lemma height_le (p : Labels.Label G d) : within p.val d := by
  classical
  intro i hi
  obtain ⟨b,hb,hh⟩ := (MvPolynomial.mem_vars_iff_mem_support i).1 hi
  have h := (MvPolynomial.mem_restrictSupport_iff (R:=ℂ) (s:={x | Labels.height x ≤ d})).1 (show p.val∈limited G d from p.property.1) hb
  have ht := Finset.single_le_sum (f:=fun x => b x • generation x) (fun x _ => Nat.zero_le _) hh
  change height b ≤ d at h
  have hb' : b i ≠ 0 := Finsupp.mem_support_iff.1 hh
  calc
    i.1 ≤ b i • generation i := by change i.fst ≤ b i * _; grw [show b i ≥ 1 by omega]; simp [generation]
    _ ≤ Labels.height b := ht
    _ ≤ d := h

def embed (h : d≤e) (i : CosKey G d) : CosKey G e := ⟨i.val,i.property.trans h⟩
def sampler (G : Gauge) (h : d≤e) : Matrix (CosKey G d) (CosKey G e) ℝ := .of (fun i j => if embed h i=j then 1 else 0)
def shrink (h : d≤e) (x : Aux G e) : Aux G d := x ∘ embed h
@[simp] lemma sampler_vec (h : d≤e) (v : Aux G e) : sampler G h *ᵥ v= shrink h v := by
  funext i; simp [sampler, mulVec, dotProduct, ite_mul,shrink]
lemma recallKernel (h : d≤e) (a : ℝ) : (sampler G h) * shellCov G e a * (sampler G h).transpose = shellCov G d a := by
  ext i j
  simp [shellCov,sampler,mul_apply,ite_mul,mul_ite,embed]
lemma aux_shrink (h : d≤e) (a : ℝ) : MeasurePreserving (shrink (G:=G) h) (auxLaw G e a) (auxLaw G d a) := by
  simpa [AnalyticBridge.LocalGaussianLaws.Density.skim,auxLaw,recallKernel] using AnalyticBridge.LocalGaussianLaws.Density.gathered (shellCov_pos (G:=G) (d:=e) a) (sampler G h)
lemma ink_ext {i : Key G} (h : d≤e) (hp : i.1≤d) : ∀ v : Aux G e, ink v i = ink (shrink h v) i := fun v => by simp [ink,shrink,embed,hp,hp.trans h]
lemma auxiliary (h : ℝ) (p : Pol G) (o : Site n) (x) : column d h o p x = avg h (d:=d) (fun y => pairEval h o x y p) := by unfold column paint; simp_rw [show dye (1 : Pol G) = (1:JetArray (Aux G d)) from funext (fun v => show PowerSeries.C (MvPolynomial.eval (ink v) 1)=1 by simp),one_mul]
lemma compatible {p : Pol G} (r : d≤e) (hp : within p d) {x : Site n} (h : ℝ) : column d h x p=column e h x p := by
  funext c; ext k
  simp_rw [auxiliary,avg,PowerSeries.coeff_mk]
  change (∫ y : Aux G d, PowerSeries.coeff k (pairEval h x c y p) ∂auxLaw ..)=_
  rw [← (aux_shrink (G:=G) r h).map_eq,integral_map (aux_shrink r h).measurable.aemeasurable (by have he := (leg_ready h x c (d:=d) p k).1.aestronglyMeasurable (μ:=auxLaw G d h); rw [aux_shrink r h |>.map_eq]; exact he)]
  congr; funext v; congr 1
  exact MvPolynomial.eval₂Hom_congr' rfl (fun i hv _ => congrArg (fun w : ℂ => seriesLex h x c i + PowerSeries.C w) (ink_ext r (hp i hv) v).symm) rfl
lemma amplitude_agrees {I : Type} [DecidableEq I] {p q : I → ℕ} (f : I → Pol G) (r : Finset I) (hpq : ∀ i∈r,p i≤q i) (hp : ∀ i∈r,within (f i) (p i)) (h : ℝ) (x : I→Site n) : amplitude p h r x f = amplitude q h r x f := by
  unfold amplitude; apply congrArg _
  unfold product; refine Finset.prod_congr rfl (fun i hi => compatible (hpq i hi) (hp i hi) h)
lemma matches_labels {I : Type} [DecidableEq I] (p q : I → Bare.Insert G) (r : Finset I) (he : ∀ i∈r, (p i).cap ≤ (q i).cap) (hv : ∀ i∈r, (p i).pol=(q i).pol) (h : ℝ) (x : I→Site n) :
    amplitude (fun i => (p i).cap) h r x (fun i => (p i).pol) = amplitude (fun i => (q i).cap) h r x (fun i => (q i).pol) := by
  rw [amplitude_agrees (q:=fun i => (q i).cap) (fun i=> (p i).pol) r he (fun i _ => height_le ((p i).operator)) h x]; unfold amplitude product; apply congrArg _; exact Finset.prod_congr rfl fun i hi => congrArg _ (hv i hi)
end YM.Pert.Full
