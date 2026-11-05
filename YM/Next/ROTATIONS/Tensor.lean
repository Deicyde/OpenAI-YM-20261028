import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import YM.Compact.Borel
import YM.Distribution.Product
import YM.OS.Schwinger

/-!
# Spectral test constants. `Sheet` here is product Schwartz only; no general
claim about global momentum values.
-/
noncomputable section
namespace YM.Outer
open MeasureTheory Measure Filter Set Function Complex Boundary Probe OS 
open scoped BigOperators Topology InnerProductSpace ContDiff NNReal ENNReal ComplexOrder

abbrev Form := Probe ℝ
abbrev Panels := Axis → Form
abbrev Tang := SpaceAxis → ℝ

def assembleL (n : ℕ) : (Fin (n+1) → ℝ) ≃L[ℝ] ℝ × (Fin n→ℝ) := LinearEquiv.toContinuousLinearEquiv {
  toFun w := (w 0, fun i => w i.succ)
  invFun w := Fin.cons w.1 w.2
  left_inv w := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv w := by apply Prod.ext; · simp
                    funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl }

def tensorN (n : ℕ) (f : Fin n → Form) : Probe (Fin n→ℝ) :=
  match n with
  | 0 => (HasCompactSupport.of_compactSpace (f:=fun _ : Fin 0→ℝ => (1:ℂ))).toSchwartzMap contDiff_const
  | k+1 => along (assembleL k) (Probe.combine (f 0) (tensorN k (Fin.tail f)))

lemma tensorN_at (n) (f) (x) : tensorN n f x=∏ i, f i (x i) := by
  induction n with
  | zero => rw [Finset.univ_eq_empty,Finset.prod_empty];rfl
  | succ k ih => rw [tensorN,along_at,combine_at,ih,Fin.prod_univ_succ]; rfl

def tensor (f : Panels) : Probe E4 := along (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis => ℝ)) (tensorN 4 f)
lemma tensor_at (f : Panels) (x : E4) : tensor f x= ∏ i,f i (x i) := tensorN_at 4 f x.ofLp

/-- Put time i. -/
def make (i : Axis) : ℝ × Tang ≃ᵐ E4 :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm.trans (MeasurableEquiv.toLp 2 _)

lemma make_time (i : Axis) (x : ℝ × Tang) : make i x i = x.1 := i.insertNth_apply_same (α:=fun _ => ℝ) x.1 x.2
lemma make_other (i : Axis) (x : ℝ × Tang) (j : SpaceAxis) : make i x (i.succAbove j) = x.2 j := i.insertNth_apply_succAbove (α:=fun _ => ℝ) x.1 x.2 j

lemma make_pres (i : Axis) : MeasurePreserving (make i) :=
  (PiLp.volume_preserving_toLp Axis).comp (volume_preserving_piFinSuccAbove _ i).symm

def elsewhere (i : Axis) (x : Tang) : Cross i := ⟨make i (0,x), make_time ..⟩
lemma make_eq (i) (t : ℝ) (x : Tang) : make i (t,x)= t • basis i+(elsewhere i x).val := by
  apply PiLp.ext; intro j
  by_cases hj : j=i
  · subst j; simp [make_time,elsewhere]
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp [make_other,elsewhere,i.succAbove_ne k]

lemma make_mirror (i) (t : ℝ) (x : Tang) : Ortho.move (Signed.reflect i) (make i (t,x))=make i (-t,x) := by
  apply PiLp.ext; intro j
  by_cases hj : j=i
  · subst j; simp [make_time]
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
  simp [i.succAbove_ne,make_other]

def part (i : Axis) (p : E4) (j : SpaceAxis) := p (i.succAbove j)
def tests (f : Panels) (i : Axis) (x : Tang) := ∏ j, f (i.succAbove j) (x j)
def reading (i : Axis) (f : Panels) (p : E4) := tests f i (part i p)

lemma tensor_made (f : Panels) (i : Axis) (t : ℝ × Tang) : tensor f (make i t)= f i t.1 * tests f i t.2 := by
  rw [tensor_at,Fin.prod_univ_succAbove _ i]; unfold tests; simp [make_time,make_other]
lemma tests_update (f : Panels) (i h) : tests (update f i h) i=tests f i := by
  ext1; unfold tests; simp [Fin.succAbove_ne]
lemma tensor_update (f : Panels) (i : Axis) (h) (p : E4) : tensor (update f i h) p=h (p i)*reading i f p := by
  rw [tensor_at,Fin.prod_univ_succAbove _ i]; unfold reading part tests; simp [Fin.succAbove_ne]

lemma tests_int (f : Panels) (i : Axis) : Integrable (tests f i) (volume : Measure Tang) :=
  Integrable.fintype_prod (μ:=fun _ => volume) (fun j => (f (i.succAbove j)).integrable)

lemma wave_prod (i : Axis) (x : Tang) (p : E4) : plane p (elsewhere i x).val=∏ j,plane (p (i.succAbove j)) (x j) := by
  unfold plane; rw [PiLp.inner_apply,Fin.sum_univ_succAbove _ i]; simp only [elsewhere,make_time,inner_zero_right,
    zero_add, make_other, ofReal_sum, Finset.sum_mul, Complex.exp_sum]

def positionTest (f : Panels) : Probe E4 := tensor fun i => hat (f i)

lemma tensor_wave (f : Panels) (p : E4) (i : Axis) :
    ∫ x : Tang,plane p (elsewhere i x).val * tests (fun i => hat (f i)) i x = ((pref ℝ)^3:ℝ) • reading i f p := by
  have hu (j : Axis) : (∫ x : ℝ,plane (p j) x * hat (f j) x)=pref ℝ • f j (p j) := by
    simp_rw [plane_dot (p j)]; exact positiveFourier ..
  simp_rw [wave_prod i]; unfold tests reading part
  simp_rw [← Finset.prod_mul_distrib]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (f:=fun j x => plane (p (i.succAbove j)) x * hat (f _) x)]
  simp_rw [hu]; unfold tests; simp [Complex.real_smul, Finset.prod_mul_distrib]
end YM.Outer
