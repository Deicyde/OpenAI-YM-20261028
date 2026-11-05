import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.MULTISOURCE.Curves
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.PRICE_COMPILER.Post
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.TwoSided

set_option warningAsError false

/-!
# Fixed-dictionary one-source data
First helpers for continuation of E(15554--91) (engineering weight can be new).
Do not merge regular terms at unequal addresses and do not forget that masks
are part of the density, or that signed force is INSIDE the constrained gas.
We will not rechoose the Rep nor TransferData at any grade/translate/cutoff;
this product space is for constructing *new* comparison coefficients and
subtractions against the ones already stored there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
open Push.RelayDifference

variable {G : Gauge} {n : Side} {e : ℕ} {F : Frame G e} {R : Rep G n} {o : Site n} {A : Hol G}

abbrev GridU (n : Side) := ℕ → Support n
/-- Fix the *regular* support table separately (full forced table inherited from actual Rep).
Linear operations BELOW are only applied relative to that table. -/
abbrev Body (F : Frame G e) (n : Side) := F.Coeff × (ℕ → Config G n → ℂ) × (ℕ → Config G n → ℂ)
namespace Body
variable {U : GridU n} (D : Body F n)
def coord := D.1
def payload := D.2.1
def flag := D.2.2
def serves (U : GridU n) : Coefficient F n := ⟨coord D,U,payload D,flag D⟩

def unpack (k : Coefficient F n) : Body F n := ⟨k.x,k.regular,k.forced⟩


variable {D}
def Ok (o : Site n) (A : Hol G) (R : Rep G n) (U : GridU n) (D : Body F n) := (serves D U).Format o A R
def cap (o : Site n) (R : Rep G n) (U : GridU n) (D : Body F n) (κ r : ℝ) := (serves D U).remBound o R κ r
variable {κ r r' : ℝ}























section Dens
variable {α β δ Λ w : ℝ}

def density (D : Body F n) (o : Site n) (X : SectionData F) (R : Rep G n) (U : GridU n) :=
    (serves D U).density o X R

private lemma mask_linear (p : BudgetPoint) (X : Support n) : IsLinearMap ℂ (masked p.threshold X (G:=G) (X:=ℂ)) := by
  constructor <;> intros <;> funext V <;> (by_cases e : Healthy p.threshold X V <;> simp [e])

lemma density_add {E : Body F n} (h : cap o R U D κ r) (hh : cap o R U E κ r')
    (X : SectionData F) (H : R.Lawful α β Λ δ w) :
    density (D+E) o X R U = density D o X R U+density E o X R U := by
  let P (D : Body F n) := serves D U
  have he (v v' : F.Coeff) : X.places (F.scaled R.p.threshold⁻¹ (F.core (v+v'))) o =
                        X.places (F.scaled R.p.threshold⁻¹ (F.core v)) o+X.places (F.scaled R.p.threshold⁻¹ (F.core v')) o := by
    rw [map_add,map_add]; funext t
    exact congr_fun (X.eval_linear.map_add _ _) _
  funext V
  have hr : (∑' i,(P (D+E)).maskedTerm R i V)=(∑' i,(P D).maskedTerm R i V)+(∑' i,(P E).maskedTerm R i V) := by
    have e i : (P (D+E)).maskedTerm R i V=(P D).maskedTerm R i V+(P E).maskedTerm R i V :=
      congr_fun ((mask_linear _ _).map_add _ _) V
    simp_rw [e]; exact Summable.tsum_add ((Coefficient.regular_series h).summable V) ((Coefficient.regular_series hh).summable V)
  have hf : (∑' i,(P (D+E)).marked R i V)=(∑' i,(P D).marked R i V)+(∑' i,(P E).marked R i V) := by
    have e i : (P (D+E)).marked R i V=(P D).marked R i V+(P E).marked R i V := by
      unfold Coefficient.marked
      simp only [P,serves,flag,Prod.snd_add, Pi.add_apply,add_mul, Finset.sum_add_distrib]
      split <;> simp
    simp_rw [e]; exact Summable.tsum_add ((Coefficient.marked_series H h).summable V) ((Coefficient.marked_series H hh).summable V)
  let u (x : F.Coeff) := masked R.p.threshold (X.footprint o) (X.places (F.scaled R.p.threshold⁻¹ (F.core x)) o)
  have hv : (P (D+E)).exponentialEntry o X R V=(P D).exponentialEntry o X R V+(P E).exponentialEntry o X R V := by
    unfold Coefficient.exponentialEntry; rw [hr]
    change ((P D).x 0 + (P E).x 0) + u ((P D).x+(P E).x) _ + (_+_) = _+u _ _ + _+(_+u _ _+_)
    rw [show u ((P D).x+(P E).x)=u (P D).x+u (P E).x from ?_]; rw [Pi.add_apply]; abel
    unfold u; rw [he, (mask_linear R.p (X.footprint o)).map_add]
  change (P (D+E)).density o X R V=(P D).density o X R V+(P E).density o X R V
  unfold Coefficient.density; rw [hf,hv]; ring




end Dens
end Body
end YM.MultiNext.SignedSource
