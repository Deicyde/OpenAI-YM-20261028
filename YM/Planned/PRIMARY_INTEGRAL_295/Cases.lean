import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Analysis.Polydisc
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06

/-! # Accounts for the composition rule, using both degrees -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Cases
open Filter Function ContinuousMultilinearMap
open scoped ContDiff BigOperators Topology

variable {n : ℕ}

lemma finest (c : OrderedFinpartition n) (hs : c.length=n) : c=.atomic n := by
  have he : ∑ i : Fin c.length, c.partSize i = n := by simpa using c.sum_sigma_eq_sum (fun _ => (1:ℕ))
  cases c with
  | mk l size h e he' hm hd hc =>
    dsimp at *
    subst l
    have hS : size = fun _ => 1 := funext fun i => by
      by_contra! ht
      have hv : ∑ i : Fin n,(1:ℕ) < ∑ i : Fin n,size i :=
        Finset.sum_lt_sum (fun i _ => h i) ⟨i,Finset.mem_univ _,by have := h i;omega⟩
      simp [he] at hv
    subst size
    have H : StrictMono (fun i : Fin n => e i 0) := hm
    have hu : (fun i : Fin n => e i 0)=id := le_antisymm H.le_id H.id_le
    have hv : e=fun i _ => i := funext fun i => funext fun j => (congr_arg (e i) (Subsingleton.elim j 0)).trans (congr_fun hu i)
    subst e; rfl

/-- We sum the *input* engineering grades per part. -/
def costs (c : OrderedFinpartition n) (w : Fin n → ℕ) (i : Fin c.length) := ∑ j, w (c.emb i j)
lemma all (c : OrderedFinpartition n) (w : Fin n → ℕ) : ∑ i,costs c w i=∑ j,w j := c.sum_sigma_eq_sum w
lemma live (c : OrderedFinpartition n) {w : Fin n → ℕ} (h : ∀ j,0 < w j) (i : Fin c.length) : 0<costs c w i := by
  haveI : Nonempty (Fin (c.partSize i)) := ⟨⟨0,c.partSize_pos _⟩⟩
  exact Finset.sum_pos (fun _ _ => h _) Finset.univ_nonempty
lemma arity {w : Fin n → ℕ} (h : ∀ j, 0<w j) : n ≤ ∑ i,w i := by
  simpa using (Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ => (1:ℕ)) (g:=w) (fun i _ => h i))

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E→F} {g : F→G} {x : E}

def caseRead (c : OrderedFinpartition n) (g : F → G) (f : E → F) (x : E) (v : Fin n → E) :=
    iteratedFDeriv ℝ c.length g (f x) fun i => iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)

lemma compReads {m : WithTop ℕ∞} (hg : ContDiffAt ℝ m g (f x)) (hf : ContDiffAt ℝ m f x) (he : (n:WithTop ℕ∞) ≤ m) (v : Fin n → E) :
    iteratedFDeriv ℝ n (g ∘ f) x v = ∑ c : OrderedFinpartition n, caseRead c g f x v := by rw [iteratedFDeriv_comp hg hf he, FormalMultilinearSeries.taylorComp, _root_.sum_apply]; rfl

lemma one (g : F → G) (f : E → F) (x : E) (v : Fin n → E) :
    caseRead (.atomic n) g f x v = iteratedFDeriv ℝ n g (f x) fun i => fderiv ℝ f x (v i) := by
  change iteratedFDeriv ℝ n g _ (fun i => iteratedFDeriv ℝ 1 f x fun _ => v i) = _
  simp_rw [iteratedFDeriv_one_apply]
end YM.Planned.PrimaryIntegral295.Cases
