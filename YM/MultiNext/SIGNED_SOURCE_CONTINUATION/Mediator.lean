import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06

set_option warningAsError false

/-!
# Nonlinear transfer of moments via Faa di Bruno

Suffices to filter by total weight on an ordinary pullback F (real
finite jets). Formal partition step proved here. No global room required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Mediator
open Function Tensor Finset OrderedFinpartition
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]

def Axes (K : ℕ → Set E) {m : ℕ} (d : ℕ) (a : Fin m → ℕ) (u : Fin m → E) :=
    (∀ i,1 ≤ a i ∧ u i∈ K (a i)) ∧ ∑ i, a i ≤ d

def valence (K : ℕ → Set E) (d : ℕ) (f : E → X) := ∀ m : ℕ,∀ (a : Fin m → ℕ) (u : Fin m → E),
    Axes K d a u → iteratedFDeriv ℝ m f 0 u = 0

def curry (K : ℕ → Set E) (L : ℕ → Set F) (d : ℕ) (f : E → F) := ∀ m : ℕ,0 < m → ∀ (a : Fin m → ℕ) (u : Fin m → E),
    Axes K d a u → iteratedFDeriv ℝ m f 0 u ∈ L (∑ i,a i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma Axes.len {K : ℕ → Set E} {d m : ℕ} {a : Fin m→ℕ} {u : Fin m → E} (h : Axes K d a u) : m ≤ d :=
  le_trans (by simpa using sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) fun i _ => (h.1 i).1) h.2

private lemma atomic_of_length {n : ℕ} (c : OrderedFinpartition n) (h : c.length=n) : c = atomic n := by
  have he (i : Fin c.length) : c.partSize i = 1 := by
    have hv := c.sum_sigma_eq_sum (α:=ℕ) (fun _ => 1)
    simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hv
    exact ((sum_eq_sum_iff_of_le (s:=Finset.univ) (f:=fun _ => 1) (g:=c.partSize) (fun v _ => c.partSize_pos v)).mp
      (by simp [hv,h]) i (mem_univ i)).symm
  obtain ⟨l,w,y,e,i,J,d,hK⟩ := c; change l=n at h; subst l
  change ∀ i,w i=1 at he; replace he : w=(fun _ => 1) := funext he
  subst w
  let v : Fin n → Fin n := fun i => e i 0
  have hv : StrictMono v := J
  have ht : v=id := by
    let W : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv.injective)
    have hw := Fintype.sum_equiv W _ (fun i => (i:ℕ)) (show ∀ i : Fin n,(v i).val = (W i).val from fun _ => rfl)
    -- id_le uses WellFounded instance
    apply funext; intro i
    have hx : ∀ i : Fin n,(i:ℕ) ≤ (v i).val := fun i => hv.id_le i
    exact Fin.ext ((Finset.sum_eq_sum_iff_of_le (fun i _ => hx i)).mp hw.symm i (Finset.mem_univ i)).symm
  have he' : e=(fun i _ => i) := by
    funext t j; rw [Subsingleton.elim j 0]; exact congrFun ht t
  subst e; rfl

lemma attenuation {d : ℕ} (K : ℕ → Set E) (L : ℕ → Set F) (p : E → F) (f : F → X)
    (he : ContDiffAt ℝ d p 0) (hh : p 0=0) (hf : ContDiffAt ℝ d f 0)
    (hs : ∀ i : ℕ,0 < i → i ≤ d → ∀ v∈L i,∃ u∈K i, fderiv ℝ p 0 u=v) (hc : curry K L d p)
    (h : valence K d (f ∘ p)) : valence L d f := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a u hA
    have ht := hA.len
    choose V HV hV using fun i => hs (a i) (hA.1 i).1 ((single_le_sum (s:=Finset.univ) (f:=a) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hA.2) (u i) (hA.1 i).2
    have hx : Axes K d a V := ⟨fun i => ⟨(hA.1 i).1,HV i⟩,hA.2⟩
    have hK := h m a V hx
    rw [iteratedFDeriv_comp (hh.symm ▸ hf) he (Nat.cast_le.mpr ht), hh,FormalMultilinearSeries.taylorComp,_root_.sum_apply] at hK
    simp_rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries] at hK
    rw [sum_eq_single (atomic m)] at hK
    · change (iteratedFDeriv ℝ m f 0) (fun i => (iteratedFDeriv ℝ 1 p 0) (fun _ => V i))=0 at hK
      simpa only [iteratedFDeriv_one_apply,hV] using hK
    · intro i hi hl
      let c (x : Fin i.length) := ∑ k,a (i.emb x k)
      have hp (x' : Fin i.length) : Axes K d (fun k => a (i.emb x' k)) (V ∘ i.emb x') := by
        refine ⟨fun x => hx.1 _, le_trans ?_ hx.2⟩
        rw [← i.sum_sigma_eq_sum]
        exact single_le_sum (f:=c) (fun _ _ => Nat.zero_le _) (mem_univ x')
      have hl : i.length < m := lt_of_le_of_ne i.length_le (fun h => hl (atomic_of_length i h))
      refine ih _ hl c _ ⟨fun k => ⟨?_, hc _ (i.partSize_pos _) (a ∘ i.emb k) (V ∘ i.emb k) (hp k)⟩,?_⟩
      · letI : NeZero (i.partSize k) := ⟨(i.partSize_pos _).ne'⟩
        exact sum_pos (s:=Finset.univ) (f:=a ∘ i.emb k) (fun x _ => (hx.1 (i.emb k x)).1) Finset.univ_nonempty
      unfold c; rw [i.sum_sigma_eq_sum]; exact hx.2
    simp
end YM.MultiNext.SignedSource.Mediator
