import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Polydisc
import YM.PCalc.Band
import YM.Source.Construction

/-!
# G06: finite polynomial cylinders

`Slot.eval` is transported Lie curvature. Compute it as curvature of a
loop based at 0; matrix multiplication and inversion on G use polynomial
link entries with conjugates. Lie projection may be merely REAL-linear;
`entryPoly_functional` accounts for this explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.G06
open Lattice Wilson RG Source MvPolynomial
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {S : Finset Cover}

/-- Polynomial on the actual positive-link entries and conjugates of this stencil. -/
def EntryPoly (S : Finset Cover) (f : CoverConfig G → ℂ) :=
    ∃ Q : Formula G S, ∀ U, aeval (entry U) Q = f U

section algebra

variable {f g : CoverConfig G → ℂ}

private lemma ep_const (c : ℂ) : EntryPoly S (fun _ : CoverConfig G => c) :=
  ⟨C c, fun _ => by simp⟩

private lemma ep_add (a : EntryPoly S f) (b : EntryPoly S g) : EntryPoly S (fun U => f U + g U) := by
  obtain ⟨P,hP⟩ := a
  obtain ⟨Q,hQ⟩ := b
  exact ⟨P+Q, fun U => by rw [_root_.map_add,hP,hQ]⟩

private lemma ep_mul (a : EntryPoly S f) (b : EntryPoly S g) : EntryPoly S (fun U => f U * g U) := by
  obtain ⟨P,hP⟩ := a
  obtain ⟨Q,hQ⟩ := b
  exact ⟨P*Q, fun U => by rw [_root_.map_mul,hP,hQ]⟩

private lemma ep_sub (a : EntryPoly S f) (b : EntryPoly S g) : EntryPoly S (fun U => f U - g U) := by
  obtain ⟨P,hP⟩ := a
  obtain ⟨Q,hQ⟩ := b
  exact ⟨P-Q, fun U => by rw [_root_.map_sub,hP,hQ]⟩

private lemma ep_sum {ι : Type*} [Fintype ι] (f : ι → CoverConfig G → ℂ)
    (h : ∀ i, EntryPoly S (f i)) : EntryPoly S fun U => ∑ i, f i U := by
  unfold EntryPoly at h
  choose P hP using h
  exact ⟨∑ i,P i, fun U => by simp only [_root_.map_sum,hP]⟩

private lemma ep_entry (x : Source.Index G S) : EntryPoly S (fun U => entry U x) :=
  ⟨X x, fun _ => aeval_X ..⟩

lemma entryPoly_conj (a : EntryPoly S f) : EntryPoly S (fun U => star (f U)) := by
  obtain ⟨P,hP⟩ := a
  simp_rw [← hP]
  clear hP
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (ep_const (G:=G) (S:=S) (star c))
  | add p q hp hq =>
    simp only [_root_.map_add,star_add]
    exact ep_add hp hq
  | mul_X p x hp =>
    simp only [_root_.map_mul, star_mul, aeval_X]
    apply ep_mul _ hp
    rcases x with ⟨l,i,j,b⟩
    cases b
    · exact ep_entry (G:=G) (l,i,j,true)
    simpa [entry] using ep_entry (G:=G) (l,i,j,false)

lemma entryPoly_re (a : EntryPoly S f) : EntryPoly S (fun U => ((f U).re : ℂ)) := by
  simp_rw [Complex.re_eq_add_conj,div_eq_mul_inv]
  exact ep_mul (ep_add a (entryPoly_conj a)) (ep_const _)

lemma entryPoly_im (a : EntryPoly S f) : EntryPoly S (fun U => ((f U).im : ℂ)) := by
  simp_rw [Complex.im_eq_sub_conj,div_eq_mul_inv]
  exact ep_mul (ep_sub a (entryPoly_conj a)) (ep_const _)
end algebra

def GP (S : Finset Cover) (f : CoverConfig G → G.El) :=
  ∀ i j, EntryPoly S (fun U => G.mat (f U) i j)

variable {u v : CoverConfig G → G.El}

private lemma gp_mul (a : GP S u) (b : GP S v) : GP S (fun U => u U * v U) := by
  intro i j
  simp only [Gauge.mat_mul,Matrix.mul_apply]
  exact ep_sum _ fun k => ep_mul (a _ k) (b k _)

private lemma gp_inv (a : GP S u) : GP S (fun U => (u U)⁻¹) := by
  intro i j
  simp only [Gauge.mat_inv,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
  exact entryPoly_conj (a j i)

private lemma gp_walk (x : Cover) (w : Walk) (h : ∀ y ∈ visits x w, y ∈ S) :
    GP S (fun U : CoverConfig G => travel U x w) := by
  induction w generalizing x with
  | nil => intro i j; exact ep_const _
  | cons d w ih =>
    have ht (y) (hy : y ∈ visits (x+d.vec) w) : y ∈ S := h y (List.mem_cons_of_mem x hy)
    apply gp_mul _ (ih (x+d.vec) ht)
    have h₀ : x ∈ S := h _ List.mem_cons_self
    have h₁ : x+d.vec ∈ S := ht _ (by cases w <;> simp [visits])
    rcases d with ⟨l,_|_⟩
    · intro i j; exact ep_entry (⟨(x,l), h₀, h₁⟩,i,j,false)
    change GP S (fun U => (U (x-step l,l))⁻¹)
    apply gp_inv
    intro i j
    exact ep_entry (⟨(x-step l,l), by simpa [Step.vec, sub_eq_add_neg] using h₁, by simpa⟩,i,j,false)

/-- Compose with any real-linear functional on matrices. -/
theorem entryPoly_functional (φ : G.Mat →ₗ[ℝ] ℝ) (A : CoverConfig G → G.Mat)
    (h : ∀ i j, EntryPoly S (fun U => A U i j)) : EntryPoly S (fun U => (φ (A U) : ℂ)) := by
  have h₁ (i j : Fin G.repDim) (z : ℂ) :
      Matrix.single i j z = z.re • Matrix.single i j (1:ℂ) + z.im • Matrix.single i j Complex.I := by
    rw [Matrix.smul_single,Matrix.smul_single,← Matrix.single_add]
    simp [Complex.real_smul]
  have h₂ (U) : (φ (A U) : ℂ) =
      ∑ i, ∑ j, (((A U i j).re : ℂ) * (φ (Matrix.single i j 1) : ℂ) +
        ((A U i j).im : ℂ) * (φ (Matrix.single i j Complex.I) : ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (A U)]
    simp only [_root_.map_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h₁ i j (A U i j),_root_.map_add,map_smul,map_smul]
    simp
  -- rewrite just once on the entire function
  rw [funext h₂]
  refine ep_sum _ fun i => ep_sum _ fun j => ?_
  exact ep_add (ep_mul (entryPoly_re (h i j)) (ep_const _))
               (ep_mul (entryPoly_im (h i j)) (ep_const _))

/-- Actual Slot readout on Cover links is polynomial in the stated entry variables. -/
theorem entryPoly_slot (v : Slot) (hs : v.stencil ⊆ S) (i : G.ColorIndex) :
    EntryPoly S (fun U : CoverConfig G => (v.eval U i : ℂ)) := by
  let T := fun U : CoverConfig G => travel U 0 v.walk
  let V := fun U : CoverConfig G => faceValue U (v.offset,v.plaq)
  let M := fun U : CoverConfig G => T U * V U * (T U)⁻¹
  have ht : GP S T := gp_walk 0 v.walk fun y hy =>
    hs (Finset.mem_union_left _ (List.mem_toFinset.mpr hy))
  have hf : GP S V := gp_walk v.offset _ fun y hy =>
    hs (Finset.mem_union_right _ (List.mem_toFinset.mpr hy))
  have hm : GP S M := gp_mul (gp_mul ht hf) (gp_inv ht)
  let φ : G.Mat →ₗ[ℝ] ℝ := (PiLp.projₗ 2 _ i).comp G.projectColor
  have hv (U : CoverConfig G) : v.eval U i = φ ((1/2:ℝ) • (G.mat (M U) - G.mat (M U)⁻¹)) :=
    congr_arg (fun y : G.Color => y i) (G.curvature_conjugate (T U) (V U)).symm
  simp_rw [hv]
  apply entryPoly_functional
  intro j k
  -- note `mat (M U)⁻¹` here means `mat ((M U)⁻¹)`
  simp only [Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul]
  exact ep_mul (ep_const _) (ep_sub (hm j k) (gp_inv hm j k))

end YM.Work.G06
