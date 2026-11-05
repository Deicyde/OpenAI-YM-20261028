import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ceils

/-!
# Principal windows (track geometry at both endpoints)

Use parametric stencil, principal compressed inverse inside each (NOT
recomputing Gram). Symmetric placement inherited (must choose invariantly);
separate start-address and support of local stencil. Ein  variant we'll
also use on interpolation for logdet. No INR exact near-singular dependencies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι κ ν : Type*} {c f : Side}

structure Window {ι : Type*} {c : Side} (a : ι → Site c) (B : ℕ) where
  take : ι → Finset ι
  here : ∀ i, i∈take i
  low : ∀ i j, separation (a i) (a j) ≤ B → i∈take j
  high : ∀ i j, i∈take j → separation (a i) (a j) ≤ B+2

namespace Window
variable {a : ι→Site c} {B : ℕ} (D : Window a B) [DecidableEq ι] [Fintype ι]
variable (A : Matrix ι ι ℝ)

/-- Principal submatrix. -/
def principal (i : ι) := A.submatrix (Function.Embedding.subtype (· ∈ D.take i)) (Function.Embedding.subtype (· ∈ D.take i))

/-- extend columns by zero, don't infer theoremhood from the nonsingular inverse default. -/
def pad : Matrix ι ι ℝ := Matrix.of (fun i j => if h : i∈D.take j then
    (D.principal A j)⁻¹ ⟨i,h⟩ ⟨j,D.here j⟩ else 0)

def error := A * D.pad A - 1

omit [Fintype ι] in
lemma inside (j : ι) (i : ↥(D.take j)) : D.pad A i j = (D.principal A j)⁻¹ i ⟨j,D.here j⟩ := by
  rw [pad,of_apply, dif_pos i.property]
omit [Fintype ι] in
lemma outside (i j : ι) (h : i∉D.take j) : D.pad A i j=0 := by rw [pad,of_apply,dif_neg h]
omit [Fintype ι] in
lemma thin : Thin a a (D.pad A) (B+2) := fun _ _ hij => D.outside _ _ _ (fun H => hij.not_ge (D.high _ _ H))
lemma stencil {w : ℕ} (h : Thin a a A w) : Thin a a (D.error A) (w+(B+2)) := by
  intro i j hij
  have he : i ≠ j := by intro hi; subst i; simp at hij
  rw [error,Matrix.sub_apply, h.mul (D.thin A) i j hij]; simp [he]

/-- No inner error even under derivative along an invertible-window curve. -/
lemma mileage (i j : ι) (h : i∈D.take j) (he : (D.principal A j)*(D.principal A j)⁻¹=1) : D.error A i j = 0 := by
  let p : ↥(D.take j) := ⟨i,h⟩; let k : ↥(D.take j) := ⟨j,D.here j⟩
  let R := D.principal A j
  have hx : (∑ m ∈ D.take j,A i m*D.pad A m j)=∑ m : ι,A i m*D.pad A m j := by
    apply Finset.sum_subset (Finset.subset_univ _); intro m _ hm; rw [D.outside _ _ _ hm,mul_zero]
  rw [error, Matrix.sub_apply, sub_eq_zero, Matrix.mul_apply,← hx,← sum_attach]
  calc
    _ = (R*R⁻¹) p k := by rw [Matrix.mul_apply]; apply sum_congr rfl; intro m _; rw [D.inside]; rfl
    _ = _ := by
      rw [he]
      by_cases h : i=j
      · have hp : p=k := Subtype.ext h; rw [hp,h]; simp
      have hp : p≠k := fun H => h (Subtype.ext_iff.mp H); simp [hp,h]

end Window
namespace Coat

variable {G : Gauge} {S : StepData c f}
/-- color-blind block windows with distance from either endpoint; E variant. -/
def frames (G : Gauge) (S : StepData c f) (B : ℕ) : Window (along (G:=G) S) B where
  take j := univ.filter (fun i => ∃ x∈ends S i.1, ∃ y∈ends S j.1, separation x y ≤ B)
  here i := mem_filter.mpr ⟨mem_univ _, _, center_end _,_, center_end _,by simp⟩
  low i j hij := mem_filter.mpr ⟨mem_univ _,_, center_end _,_, center_end _,hij⟩
  high i j hij := by
    obtain ⟨x,hx,y,hy,he⟩ := (mem_filter.mp hij).2
    have hp : separation (atEdge S i.1) x ≤ 1 := by rw [separation_comm]; exact stride _ hx
    have hk : separation y (atEdge S j.1) ≤ 1 := stride _ hy
    exact (separation_triangle (atEdge S i.1) x (atEdge S j.1)).trans ((add_le_add hp
      ((separation_triangle x y _).trans (add_le_add he hk))).trans (by omega))

lemma in_frame (i j : Tubular f G) {B : ℕ} : i∈(frames G S B).take j ↔
    ∃ x∈ends S i.1, ∃ y∈ends S j.1, separation x y ≤ B := by simp [frames]




end Coat
end YM.ConnectedActivityE6
