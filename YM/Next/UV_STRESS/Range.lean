import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import YM.Bid.Fuels
import YM.Next.UV_STRESS.Across
import YM.Work.E01





/-!
# Terminal read bills from canonical coordinates at the actual History

In the lane for discrepancy norms (Grill and Shell), can consume exact
canonical Form alignment at terminal ℓ, mixed-only provisional growth, and
geometry, **instead of** assuming the full root cost (or full Radial). Still
trajectory level inputs, linked at application to Rep at SAME cutoff and period/gauges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {F : Extraction.Order}

open Relation
private def towards_origin (x : ℤ) := if 0<x then x-1 else if x=0 then 0 else x+1
private lemma lesser (k : ℕ) (x : Cover) (hx : x∈box (k+1)) :
    (towards_origin ∘ x)∈box k ∧ (towards_origin ∘ x)-x ∈ box 1 := by
  let p i := towards_origin (x i)
  have he i : - (↑k:ℤ) ≤ p i ∧ p i ≤ ↑k ∧ -1 ≤ p i-x i ∧ p i-x i ≤ 1 := by
    obtain ⟨hl,hu⟩:=box_test.mp hx; specialize hl i; specialize hu i
    unfold p towards_origin; split_ifs <;> omega
  exact ⟨box_test.mpr ⟨fun i => (he i).1,fun i => (he i).2.1⟩,
    box_test.mpr ⟨fun i => (he i).2.2.1,fun i => (he i).2.2.2⟩⟩

/-- Every canonical readout stencil with coverSize B beyond its fixed footprint
in native steps only pays one unit here. Include torus geometry (no volume
hit presumed). -/
lemma meters_cover {n : Side} (m : ℕ) (o : Site n) (S : Support n)
    (h : ∀ i∈S,separation i o ≤ m) : coverNumber m S ≤ 1 := by
  classical
  let X : Support n := {o}
  let R := halo m X
  let P := fun x y : Site n => x ∈ R ∧ y ∈ R ∧ separation x y ≤ 1
  have he x : x∈R ↔ separation x o≤m := by simp [R,X, halo_spec,separation_comm o]
  have hp (j) (hj : j ≤ m) (x : Cover) (hx : x∈box j) : wrap n x+o ∈ R := (he _).2 (by
    unfold separation; rw [add_sub_cancel_right]; exact (Work.E01.pdist_wrap_le hx).trans hj)
  have hh (j) (hj : j≤m) (x : Cover) (hx : x∈box j) : ReflTransGen P o (wrap n x + o) := by
    induction j generalizing x with
    | zero =>
      rw [show x=0 from funext (fun i => by have ha := (box_test.mp hx).1 i; have hb := (box_test.mp hx).2 i; change x i=0; omega), _root_.map_zero, zero_add]
    | succ j ih =>
      obtain ⟨hl,hr⟩ := lesser j x hx
      apply ReflTransGen.tail (b:=wrap n (towards_origin ∘ x)+o) (ih (by omega) _ hl)
      refine ⟨hp j (by omega) _ hl,hp _ hj _ hx,?_⟩
      unfold separation; rw [add_sub_add_right_eq_sub,← _root_.map_sub]; exact Work.E01.pdist_wrap_le hr
  have hy x (hx : x∈R) : ReflTransGen P o x := by
    let y := Lattice.lift (x-o)
    have he' : wrap n y+o=x := by simp [y]
    have ht (i) := (component_le (x-o) i).trans ((he x).1 hx)
    have hL (i) : -(↑m:ℤ)≤y i ∧ y i ≤ ↑m := by specialize ht i; unfold y; omega
    exact he' ▸ hh m le_rfl y (box_test.mpr ⟨fun i => (hL i).1,fun i => (hL i).2⟩)
  letI : Std.Symm P := ⟨fun i j hij => ⟨hij.2.1,hij.1,(separation_comm ..).le.trans hij.2.2⟩⟩
  have hf : covers m S X := ⟨fun i hi => (he _).2 (h _ hi), fun x hx y hY => (symm (hy x hx)).trans (hy y hY)⟩
  exact Nat.find_min' (covers_some m S) ⟨X,hf,Finset.card_singleton _⟩

variable {D k N p ℓ i : ℕ}
abbrev lenses (C : Family G) (m : ℕ) : BudgetPoint := C.path.levels.budget m

def stencil_at (m d : ℕ) := C.ref d ≤ m ∧ ((C.localSection d).stencil) ⊆ box (lenses C m).B
include C in
lemma light_cost (m : ℕ) {N p : ℕ} (hC : C.Makes) (o : Site (C.side m p)) (c : ℝ) (hc : 0≤c) (d : ℕ) (H : stencil_at C m d)
    (hN : m≤N) : (C.path.rep N p m).p.mass ((C.localSection d).footprint o) c ≤ Real.exp (lenses C m).supportExponent*c := by
  rw [(hC.wilson.represents N p m hN).vac]; apply mul_le_mul_of_nonneg_right _ hc
  have hp : coverNumber (lenses C m).B ((C.localSection d).footprint o) ≤ 1 := meters_cover _ o _ (fun j hj => by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 hj; unfold separation; rw [add_sub_cancel_right]
    exact Work.E01.pdist_wrap_le (H.2 hv))
  apply Real.exp_monotone; exact mul_le_of_le_one_right (lenses C m).exponent_pos.le (by exact_mod_cast hp)

-- Reading canonical PRIMARY chunks. Singleton calibration in Cut only.



def hx_chunk (m : ℕ) {N p : ℕ} (Z : Source.Coefficient (C.labels.level D) (C.side m p)) (o : Site (C.side m p))
    (j : Stones C D) :=
  let f := C.labels.level D
  let θ := (C.path.rep N p m).p.threshold
  (f.scaled θ⁻¹ (f.core Z.x) j) • (C.localSection D).places (piece C D j) o

abbrev slope_fee (A : BudgetPoint) := ((A.order:ℝ)+1)




end YM.Next.UVStress
