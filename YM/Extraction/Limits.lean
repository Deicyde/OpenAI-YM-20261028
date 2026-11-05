import YM.Extraction.LatticeFamily
import YM.Extraction.Patch
import YM.Extraction.Orders

/-!
# Ordered extraction interface

Fundamental-cell lifted smearing with all tuples. Demand actual convergence
on every fixed p where the test is inside the comparison cell (eventual for
each test). See . `GridPoints` is *additional* generic-limit data;
treat separately so not inferred from smoothness on the infinite volume or
from mesh+volume limits of tests without equicontinuity. Grid lifts arbitrary
in cover, enabling statements at fixed-p seams; no ties for this port.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter MeasureTheory Lattice
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
namespace Order
variable (f : Order) (C : Family G) (S : Table C.book)

def cells {G : Gauge} (C : Family G) (N p : ℕ) {n : ℕ} (r : Fin n → Site (C.side N p)) := points fun i => C.S.place (r i)

def smears (N p : ℕ) {n : ℕ} (v : Fin n → C.book.Token) (t : Test n) :=
  (C.S.a N : ℂ)^(4*n) * ∑ r : Fin n → Site (C.side N p), t (cells C N p r) * C.numeric N p v r

/-- Mesh then volume, *same* C. Support of test bounded strictly inside
fundamental domain. No data is required for test support too near seam of a
small p. -/
structure Ordered : Prop where
  reads (n : ℕ) (v : Fin n → C.book.Token) (t : Test n) :
    f.limits (fun p => suitable C.S p t) (fun N p => smears C N p v t)
      (t.applyTo (fun x => S.read x v))

/-- Stability includes parameter-dependent mesh witnesses (don't choose
S for different uses). -/
theorem upon {f : Order} {C : Family G} {T : Table C.book} (h : f.Ordered C T) (g : Order) :
    (f.refine g).Ordered C T := ⟨fun n v t => retained (h.reads n v t)⟩

theorem full_read (h : f.Ordered C S) (n : ℕ) (d : Caps n) (v : C.book.Vector d) (t : Test n) :
    f.limits (fun p => suitable C.S p t)
      (fun N p => (C.S.a N : ℂ)^(4*n) * ∑ r : Fin n → Site (C.side N p), t (cells C N p r) * C.ensemble d r v)
      (S.integralOn d v t) := h.reads n (fun i => ⟨d i,v i⟩) t

theorem determined {T : Table C.book} (h : f.Ordered C S) (hp : f.Ordered C T) (hs : S.Smooth) (ht : T.Smooth)
    {n : ℕ} (v : Fin n → C.book.Token) : EqOn (fun x => S.read x v) (fun x => T.read x v) (conf n) :=
  (Test.unique_kernel (S.smooth_read hs v).continuousOn (T.smooth_read ht v).continuousOn).mp
    (fun t => f.unique _ _ (h.reads n v t) (hp.reads n v t))

def grid (N : ℕ) {n : ℕ} (r : Fin n → Cover) := points fun i => C.S.gridPoint N (r i)

/-- Local uniform form. All compact sets of the indicated patch; points in
K must already be lattice points (off lattice bounds by sequence or a
neighborhood extension are separate applications). -/
structure Meshes (P : ℕ → Table C.book) : Prop where
  continuous {n : ℕ} (p : ℕ) (v : Fin n → C.book.Token) :
    ContinuousOn (fun x => (P p).read x v) (Cyclic C.S p n)
  onK (p n : ℕ) (K : Set (Points n)) (h : IsCompact K) (hk : K ⊆ Cyclic C.S p n) (v : Fin n → C.book.Token) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, ∀ r : Fin n → Cover, grid C (f.mesh i) r ∈ K →
      ‖(C.numeric (f.mesh i) p v (fun j => wrap _ (r j))) - (P p).read (grid C (f.mesh i) r) v‖ < ε

def VolumePoints (P : ℕ → Table C.book) := ∀ n (K : Set (Points n)), IsCompact K → K ⊆ generic n →
    ∀ v : Fin n → C.book.Token, ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, ∀ x ∈ K,
      ‖(P (f.per i)).read x v - S.read x v‖ < ε

def PointLimits := ∃ P : ℕ → Table C.book, f.Meshes C P ∧ f.VolumePoints C S P

lemma point_retained (H : f.PointLimits C S) (g) : (f.refine g).PointLimits C S := by
  obtain ⟨P,H,V⟩ := H
  exact ⟨P, ⟨H.continuous, fun p n K h he v ε hε => g.mesh.cofinal.eventually (H.onK p n K h he v ε hε)⟩,
    fun n K HK he v ε hε => g.per.cofinal.eventually (V n K HK he v ε hε)⟩

theorem evaluated {P : ℕ → Table C.book} (H : Meshes f C P) (p n : ℕ)
    (v : Fin n → C.book.Token) (x : Points n) (hx : x ∈ Cyclic C.S p n) (r : ℕ → Fin n → Cover)
    (hr : Tendsto (fun i => grid C (f.mesh i) (r i)) atTop (𝓝 x)) :
    Tendsto (fun i => C.numeric (f.mesh i) p v (fun k => wrap _ (r i k))) atTop
      (𝓝 ((P p).read x v)) := by
  let Y := fun i => grid C (f.mesh i) (r i)
  let X (i : ℕ) := C.numeric (f.mesh i) p v (fun k => wrap _ (r i k))
  have ho := (cyclicOpen C.S p n).mem_nhds hx
  obtain ⟨K, hK,hk, hU⟩ := exists_compact_subset (cyclicOpen C.S p n) hx
  have he : Tendsto (fun i => (P p).read (Y i) v) atTop (𝓝 ((P p).read x v)) :=
    (((H.continuous p v x hx).continuousAt ho).tendsto.comp hr)
  have hu : Tendsto (fun i => X i - (P p).read (Y i) v) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [H.onK p n K hK hU v ε hε, hr.eventually (mem_interior_iff_mem_nhds.mp hk)] with i hi hx
    simp only [dist_zero_right]
    exact hi _ hx
  convert hu.add he using 1
  · simp
    rfl
  rw [zero_add]
end Order
end YM.Extraction
