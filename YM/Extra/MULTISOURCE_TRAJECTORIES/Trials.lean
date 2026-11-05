import YM.Extra.MULTISOURCE_TRAJECTORIES.Localization
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
/-!
# Several-source transport for whole cylinders, combinations and discrepancies

One array on the actual C.path, treating a possibly composite comparison as a
marker (no multiplying different signed estimates).

Doesn't prove the tuning or that
the resulting representations are sufficiently small at compatible stops.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Wilson RG Extraction Lattice Overlay Marker Mix Function Filter MeasureTheory Stock Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {H : History G} {N p j : ℕ} {V : Type} [DecidableEq V] {R : Census V}
namespace Insertions
variable (A : Insertions H V N p)

lemma reads (s : R.Mode) : Integrable (Ride.Product (H:=H) A.uses s) (law G _ (H.β N p N)) :=
  continuous_integrable _ (continuous_finsetProd _ fun i _ => (A.smooth i).continuous.comp matrixField_cont)



variable [Fintype V] [Nonempty V] (W : Windows (H.S.side j p))
    (o : V → Site (H.S.side j p)) (core : V → Support (H.S.side j p))




end Insertions

variable {C : Family G} {d : ℕ}
structure Cylinder (C : Family G) where
  stencil : Finset Cover
  contains : 0∈stencil
  field (N p : ℕ) (x : Site (C.side N p)) : Field G (C.side N p) → ℂ
  smooth (N p x) : ContDiff ℝ ∞ (field N p x)
  symm (N p x) : C.Makes → GaugeInvariant (field N p x ∘ matrixField)
  sites (N p x) : C.Makes → LocalOn (stencil.image (fun y => wrap (C.side N p) y+x)) (field N p x ∘ matrixField)

namespace Cylinder



def combine (a b : Cylinder C) (f : ℂ → ℂ → ℂ) (hf : ContDiff ℝ ∞ (uncurry f)) : Cylinder C where
  stencil := a.stencil ∪ b.stencil
  contains := Finset.mem_union_left _ a.contains
  field N p x U := f (a.field N p x U) (b.field N p x U)
  smooth N p x := hf.comp ((a.smooth N p x).prodMk (b.smooth N p x))
  symm N p x h t U := congrArg₂ f (a.symm N p x h t U) (b.symm N p x h t U)
  sites N p x h U W he := by
    refine congrArg₂ f (a.sites N p x h U W (agrees_mono he ?_)) (b.sites N p x h U W (agrees_mono he ?_)) <;> simp [Finset.image_union]






def scale (z : ℕ→ℕ→ℂ) (a : Cylinder C) : Cylinder C where
  stencil := a.stencil
  contains := a.contains
  field N p x := z N p • a.field N p x
  smooth N p x := (a.smooth N p x).const_smul (z N p)
  symm N p x h t U := congrArg (z N p • ·) (a.symm N p x h t U)
  sites N p x h U W he := congrArg (z N p • ·) (a.sites N p x h U W he)

def displaced (z : Cover) (a : Cylinder C) : Cylinder C where
  stencil := insert 0 (a.stencil.image (· + z))
  contains := Finset.mem_insert_self ..
  field N p x := a.field N p (x+ wrap _ z)
  smooth N p _ := a.smooth N p _
  symm N p _ h := a.symm N p _ h
  sites N p _ h U W he := by
    refine a.sites N p _ h U W (agrees_mono he ?_); intro i hi
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨s+z,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hs),by rw [map_add]; abel⟩

def read (z : Bid.Rowe C d) : Cylinder C where
  stencil := insert 0 (C.localSection d).stencil
  contains := Finset.mem_insert_self ..
  field N p x := observable C N p (z (N,p)) x
  smooth N p x := observable_smooth C N p d _ x
  symm N p x h := C.invariant h N p d _ x
  sites N p x _ U W he := by
    refine C.localO N p d _ x U W (agrees_mono he (Finset.coe_subset.mpr (Finset.image_subset_image (Finset.subset_insert ..))))





end Cylinder
end YM.Extra.Trajectories
