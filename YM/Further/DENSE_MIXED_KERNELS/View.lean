import YM.Further.DENSE_MIXED_KERNELS.Keyed
import YM.Further.DENSE_MIXED_KERNELS.Surface


/-!
# The view of a physical component

`View` specifies actual local data to use in a per-entry calculation.
One set of Gaussian coordinates on Free positions of the REAL slice (no
trunks), possibly omitting unused ones; Y/frozen still on Haar. NO assumptions
of correctness of component decomposition of the global sector integral:
those data are exactly the job of the provider, not a consequence of
these types. Use θ over whole predictor tags even for local functions;
if unused coordinates, e.g. off-support reads of U, are supplied by the
constructors, still check the complete-support hypotheses before assembly.

Advantage for applying to E: all marked arguments can be held, even ones
with nonsmooth U reads still in the integral. Must include their complete
mask, stencil, indicators etc when deciding which to hold. See View.probes
and later clients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Tree Port Gaussian Surface
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {A : ChartRatio G} {H : Port A} {m n : Side} {S : StepData m n}
    {F : Forest S.ratio}

abbrev Compass (G : Gauge) (S : StepData m n) {F : Forest S.ratio} (cold : Finset F.Free) :=
    Keyed S × (cold → G.El)

structure View (H : Port A) (F : Forest S.ratio) where
  J : Finset F.Free   -- held regular
  K : Finset F.Free   -- other (unheld) regular
  Y : Finset F.Free   -- frozen Haar used (padding with unused OK)
  separated : Disjoint J K
  frozen : Disjoint Y (J ∪ K)
  base : Config G m → Surface H J K (Compass G S Y)
  lean : Config G m → Compass G S Y → H.Room K
  way : Config G m → Compass G S Y → H.Bound K

namespace View
variable (V : View H F) (U : Config G m) (g : ℝ)
abbrev Frame := Compass G S V.Y
abbrev Before := V.Frame × H.front V.J (H.Room V.K)
abbrev After := V.Frame × H.back V.J (H.Room V.K)

def fare : Measure V.Frame := (Keyed.primary S).prod heldLaw
instance : IsProbabilityMeasure V.fare := by unfold fare; infer_instance

def inputs (r : V.Before) (i : F.Free) :=
    if h : i ∈ V.J then H.field g ((V.base U).mean r.1) ((V.base U).orient r.1) r.2.1 ⟨i,h⟩
    else if h : i∈V.Y then r.1.2 ⟨i,h⟩
    else if h : i∈V.K then H.field g (V.lean U r.1) (V.way U r.1) r.2.2 ⟨i,h⟩ else 1

def config (r : V.Before) := F.drape (V.inputs U g r)

/-- Can use only for the MARKED amplitude in this view. Doesn't supply
other values when the factors require them (those use `config` or need
other bindings). -/
def fixed (k : V.After) (i : F.Free) : G.El := if h : i∈ V.J then k.2.1 ⟨i,h⟩
    else if h : i∈V.Y then k.1.2 ⟨i,h⟩ else 1
def recover (p : V.After) := F.drape (V.fixed p)

lemma bunched : Measurable V.recover := by
  unfold recover; apply Measurable.comp F.continuous_drape.measurable
  unfold fixed; refine measurable_pi_lambda _ fun i => ?_
  split
  next h => exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  split
  next h => exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst)
  exact measurable_const

/-- Every potentially queried marked link of X (takes *augmentations*
as X, not just the old geometric support). -/
def Held (X : Support n) := ∀ i : F.Free, i.val.1 ∈ X → i.val.1 + Lattice.step i.val.2 ∈ X → i∈ V.J ∪ V.Y

theorem probes {X : Support n} (h : V.Held X) (p : V.Before) : Agrees X (V.config U g p) (V.recover ((V.base U).mapDown g p)) := by
  intro e he eh
  unfold config recover
  by_cases ht : e∈F.trunks
  · exact (F.on_tree _ ⟨e,ht⟩).trans (F.on_tree _ ⟨e,ht⟩).symm
  let i : F.Free := ⟨e,ht⟩
  trans V.inputs U g p i
  · exact F.off_tree _ i
  rw [show _ = V.fixed ((V.base U).mapDown g p) i from F.off_tree _ i]
  have hv := Finset.mem_union.mp (h i he eh)
  unfold fixed inputs
  by_cases hi : i∈ V.J
  · rw [dif_pos hi,dif_pos hi]; rfl
  have hI := hv.resolve_left hi
  rw [dif_neg hi,dif_neg hi,dif_pos hI,dif_pos hI]; rfl
end View
end YM.Further.DenseMixedKernels
