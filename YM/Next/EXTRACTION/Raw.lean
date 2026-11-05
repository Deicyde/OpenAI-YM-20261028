import YM.Next.EXTRACTION.Tails
import YM.Org.Theatre
import YM.Work.B04
import YM.Work.B06

/-!
# Selecting the raw hierarchy with auxiliary data

Use the fixed-period *and*
expanding-period finite-cutoff bounds in `CenterPort` to run the common
extraction.

At the same time (or once a raw limit has already been chosen)
include any given countable list of auxiliary numerical data.

They need only
*eventually* be in compact sets.

For the inner step, compact bounds are **per
period**, whenever that period is requested at the signature of the data.

For
the outer step use a separate `late` bound: one compact per signature for
sufficiently large periods on the selected period sequence, eventually in the
mesh index at each such period.

Neither sort of bound is inferred from the other. This is important for staged
uses, which may only establish certain bounds after period refinement (but for
which one may still need mesh limits on every fixed period!). This file does
not assert the bounds hold for data for which we have no estimate. The output
keeps all witnesses with the *same* refined mesh and period sequences.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Next.Extract
open Extraction Set Function Filter
open scoped Topology

/-- Explicit compact bounds for picking more ordered limits. An `i` can, for
example, stand for a choice of weights, weak scale and coefficient index.
`A i p` guards the mesh limit at p, e.g. when the test fits a comparison
cell; often just `True`. -/
structure Reserve {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (f : Order) (A : ι → ℕ → Prop)
    (T : ∀ i, ℕ → ℕ → X i) : Prop where
  uses (i) : ∀ᶠ k : ℕ in atTop, A i (f.per k)
  rows (i) (p) : A i p → ∃ K : Set (X i), IsCompact K ∧ ∀ᶠ j : ℕ in atTop, T i (f.mesh j) p ∈ K
  outer (i) : ∃ K : Set (X i), IsCompact K ∧ f.late fun N p => T i N p ∈ K

/-- Data retained in the two-stage extraction. In particular keep their inner
(mesh) limits `z` at *every* requested p, including p's not in `f.per`. -/
structure Keeps {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (f : Order) (A : ι → ℕ → Prop)
    (T : ∀ i, ℕ → ℕ → X i) (z : ∀ i, ℕ → X i) (y : ∀ i, X i) : Prop where
  uses (i) : ∀ᶠ k : ℕ in atTop, A i (f.per k)
  rows (i) (p) : A i p → Tendsto (fun j => T i (f.mesh j) p) atTop (𝓝 (z i p))
  outer (i) : Tendsto (fun j => z i (f.per j)) atTop (𝓝 (y i))

section
variable {ι : Type*} {X : ι → Type*} {f g : Order} {A : ι → ℕ → Prop}
variable {T : ∀ i, ℕ → ℕ → X i} {z : ∀ i, ℕ → X i} {y : ∀ i, X i}

/-- Norm bounds suffice for all the usual finite-dimensional data. -/
lemma Reserve.of_norm [∀ i, NormedAddCommGroup (X i)] [∀ i, ProperSpace (X i)]
    (ht : ∀ i, ∀ᶠ k : ℕ in atTop, A i (f.per k)) (hr : ∀ i p, A i p → ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ j : ℕ in atTop, ‖T i (f.mesh j) p‖ ≤ D) (h : ∀ i, ∃ D : ℝ, 0 ≤ D ∧ f.late fun N p => ‖T i N p‖ ≤ D) :
    Reserve f A T := by
  refine ⟨ht, fun i p hp => ?_, fun i => ?_⟩
  · obtain ⟨D, -, he⟩ := hr i p hp
    exact ⟨Metric.closedBall 0 D, isCompact_closedBall .., by simpa using he⟩
  obtain ⟨D, -, he⟩ := h i
  exact ⟨Metric.closedBall 0 D, isCompact_closedBall .., by simpa [Order.late] using he⟩

variable [∀ i, TopologicalSpace (X i)]

lemma Tails.reserve (h : Tails g f) (H : Reserve f A T) : Reserve g A T := by
  constructor
  · intro i
    exact h.per.holds _ (H.uses i)
  · intro i p hp
    obtain ⟨K,hK,hp⟩ := H.rows i p hp
    exact ⟨K,hK,h.mesh.holds (fun N => T i N p ∈ K) hp⟩
  intro i
  obtain ⟨K,hK,hp⟩ := H.outer i
  exact ⟨K,hK,h.late hp⟩

lemma Tails.keeps (h : Tails g f) (H : Keeps f A T z y) : Keeps g A T z y :=
  ⟨fun i => h.per.holds _ (H.uses i),
   fun i p hp => h.mesh.converges (fun N => T i N p) (H.rows i p hp),
   fun i => h.per.converges _ (H.outer i)⟩

lemma Keeps.limits (H : Keeps f A T z y) (i) : f.limits (A i) (T i) (y i) :=
  ⟨H.uses i, z i, H.rows i, H.outer i⟩

variable [Countable ι] [∀ i, FirstCountableTopology (X i)] [∀ i, T2Space (X i)]

/-- One actual mesh-then-period refinement for all of these data. No
first-countability requirement on `Order.fuse`; only use sequences here. -/
theorem Reserve.gather (H : Reserve f A T) : ∃ g : Order, ∃ z y, Keeps (f.refine g) A T z y := by
  classical
  let I := {ip : ι × ℕ // A ip.1 ip.2}
  let i (a : I) := a.val.1
  let p (a : I) := a.val.2
  choose K hK hr using fun a : I => H.rows (i a) (p a) a.property
  let B (a : I) (j : ℕ) := T (i a) (f.mesh j) (p a)
  obtain ⟨u,v,hv⟩ := simultaneous (ι := I) (X := fun a => X (i a)) B (K := K) hK hr
  let z (i : ι) (p : ℕ) : X i := if h : A i p then v (⟨(i,p),h⟩ : I) else T i 0 p
  have hm (i : ι) (p : ℕ) (h : A i p) : Tendsto (fun j => T i (f.mesh (u j)) p) atTop (𝓝 (z i p)) := by
    rw [show z i p = v (⟨(i,p),h⟩ : I) from dif_pos h]
    exact (hv ⟨(i,p),h⟩).2
  choose U hU hL using H.outer
  have ha (i : ι) : ∀ᶠ k : ℕ in atTop, z i (f.per k) ∈ U i := by
    have hx := hL i
    unfold Order.late at hx
    filter_upwards [hx,H.uses i] with k hk ha
    exact (hU i).isClosed.mem_of_tendsto (hm i (f.per k) ha) (u.cofinal.eventually hk)
  obtain ⟨w,y,hy⟩ := simultaneous (fun i k => z i (f.per k)) hU ha
  exact ⟨Order.mk u w,z,y,fun i => w.cofinal.eventually (H.uses i),hm,fun i => (hy i).2⟩
end

section Physical
variable {G : Gauge} {C : Family G} {f g : Order} {S : Table C.book} {M : ℕ → Table C.book}

lemma Tails.center (h : Tails g f) (H : CenterPort C f) : CenterPort C g := by
  refine ⟨?_,H.cells.all,?_⟩
  · intro v p
    filter_upwards [H.per v p] with m hm
    obtain ⟨D,hD,he⟩ := hm
    exact ⟨D,hD,h.mesh.holds (fun N => centeredBudget C v D m N p) he⟩
  intro d ε R he hr
  obtain ⟨m,hv,A,ha,W⟩ := H.cells.centered d ε R he hr
  exact ⟨m,hv,A,ha,fun i hi t ht => h.late (W i hi t ht)⟩

lemma Tails.raw (h : Tails g f) (H : RawLimits C f S M) : RawLimits C g S M := by
  refine ⟨H.regular,⟨H.mesh.continuous,?_⟩, ?_, ⟨fun n v t => h.limits (H.integral.reads n v t)⟩⟩
  · intro p n K hk hh v ε hε
    apply h.mesh.holds (fun N => ∀ r : Fin n → Lattice.Cover, Order.grid C N r ∈ K →
      ‖C.numeric N p v (fun j => Lattice.wrap _ (r j)) - (M p).read (Order.grid C N r) v‖ < ε)
    exact H.mesh.onK p n K hk hh v ε hε
  intro n K hk he v ε hε
  apply h.per.holds (fun p => ∀ x ∈ K, ‖(M p).read x v - S.read x v‖ < ε)
  exact H.volume n K hk he v ε hε

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [Countable ι]
variable [∀ i, FirstCountableTopology (X i)] [∀ i, T2Space (X i)] {A : ι → ℕ → Prop} {T : ∀ i, ℕ → ℕ → X i}

/-- Refine an already produced raw surface to add countably many data after
establishing cutoff bounds for them. Keeps the same limiting tables even off
the generic sets (where no point convergence is claimed). -/
theorem gather_after_raw (h : RawLimits C f S M) (H : Reserve f A T) :
    ∃ g : Order, RawLimits C (f.refine g) S M ∧ ∃ z y, Keeps (f.refine g) A T z y := by
  obtain ⟨g,z,y,hg⟩ := H.gather
  exact ⟨g,(Tails.refine f g).raw h,z,y,hg⟩

/-- Produce a raw limit from centered bounds, retaining all auxiliary
numerical data for which we have explicit bounds. `RawLimits` keeps actual
ordered limits of fixed finite families of Wilson moments on `Cyclic` /
`generic` (point) and for compact smooth tests supported in configuration
space on all `suitable` periods (Lebesgue smears, normalization
`a_N^(4*n)` for n slots). It includes arities zero and one. It does not give
point limits at axis ties. Same `C` throughout. -/
theorem raw (h : C.Makes) (c : CenterPort C f) (H : Reserve f A T) :
    ∃ g : Order, ∃ S M, RawLimits C (f.refine g) S M ∧ ∃ z y, Keeps (f.refine g) A T z y := by
  obtain ⟨g₀,S,M,hg⟩ := Extraction.crops h c
  obtain ⟨g',hw,z,y,he⟩ := gather_after_raw hg ((Tails.refine _ _).reserve H)
  exact ⟨g₀.refine g',S,M,hw,z,y,he⟩
end Physical
end YM.Next.Extract
