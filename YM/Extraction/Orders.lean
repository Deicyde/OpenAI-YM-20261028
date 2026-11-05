import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Mesh before period

Mesh common to ALL periods. Not `Tendsto` along a single diagonal (p,N_p).
Use tails (`late`) or actual *two* ordinary Tendsto's (`limits`)
and prove stability when refining. This ports also to numerical data using the same
`Order`. Condition `A p` means that the test is supported inside p, etc.; we demand
it is eventually met on the period sequence when asking for this limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter
open scoped Topology BigOperators

structure Sequence where
  choose : ℕ → ℕ
  monotone : StrictMono choose
instance : CoeFun Sequence (fun _ => ℕ → ℕ) := ⟨fun k => k.choose⟩

def Sequence.after (s t : Sequence) : Sequence := ⟨s ∘ t, s.monotone.comp t.monotone⟩

def Sequence.full : Sequence := ⟨id,fun _ _ h => h⟩

@[simp] theorem Sequence.after_apply (s t : Sequence) (n : ℕ) : s.after t n = s (t n) := rfl
@[simp] theorem Sequence.full_apply (n : ℕ) : Sequence.full n = n := rfl

theorem Sequence.cofinal (s : Sequence) : Tendsto s atTop atTop := s.monotone.tendsto_atTop

structure Order where
  mesh : Sequence
  per : Sequence

namespace Order

def refine (f g : Order) := Order.mk (f.mesh.after g.mesh) (f.per.after g.per)

def full := Order.mk .full .full

/-- Some downstream comparisons only ask for eventuality, for instance an
ε relaxation to an estimated bound. Period threshold first, then cutoff threshold
which may depend on fixed period. -/
def late (f : Order) (A : ℕ → ℕ → Prop) := ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop, A (f.mesh j) (f.per k)

theorem late_refine (f g : Order) {A} (h : f.late A) : (f.refine g).late A := by
  refine g.per.cofinal.eventually (?_ : ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop, A (f.mesh (g.mesh j)) (f.per k))
  exact (show ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop, A (f.mesh j) (f.per k) from h).mono fun k he =>
    g.mesh.cofinal.eventually he

/-- Do not use a totalized Limsup bound as a number without knowing the appropriate boundedness.
Prefer this filter predicate. -/
def upper (f : Order) (A : ℕ → ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → f.late fun N p => A N p ≤ c + ε

variable {X : Type*} [TopologicalSpace X]

def limits (f : Order) (A : ℕ → Prop) (W : ℕ → ℕ → X) (x : X) := (∀ᶠ k : ℕ in atTop, A (f.per k)) ∧
  ∃ v : ℕ → X,
    (∀ p, A p → Tendsto (fun j => W (f.mesh j) p) atTop (𝓝 (v p))) ∧
    Tendsto (fun k => v (f.per k)) atTop (𝓝 x)

theorem retained {f g : Order} {A W} {x : X} (h : f.limits A W x) : (f.refine g).limits A W x := by
  obtain ⟨ht,v,hv,H⟩ := h
  exact ⟨g.per.cofinal.eventually ht,v,(fun i hi => (hv i hi).comp g.mesh.cofinal),H.comp g.per.cofinal⟩

theorem unique [T2Space X] (f : Order) (A) (W) {x y : X} (hx : f.limits A W x) (hy : f.limits A W y) : x=y := by
  obtain ⟨ht,v,hV,H⟩ := hx
  obtain ⟨-,w,hW,K⟩ := hy
  refine tendsto_nhds_unique (f := fun k => w (f.per k)) (H.congr' ?_) K
  filter_upwards [ht] with k hk; exact tendsto_nhds_unique (hV _ hk) (hW _ hk)

theorem neighborhood {f : Order} {A W} {x : X} (h : f.limits A W x) {s : Set X} (hs : s ∈ 𝓝 x) :
    f.late fun N p => W N p ∈ s := by
  obtain ⟨u,h₁,h₂,h₃⟩ := mem_nhds_iff.mp hs
  obtain ⟨ht,v,hV,H⟩ := h
  unfold late
  filter_upwards [ht,H.eventually (h₂.mem_nhds h₃)] with k hk hw
  exact (hV _ hk).eventually (mem_of_superset (h₂.mem_nhds hw) h₁)

/-- When mesh row limits are already included, eventuality implies the claimed ordinary limit.
X regular to shrink neighborhoods. -/
theorem from_late [RegularSpace X] {f : Order} {A : ℕ → Prop} (ht : ∀ᶠ k : ℕ in atTop, A (f.per k))
    {W : ℕ → ℕ → X} (v : ℕ → X) (hV : ∀ p, A p → Tendsto (fun j => W (f.mesh j) p) atTop (𝓝 (v p)))
    {x : X} (he : ∀ s ∈ 𝓝 x, f.late fun N p => W N p ∈ s) : f.limits A W x := by
  refine ⟨ht,v,hV,?_⟩
  apply tendsto_def.mpr
  intro s hs
  obtain ⟨u,U₁,U₂,U₃⟩ := exists_mem_nhds_isClosed_subset hs
  have H := he u U₁; unfold late at H
  filter_upwards [ht,H] with k hk h
  exact U₃ (U₂.mem_of_tendsto (hV _ hk) h)
end Order
end YM.Extraction
