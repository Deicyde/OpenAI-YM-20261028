import YM.Extraction.Orders
import Mathlib.Analysis.Complex.Basic

/-! Local helpers for full sequence convergence. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension
open Filter Function
open scoped Topology BigOperators

def Arrives {X : Type*} [TopologicalSpace X] (f : ℕ → X) :=
  ∃ z, Tendsto f atTop (𝓝 z)

namespace Arrives

section top
variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : ℕ → X}

theorem copy (h : Arrives f) (he : f =ᶠ[atTop] g) : Arrives g :=
  let ⟨_,hk⟩ := h; ⟨_,hk.congr' he⟩

theorem post (h : Arrives f) {T : X → Y} (hx : Continuous T) : Arrives (fun n => T (f n)) :=
  let ⟨_,he⟩ := h; ⟨_, hx.continuousAt.tendsto.comp he⟩

theorem pair (h : Arrives f) {g : ℕ → Y} (he : Arrives g) : Arrives fun n => (f n,g n) := by
  obtain ⟨_,h⟩ := h; obtain ⟨_,he⟩ := he; exact ⟨_,h.prodMk_nhds he⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem columns {κ : ι → Type*} [∀ i, TopologicalSpace (κ i)] {f : ℕ → ∀ i, κ i}
    (h : ∀ i, Arrives fun n => f n i) : Arrives f := by
  choose z hz using h; exact ⟨z,tendsto_pi_nhds.mpr hz⟩

theorem upon (h : Arrives f) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop) : Arrives (f ∘ w) :=
  let ⟨_,hk⟩ := h; ⟨_,hk.comp hw⟩

theorem steady (v : X) : Arrives fun _ => v := ⟨_,tendsto_const_nhds⟩
end top

variable {ι X : Type*} {f g : ℕ → X}

theorem plus [Add X] [TopologicalSpace X] [ContinuousAdd X] (h : Arrives f) (he : Arrives g) :
    Arrives fun i => f i + g i := (h.pair he).post continuous_add

theorem times [Mul X] [TopologicalSpace X] [ContinuousMul X] (h : Arrives f) (he : Arrives g) :
    Arrives fun i => f i * g i := (h.pair he).post continuous_mul

theorem sum [AddCommMonoid X] [TopologicalSpace X] [ContinuousAdd X] (s : Finset ι) {f : ℕ → ι → X}
    (h : ∀ i ∈ s, Arrives fun n => f n i) : Arrives fun n => ∑ i ∈ s, f n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using steady (0:X)
  | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (h _ (Finset.mem_insert_self _ _)).plus (ih fun i hh => h i (Finset.mem_insert_of_mem hh))

theorem reci [NormedField X] (h : Arrives f) (hc : ∃ c : ℝ, 0<c ∧ ∀ᶠ i in atTop, c ≤ ‖f i‖) :
    Arrives fun i => (f i)⁻¹ := by
  obtain ⟨t,h⟩ := h; obtain ⟨c,hc,hh⟩ := hc
  exact ⟨_,h.inv₀ (norm_pos_iff.mp (hc.trans_le (ge_of_tendsto h.norm hh)))⟩
end Arrives
end YM.UVExtension
