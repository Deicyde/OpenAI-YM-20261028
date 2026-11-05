import YM.Extraction.Orders
import Mathlib.Topology.UniformSpace.Compact

/-!
# Producer for countably many numerical demands on a history

Real often-hidden hypotheses: fixed-period row tails for extracting *each* p;
not the same as doubly eventual. Clip values before compactness. Keep same
regulator; Order refinement only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter TopologicalSpace
open scoped Topology

variable {ι : Type*} [Countable ι] {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] [∀ i, FirstCountableTopology (X i)]

/-- One level of refinement for countably many eventually-bounded choices. -/
theorem simultaneous (T : ∀ i, ℕ → X i) {K : ∀ i, Set (X i)}
    (h : ∀ i, IsCompact (K i)) (H : ∀ i, ∀ᶠ j in atTop, T i j ∈ K i) :
    ∃ t : Sequence, ∃ y : ∀ i, X i, ∀ i, y i ∈ K i ∧ Tendsto (fun j => T i (t j)) atTop (𝓝 (y i)) := by
  classical
  have he : ∀ i, ∃ j, T i j ∈ K i := fun i => (H i).exists
  choose j hj using he
  let F (n : ℕ) (i : ι) := if T i n ∈ K i then T i n else T i (j i)
  have hw (n i) : F n i ∈ K i := by dsimp [F]; split_ifs <;> first | assumption | exact hj _
  obtain ⟨y,hy,s,hs,hS⟩ := (isCompact_pi_infinite h).tendsto_subseq (x := F) (fun j i => hw j i)
  refine ⟨⟨s,hs⟩,y,fun i => ⟨hy i, (tendsto_pi_nhds.mp hS i).congr' ?_⟩⟩
  filter_upwards [hs.tendsto_atTop.eventually (H i)] with k hk
  change F (s k) i = T i (s k); dsimp [F]; split_ifs ; simp_all

/-- Add countably many index data: inner compact set covers tails whenever p
is requested at that signature, period bounds here uniform in p (enough for outer compactness;
can be weakened). Inactive periods allowed arbitrary numbers. -/
theorem collect [∀ i, Nonempty (X i)] (f : Order) (A : ι → ℕ → Prop) (hf : ∀ i, ∀ᶠ k : ℕ in atTop, A i (f.per k))
    (T : ∀ i, ℕ → ℕ → X i) {K : ∀ i, Set (X i)} (h : ∀ i, IsCompact (K i))
    (H : ∀ i p, A i p → ∀ᶠ j in atTop, T i (f.mesh j) p ∈ K i) :
    ∃ g : Order, ∃ y : ∀ i, X i, ∀ i, y i ∈ K i ∧ (f.refine g).limits (A i) (T i) (y i) := by
  classical
  let JO := {p : ι × ℕ // A p.1 p.2}
  let α : JO → ι := fun a => a.1.1
  let B (v : JO) (j : ℕ) := T (α v) (f.mesh j) v.val.2
  obtain ⟨u,z,hZ⟩ := simultaneous (ι := JO) (X := fun i => X (α i)) B
    (K := fun w => K (α w)) (fun w => h _) (fun w => H _ _ w.property)
  let F (i : ι) (p : ℕ) := if e : A i p then (z ⟨(i,p),e⟩ : X i) else Classical.arbitrary (X i)
  have he (i p) (e : A i p) : F i p = z ⟨(i,p),e⟩ := dif_pos e
  obtain ⟨v,y,hv⟩ := simultaneous (fun i k => F i (f.per k)) h (fun i => by
    filter_upwards [hf i] with k hk; rw [he i (f.per k) hk]; exact (hZ ⟨(i,f.per k),hk⟩).1)
  refine ⟨⟨u,v⟩, y, fun i => ⟨(hv i).1, v.cofinal.eventually (hf i), F i, fun p hp => ?_, (hv i).2⟩⟩
  rw [he i p hp]
  exact (hZ ⟨(i,p),hp⟩).2
end YM.Extraction
