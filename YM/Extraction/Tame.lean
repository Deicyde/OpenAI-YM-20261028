import YM.Extraction.Simultaneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Equicontinuity extraction on open patches

Do not require series producing points at coincidences or continuous interpolants.
Authors can supply `oscillation`, possibly from Lipschitz tails for the grid
inside a patch, and this module will extract all finite limits together.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter Metric TopologicalSpace
open scoped Topology BigOperators

variable {X : Type*} [MetricSpace X]

def oscillation (U : Set X) (S : ℕ → X → ℂ) := ∀ K : Set X, K ⊆ U → IsCompact K → ∀ ε : ℝ, 0 < ε →
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i : ℕ in atTop, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → dist (S i x) (S i y) < ε

lemma osc_pull {U : Set X} {S} (H : oscillation U S) (t : Sequence) : oscillation U (fun i => S (t i)) := by
  intro K h hk ε hε
  obtain ⟨u,hu,H⟩ := H K h hk ε hε
  exact ⟨u,hu,t.cofinal.eventually H⟩

structure Meets (U : Set X) (T : ℕ → X → ℂ) (S : X → ℂ) : Prop where
  continuousOn : ContinuousOn S U
  uniform (K : Set X) (h : K ⊆ U) (hk : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ x ∈ K, dist (T i x) (S x) < ε

variable [LocallyCompactSpace X]

lemma growFrom {U : Set X} (hU : IsOpen U) {T : ℕ → X → ℂ} (hO : oscillation U T)
    (D : Set X) (hD : Dense D) (h : ∀ x ∈ D ∩ U, CauchySeq (fun i => T i x)) : ∃ f, Meets U T f := by
  classical
  have hp (x) (hx : x ∈ U) : ∃ y : ℂ, Tendsto (fun i => T i x) atTop (𝓝 y) := by
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK, hu, hk⟩ := exists_compact_subset hU hx
    obtain ⟨q,hq,H⟩ := hO K hk hK (ε/4) (by positivity)
    obtain ⟨d, ⟨⟨hd,h1⟩,h₂⟩⟩ := hD.inter_open_nonempty (interior K ∩ ball x q)
      (isOpen_interior.inter isOpen_ball) ⟨x,hu,mem_ball_self hq⟩
    have hC := h d ⟨h₂,hk (interior_subset hd)⟩
    obtain ⟨r,hr⟩ := Metric.cauchySeq_iff.mp hC (ε/4) (by positivity)
    obtain ⟨m,hm⟩ := eventually_atTop.mp H
    refine ⟨max m r,fun i hi j hj => ?_⟩
    have hi' := hm i (by omega) x (interior_subset hu) d (interior_subset hd)
      (show dist x d < q by simpa [dist_comm x] using! (mem_ball.mp h1))
    have hj' := hm j (by omega) d (interior_subset hd) x (interior_subset hu) (mem_ball.mp h1)
    specialize hr i (by omega) j (by omega)
    have Ht := dist_triangle (T i x) (T i d) (T j x)
    have Hv := dist_triangle (T i d) (T j d) (T j x)
    change dist (T i d) (T j d) < _ at hr
    change dist (T i x) (T j x) < _
    linarith
  let f := fun x => if hx : x ∈ U then (hp x hx).choose else 0
  have hf (x) (hx : x ∈ U) : Tendsto (fun i => T i x) atTop (𝓝 (f x)) := by
    dsimp [f]; rw [dif_pos hx]; exact (hp x hx).choose_spec
  have ht (x) (hx : x ∈ U) : ContinuousAt f x := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K,hk,hu,hKU⟩ := exists_compact_subset hU hx
    obtain ⟨δ,hδ,H⟩ := hO K hKU hk (ε/2) (by positivity)
    filter_upwards [ball_mem_nhds x hδ,mem_interior_iff_mem_nhds.mp hu] with j hj hy
    have hhx := hf x hx; have hhJ := hf _ (hKU hy)
    have hh : dist (f j) (f x) ≤ ε/2 := le_of_tendsto (hhJ.dist hhx) (H.mono fun i hi =>
      (hi j hy x (interior_subset hu) (mem_ball.mp hj)).le)
    linarith
  refine ⟨f,⟨fun x hx => (ht x hx).continuousWithinAt,?_⟩⟩
  intro K h hk ε hε
  by_contra H
  have hfreq : ∃ᶠ i : ℕ in atTop, ∃ x ∈ K, ε ≤ dist (T i x) (f x) := by simpa [frequently_atTop] using H
  obtain ⟨g,hg, hg'⟩ := extraction_of_frequently_atTop hfreq
  choose x hx Hx using hg'
  obtain ⟨p,hp,G,hG,HG⟩ := hk.tendsto_subseq hx
  have hc := hG.tendsto_atTop
  have hy := hg.tendsto_atTop.comp hc
  have hu := h hp
  obtain ⟨t₁,ht₁, HH⟩ := hO K h hk (ε/4) (by positivity)
  have hw := Metric.tendsto_nhds.mp HG
  have h₁ : ∀ᶠ i in atTop, dist (T (g (G i)) (x (G i))) (T (g (G i)) p) < ε/4 := by
    filter_upwards [hy.eventually HH, hw t₁ ht₁] with i hi h'
    exact hi _ (hx (G i)) p hp h'
  have h₂ := Metric.tendsto_nhds.mp ((hf p hu).comp hy) (ε/4) (by positivity)
  have h₃ := Metric.tendsto_nhds.mp ((ht p hu).tendsto.comp HG) (ε/4) (by positivity)
  obtain ⟨i,hi,h',h''⟩ := (h₁.and (h₂.and h₃)).exists
  change dist (T _ _) (T _ _) < _ at hi
  change dist (T (g (G i)) p) (f p) < _ at h'
  change dist (f (x (G i))) (f p) < _ at h''
  have hv := Hx (G i)
  rw [dist_comm] at h''
  have he := dist_triangle (T (g (G i)) (x (G i))) (T (g (G i)) p) (f p)
  have hf := dist_triangle (T (g (G i)) (x (G i))) (f p) (f (x (G i)))
  linarith

/-- One choice for every component-level demand, using complex properness. -/
lemma localAscoli {ι : Type*} [Countable ι] (Y : ι → Type*) [∀ i, MetricSpace (Y i)] [∀ i, LocallyCompactSpace (Y i)]
    [∀ i, SecondCountableTopology (Y i)] (U : (i : ι) → Set (Y i)) (hU : ∀ i, IsOpen (U i))
    (T : ∀ i, ℕ → Y i → ℂ) (h : ∀ i, oscillation (U i) (T i))
    (H : ∀ i x, x ∈ U i → ∃ D : ℝ, ∀ᶠ j : ℕ in atTop, ‖T i j x‖ ≤ D) :
    ∃ t : Sequence, ∃ g : ∀ i, (Y i) → ℂ, ∀ i, Meets (U i) (fun j => T i (t j)) (g i) := by
  choose d hd hD using fun i => TopologicalSpace.exists_countable_dense (Y i)
  haveI (i : ι) : Countable ↥(d i ∩ U i) := (hd i).mono inter_subset_left
  let I := (i : ι) × ↥(d i ∩ U i)
  let F (p : I) (j : ℕ) := T p.1 j p.2.val
  choose C hC using fun (p : I) => H p.1 p.2.val p.2.property.2
  obtain ⟨s,v,H⟩ := simultaneous F (K := fun p => Metric.closedBall 0 (C p)) (fun _ => isCompact_closedBall ..)
    (fun p => by simpa [F] using hC p)
  choose f hf using fun i => growFrom (hU i) (osc_pull (h i) s) (d i) (hD i) fun x hx =>
      ((H ⟨i,x,hx⟩).2).cauchySeq
  exact ⟨s,f,hf⟩
end YM.Extraction
