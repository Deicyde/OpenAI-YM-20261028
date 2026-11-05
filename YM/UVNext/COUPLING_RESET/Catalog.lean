import YM.Push.BETA_TRANSPORT.Census
import YM.UVNext.COUPLING_RESET.Reset


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-! Inputs on the real dictionaries: methods to price continuity through the
implicit selection, and a fixed-label order-zero dial-change condition for
its quantitative inverse. These are additional producer responsibilities.
Using BETA_TRANSPORT on arbitrary curves into the two-variable template,
with no derivative requirements on the hard masks. -/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.BetaTransport RG Activities Shoot Wilson Lattice Filter Set Function
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side}

/-- Fixed-period local activity estimates, not scheduling or a bound just
on the evaluated exponential. Use e.g. `submajorized_of_majorizes` for the
tails if there's a common absolute list. Admits genuine further-subsequence
inputs where only those suffice. Not a refinement of the physical extraction. -/
structure Catalog (A : Template G n) (s t : Set ℝ) (δ w : ℝ) : Prop where
  valid : ∀ x ∈ s, ∀ u ∈ t, (A.terms x u).Valid A.p δ w
  paths : ∃ σ C Λ, A.path.Bounds A.clip σ C Λ
  reg : ∀ z ∈ s ×ˢ t, ∀ y ∈ s ×ˢ t, (uncurry A.terms z).reg = (uncurry A.terms y).reg
  forced : ∀ z ∈ s ×ˢ t, ∀ y ∈ s ×ˢ t, (uncurry A.terms z).forced = (uncurry A.terms y).forced
  each : ∀ z∈ s ×ˢ t, AtEach A.p (uncurry A.terms z) (uncurry A.terms) (𝓝[s ×ˢ t] z)
  tails : ∀ z∈ s ×ˢ t, Submajorized A.p (uncurry A.terms z) (uncurry A.terms) (𝓝[s ×ˢ t] z)

namespace Catalog
variable {A : Template G n} {s t u : Set ℝ} {δ w : ℝ} {f g base v : ℝ → ℝ}

lemma stable (h : Catalog A s t δ w) (hf : ContinuousOn f u) (hg : ContinuousOn g u) (hs : MapsTo f u s)
    (ht : MapsTo g u t) : StableActivities A.p (fun z => A.trial base (f z) (g z) (v z)) u := by
  have hm z (hz : z∈u) := ((hf.prodMk hg) z hz).tendsto_nhdsWithin (hs.prodMk ht)
  refine stable_from_census (fun z hz y hy => h.reg _ ((hs.prodMk ht) hz) _ ((hs.prodMk ht) hy))
    (fun z hz y hy => h.forced _ ((hs.prodMk ht) hz) _ ((hs.prodMk ht) hy))
    (fun z hz => (h.each _ ((hs.prodMk ht) hz)).map (hm z hz)) (fun z hz seq hq => ?_)
  exact h.tails _ ((hs.prodMk ht) hz) _ ((hm z hz).comp hq)

lemma along (V : Config G n) (h : Catalog A s t δ w) (hf : ContinuousOn f u) (hg : ContinuousOn g u) (hs : MapsTo f u s)
    (ht : MapsTo g u t) : ContinuousOn (fun z => A.add V (f z) (g z)) u := by
  obtain ⟨σ,C,Λ,hp⟩ := h.paths
  have hh : FixedRepData A.path A.clip A.p (fun z => A.trial 0 (f z) (g z) 0) u :=
    ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun z hz => ⟨σ,C,Λ,δ,w,hp,h.valid _ (hs hz) _ (ht hz)⟩⟩
  exact (hh.continuous_activities (h.stable (v:=fun _ => 0) hf hg hs ht) V).1
end Catalog

namespace Template
variable {A : Template G n} {x a b δ w κ : ℝ} {V : Config G n}

/-- Example producer-side dial-motion estimate: total change of unmasked
values with summable per-anchor prices proportional to the dial change, only
on the tested domain. No uniform continuity of K as a function of V here. -/
def varies (A : Template G n) (V : Config G n) (κ x a b : ℝ) :=
  ∃ p : ℕ → ℝ, (∀ i, 0 ≤ p i ∧ |(A.terms x b).E i V - (A.terms x a).E i V| ≤ p i * |b-a|) ∧
    ∀ o : Site n, SumBudget (fun i => if ((A.terms x a).reg i).site = o then p i else 0) κ

lemma motion (hV : flags A.p.threshold V = ∅) (ha : (A.terms x a).Valid A.p δ w) (hb : (A.terms x b).Valid A.p δ w)
    (hh : A.varies V κ x a b) : |A.add V x b-A.add V x a| ≤ (sites n * κ) * |b-a| := by
  obtain ⟨p,hp,ho⟩ := hh
  let c (o : Site n) i := if ((A.terms x a).reg i).site = o then p i else 0
  have he : p = fun i => ∑ o, c o i := funext fun _ => by simp [c]
  have hs : Summable p := he ▸ summable_sum fun o _ => (ho o).2.1
  have hB : ∑' i, p i ≤ sites n * κ := by
    rw [he,Summable.tsum_finsetSum fun o _ => (ho o).2.1]
    simpa [sites] using Finset.sum_le_sum (s:=Finset.univ) fun o _ => (ho o).2.2
  have hval (i : ℕ) : ‖(A.terms x b).regularOccurrence A.p i V-(A.terms x a).regularOccurrence A.p i V‖ ≤ p i * |b-a| := by
    have ht (z : ℝ) : Healthy A.p.threshold ((A.terms x z).reg i).support V := by simp [Healthy,hV]
    simp only [regularOccurrence, masked_eq _ _ _ _ (ht _),Real.norm_eq_abs]; exact (hp i).2
  have h := hs.mul_right |b-a|
  have ht := h.of_nonneg_of_le (fun i => norm_nonneg _) hval
  simp only [Template.add,additive,← ((ESeries hb).summable V).tsum_sub ((ESeries ha).summable V)]
  exact (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hval h).trans
    (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)))
end Template
end YM.UVNext.CouplingReset
