import YM.MultiNext.VACUUM_STABILITY.Arrival.InputLaw
import YM.MultiNext.VACUUM_STABILITY.Gaussian.Foundation


set_option warningAsError false

/-!
# A specialization for paying `ProductCost`: use held sources throughout

If no contraction at this layer, all needed estimates can use the source letters as black
boxes at **fixed** U arguments. (For single-source contraction/history cut one may need
another organization and a consistency proof for the actual output.) Thus a smaller
quantitative input at an RG calculation in common with vacuum and single-source estimate.
Before multiplying in any scalar perturbations. Background estimates permit source arguments
in the calculation of held kernel and chart envelopes, INCLUDING indicator halos, use them
with same tags etc. Retain support rules independently of actual coefficient values. No use
of singleton truncations here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Holding
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Desk Component Component.Pasture Puff Stamp
open Arrival Arrival.Flock Tune Gauss
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I J V : Type} {G : Gauge} {n p : Side} (Q : Rep G n) (F : Flock V G n)

/-- Choose ANY large enough countable general atom type I. Separate alternatives at each
    thermal/hard input option, retaining the original option indices. Background terms
    including compulsory packets may require such input atoms to be present. -/
abbrev Station (I : Type) (F : Flock V G n) := I ⊕ ((Σ _ : Power V, ℕ) ⊕ (Σ _ : Cases F, ℕ))

def codon (q : Station I F) : Grade V := Sum.elim (fun _=>0) (Sum.elim (fun i => (F.penny i.1).name)
    fun i => (scrip F Q i.1).name) q

def reads (q : Station I F) : Config G n → ℂ := Sum.elim (fun _ _ => 1) (Sum.elim (fun i =>
    masked Q.p.threshold (pennyZone F i.1) (F.penny i.1).ink) fun i => (scrip F Q i.1).ink) q

section
variable [Fintype V]

def assay (q : Station I F) (z : V→ℂ) := Stamp.beat (codon Q F q) z • reads Q F q

lemma at_pressure (z : V→ℂ) (j : Σ _ : Power V,ℕ) : assay Q F (I:=I) (.inr (.inl j)) z=F.optional Q j.1 z := by
  ext1 U
  unfold assay codon reads Flock.optional; dsimp only [Sum.elim_inr,Sum.elim_inl]
  by_cases h : Healthy Q.p.threshold (F.pennyZone j.1) U <;> simp [h]
end

variable {B : Brush V G p}

/-- Output/pipeline tags. Assumes actual execution recovers & retains this data via Flow when
used; none of the fields below allow changing any branch of the vacuum representation. `L` from
Curves, purchases here allow dummy atoms but **also** locate them. -/
structure Table (R : Currency G n p) (A : Component.Pasture (Station I F) B) : Prop where
  charges i : A.hue i = codon Q F i
  enlarges (i : Σ _ : Power V,ℕ) : (pennyZone F i.1).image R.ratio.parent ⊆ A.sites (.inr (.inl i))
  gets (i : Σ _ : Cases F,ℕ) : (owes F Q i.1).zone.image R.ratio.parent ⊆ A.sites (.inr (.inr i))
  pricedL (i : Σ _ : Power V,ℕ) : R.Renewal (pennyZone F i.1) (A.sites (.inr (.inl i)))
  pricedH (i : Σ _ : Cases F,ℕ) : R.Renewal (owes F Q i.1).zone (A.sites (.inr (.inr i)))

-- multiply with the unmarked operator's per-atom issued weight. E1shape allows finite
-- poly losses from each (including powers held together, a single costed Power.penny). -/

def fit (F : Flock V G n) (f : Power V → ℝ) (g : Cases F → ℝ) (i : Station I F) : ℝ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun i => f i.1) fun i => g i.1) i

def priceAt (F : Flock V G n) (tax : Station I F→ℝ) (f : Power V→ℝ) (g : Cases F→ℝ) (i) := fit F f g i * tax i

structure Passable (R : Currency G n p) (A : Component.Pasture (Station I F) B) (tax : Station I F→ℝ)
    (k : ℕ) (e c : ℝ) : Prop where
  nonneg i : 0 ≤ tax i
  stored : Ac.Hit (fun i => A.sites (.inl i)) R.M (fun i => tax (.inl i)) R.strong c
  packets_light i : SumBudget (fun j => tax (.inr (.inl ⟨i,j⟩))) (e*R.polyRoot k (pennyZone F i))
  bins_light i : SumBudget (fun j => tax (.inr (.inr ⟨i,j⟩))) (e*R.polyRoot k (owes F Q i).zone)

namespace Passable
variable {F} {R : Currency G n p} {A : Component.Pasture (Station I F) B} {k : ℕ} {e c : ℝ} {tax : Station I F→ℝ}

lemma buys {f : Power V → ℝ} {g : Cases F → ℝ} {d t : ℝ} (h : Passable Q F R A tax k e c) (hm : Table Q F R A) (he : 0 ≤ e)
    (hf : Floats R (pennyZone F) f d) (hg : Floats R (fun i => (owes F Q i).zone) g t) (hF : ∀ i,0 ≤ f i)
    (hG : ∀ i,0≤g i) : Ac.Hit A.sites R.M (priceAt F tax f g) R.strong (c + (e * (R.scaleCost k*d) + e*(R.scaleCost k*t))) := by
  have ht := hf (fun i : Σ _ : Power V,ℕ => A.sites (.inr (.inl i))) k e (fun i => f i.1*tax (.inr (.inl i))) he hm.pricedL (fun i => by
    rw [mul_comm _ (f i)]; exact permit_mul (h.packets_light i) (hF i))
  have hu := hg (fun i : Σ _ : Cases F,ℕ => A.sites (.inr (.inr i))) k e (fun i => g i.1*tax (.inr (.inr i))) he hm.pricedH (fun i => by
    rw [mul_comm _ (g i)]; exact permit_mul (h.bins_light i) (hG i))
  intro x
  apply Absolute.union
  · simpa only [Function.comp_def,priceAt,fit,Sum.elim_inl,one_mul] using h.stored x
  apply Absolute.union
  · exact ht x
  exact hu x
end Passable

namespace Table
variable {F} {A : Component.Pasture (Station I F) B} {R : Currency G n p}
variable [Fintype V] {o : V → Site p} {k : V→ℝ} {κ : ℝ} {D : V→Pulse G n} {Y : Type*} {ref : V→Option Y}
  {X : V→ℕ→Support n}

-- Reading rule at ANY assembled z if actual source options in the atom complete support as required.
omit [Fintype V] in
lemma readouts (h : Table Q F R A) (hs : Attended F Q.p D (fun i => R.ratio.embed (o i)) k κ) (ht : Silent F ref X)
    (i : Station I F) (x) (hh : x∈(A.hue i).support) : if ref x=none then
          (∃ u, (X x u).image R.ratio.parent ⊆ A.sites i) ∨ (∃ q : Pack _,(D x).2 q ≠ 0 ∧ q.zone.image R.ratio.parent ⊆ A.sites i)
          else o x ∈ A.sites i := by
  rw [h.charges] at hh
  obtain i|i|j:= i
  · simp [codon] at hh
  · obtain ⟨⟨⟨v,a⟩,b⟩,j⟩:= i
    change x ∈ ((b+1) • spike v).support at hh
    have hv : x=v := by
      rw [Finsupp.mem_support_iff] at hh; by_contra hn
      exact hh (by simp [spike,show v ≠ x from Ne.symm hn])
    subst v
    let L := (pennyZone F ((x,a),b)).image R.ratio.parent
    have he := h.enlarges ⟨((x,a),b),j⟩
    split; rename_i hi
    · left; use a; have hw := (ht x hi).2; rw [←hw]; exact he
    have hw := ((hs.authorizations x).wears a).1
    exact he (mem_image.mpr ⟨_,hw,R.ratio.embed_parent _⟩)
  obtain ⟨i,k⟩:=j
  obtain i|⟨⟨v,a⟩,hb⟩:=i
  · simp [codon,scrip] at hh
  change x∈(spike v).support at hh; have he : x=v := by simpa [spike] using hh
  subst v
  let f : Augment F := ⟨(x,a),hb⟩
  have ht := h.gets ⟨Sum.inr f,k⟩
  have hg : (D x).2 a=(F x).d a := by rw [← hs.fact]; rfl
  split
  · exact Or.inr ⟨a,hg ▸ hb,ht⟩
  have ho := ((hs.authorizations x).bears a).2.1 hb
  exact ht (mem_image.mpr ⟨_,ho,R.ratio.embed_parent _⟩)
end Table
end YM.Multi.Vacuum.Holding
