import YM.Further.DENSE_MIXED_KERNELS.Street
import YM.Further.DENSE_MIXED_KERNELS.Stroke
import YM.Further.DENSE_MIXED_KERNELS.Tarpaulin

/-!
# Towards use of the dense mixed entries at actual addresses

Encode in caller's Alphabet.

Whole construction still has to retain
modes admissible, attach output cut to THESE histories, match the
real contour orientations, and buy an actual dense `power` gate with
booked/queue sacrifices, all clocks funded.

These are per-entry purchase
and representation rules *including proof that the raw mixed input
selection sum over vacuum K partners really works here*, not just tests.

Only call on allocations legitimate for this step including rest of
alphabet.

Can
for example permit this label only for some nonempty selections, retaining
calibrations to vacuum/unaffected labels elsewhere provided checked with
Lane etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona Overlay Extra.Multi Labels Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical NNReal ENNReal
variable {c f : Side} {G : Gauge} {A : ChartRatio G} {H : Port A}
    {S : StepData c f} {F : Forest S.ratio} {x W γ σ σ' C C' Λ Λ' δ δ' w w' : ℝ}
    {R : Rep G f} {P : Rep G c} {T : Tube G S} {V α β I : Type} [DecidableEq V] {L : Census V}
    {D : Bands L R} {X : Chain (α⊕β)} {ρ : α→Pieces} {o : X.Index} {Y : Stores S}

namespace Throng
-- ONE old step length with unmarked density read THROUGH ALL of sector
structure Associates (X : Chain (α⊕β)) (ρ : α→Pieces) where
  wherePack : X.Index
  packet : β
  source (j : {a : X.Index // a ≠ wherePack}) : α
  Hs : Finset ℕ
  Ks : Finset ℕ
  recipe : ℕ → ℕ
  banner : X.2 wherePack=Sum.inr packet
  bills : ∀ j, X.2 j.val=Sum.inl (source j)
  distinct : Injective (fun i => ρ (source i))
  all : univ.image (fun i => ρ (source i)) = Hs.disjSum (Ks.image (fun j => (j,recipe j)))

namespace Associates
variable (a : Associates X ρ)
include a

lemma belongs : Injective X.2 := by
  intro i j hx
  by_cases hi : i=a.wherePack
  · by_contra hv; subst i; rw [a.banner,a.bills ⟨j,Ne.symm hv⟩] at hx; contradiction
  by_cases hj : j=a.wherePack
  · subst j; rw [a.banner, a.bills ⟨i,hi⟩] at hx; contradiction
  rw [a.bills ⟨i,hi⟩, a.bills ⟨j,hj⟩] at hx
  exact congr_arg (fun i => i.val) (a.distinct <| congr_arg ρ (Sum.inl.inj hx))

lemma denominator : oneWord X=1 := by
  let Y := catalog X
  have he : Y.Nodup := Multiset.Nodup.map a.belongs (Finset.nodup univ)
  have hv (i : α ⊕ β) (hv : i∈Y.toFinset) : (Y.count i).factorial=1 := by
    rw [Multiset.count_eq_one_of_mem he (Multiset.mem_toFinset.mp hv)]; rfl
  have hp : Numbered.divisor Y=1 := by
    have hx : ∏ j∈Y.toFinset,(Y.count j).factorial=1 := prod_eq_one hv
    unfold Numbered.divisor; convert hx using 1; congr!
  unfold oneWord; change ((Numbered.divisor Y:ℝ))⁻¹=_; rw [hp,Nat.cast_one,inv_one]




end Associates

variable (K : Allocation G S x W) (Y : Stores S)
    (h : Throng Y x) (hr : R.Lawful σ C Λ δ w) (hp : P.Lawful σ' C' Λ' δ' w')
    (hb : 0≤R.beta) (ht : Throng.Fits T P R x) (Hq : S.patch.Branches S.kernel G)
    (hh : PointCharge T x W γ) (hw : 0≤w) {l m : ℝ} (hl : l ≤ m) (he : 0 ≤ m)

section budget
variable {L' Z : Layer G V c} [Fintype I] {b : Bazaar D S L' Z} {χ : Chain (L'.Id ⊕ Z.Id)}
    (C'v : Vault I S) {g : ℝ}

include h hr hp hb ht Hq hh hw hl he

-- supplying this particular kind of invoice with the same forest mixture.
-- Issue X after matching the appropriate flag/support to Y (even univ).
-- Down κ reserve pulled out by Workable.use.

end budget
end Throng
end YM.Further.DenseMixedKernels
