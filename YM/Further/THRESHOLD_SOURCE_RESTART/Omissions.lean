import YM.Further.THRESHOLD_SOURCE_RESTART.Dock
import YM.Push.CORRECTED_COLUMNS.Reprint

/-!
# An identity upstream of the final unscaled-source leases

At the kernel cut in this module, assume the push has been opened and
integrated and the **scalar** gas format recovered, with *marked*
omission constraints not yet restored. This is a major physical input,
not provided by the single-source step nor by the fact that the vacuum alone
has some density representation!

`Pre` allows exact tracked contact (not necessarily every physical overlap).
Think e.g. blockers in an earlier first system; a hard record has to retain
enough history in its address that all its bans can be tested without a new
factor choice. Commuting any scalar reclosure before this cut has to be
proved when producing it. No inference that an arbitrary reclosed K record,
summed over earlier d's etc., could meet the assumption. Structurally can
also use an identity with no bans, *if* estimates earned at the addresses
used for it. Quantitative inputs further below test individual occurrences,
not estimates on the full value of a Pre.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Set Filter MeasureTheory Wilson RG Lattice Marker
open Push.Corrected Prepare Width
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V α : Type*} [DecidableEq V] {R : Census V}
variable {P : Rep G n} {o : V → Site n}
variable {w : V → ℝ}

lemma covered_send {x y : ℂ} (h : ‖x‖≤y.re) (hp : y.im=0) (i : R.Mode) :
    Covered (Poly.send i x) (Poly.send i y) := by
  intro j
  rw [Poly.part_send,Poly.part_send]; split <;> simp [*]
lemma hot_mask (X : Support n) (f : Config G n → ℂ) (p : BudgetPoint) (j : R.Mode) (ht : LocalOn X f)
    (hg : GaugeInvariant f) (hb : Measurable f)
    (hh : ∀ i∈j.val, o i ∈ X) : LocalCharge p o X (fun U => Poly.send j (masked p.threshold X f U)) := by
  constructor
  · intro t U; dsimp only; by_cases h : Healthy p.threshold X U
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (show Healthy p.threshold X (gauge t U) from by simpa [Healthy] using h),hg ..]
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (show ¬Healthy p.threshold X (gauge t U) from by simpa [Healthy] using h)]
  · exact (Overlay.Bands.sends _).measurable.comp (masked_measurable _ _ _ hb)
  · intro U W hy hv
    have he : Healthy p.threshold X U ↔ Healthy p.threshold X W := by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,hv]
    by_cases h : Healthy p.threshold X U
    · dsimp only; rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (he.mp h), ht U W hy]
    dsimp only; rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt he.mpr h)]
  intro U i hi; by_cases h : i=j; exact h.symm ▸ hh
  exact False.elim (hi (by rw [Poly.part_send,if_neg h]))
lemma value_of_mask (p : BudgetPoint) (s : Support n) (F : Config G n → ℂ) (U) {b : ℝ} (hp : 0≤b)
    (hx : Healthy p.threshold s U → ‖F U‖ ≤ b) : ‖masked p.threshold s F U‖ ≤ b := by
  by_cases h : Healthy p.threshold s U
  · rw [masked_eq _ _ _ _ h]; exact hx h
  rw [masked_ne _ _ _ _ h,norm_zero]; exact hp


/-- Atoms from the unrestricted MARKED log layer, and the hard array at
that point of the operation. Unmarked already in `P` (`hard` extends
that very labelled gas). No budgets here. -/
structure Pre (P : Rep G n) (o : V → Site n) (R : Census V) (α : Type*) where
  hard : Original P o R
  regular : Atoms P.p R o G α
  conflict : α → ℕ → Prop
  physical i j : conflict i j → ∃ x∈regular.sites i,x∈oldSites P j

namespace Pre
variable (L : Pre P o R α)

def docks : Dock P o R α where
  patch := L.regular.sites
  contact := L.conflict
  letter i U := Poly.send (L.regular.tag i) (masked P.p.threshold (L.regular.sites i) (fun U => - L.regular.H i U) U)
  warm i := by
    obtain ⟨v,hv⟩ := L.regular.proper i; exact ⟨o v,L.regular.pin i v hv⟩
  hot i U := by rw [Poly.part_send,if_neg (fun h => (L.regular.proper i).ne_empty (congrArg Subtype.val h.symm))]
  meets := L.physical
  reads i := hot_mask _ _ _ _ (fun U W h => congrArg Neg.neg (L.regular.footprint i U W h))
    (fun t U => congrArg Neg.neg (L.regular.gauge i t U)) (L.regular.borel i).neg (L.regular.pin i)

def penalty (i : α) (U : Config G n) := masked P.p.threshold (L.regular.sites i) (fun U => -L.regular.H i U) U
lemma amendment (i U) : L.docks.letter i U=Poly.send (L.regular.tag i) (L.penalty i U) := rfl


variable [Fintype V]

-- Already after any scalar omission restoration. Each record carries its
-- own history, avoid test uses it. Linearized identity would NOT supply this.






variable [Countable α] [Nonempty V]




end Pre
end YM.Further.ThresholdSourceRestart
