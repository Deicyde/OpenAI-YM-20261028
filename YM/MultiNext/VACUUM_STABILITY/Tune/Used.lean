import YM.MultiNext.VACUUM_STABILITY.Tune.Sample
import YM.Next.EXTRACTION.Base
import YM.Next.MULTISOURCE.Enclosure




set_option warningAsError false

/-!
# Employ the cheaper data: only raw first-system and base attachment estimates

Counterterm implementation tuned from local letters paid and present in same S.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Tune
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock Source Labels
open Jets Hits
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge}

structure Met (B : Brush V G n) (base : ℕ→HardLetter V G n) (P : BudgetPoint)
    (L : V → Support n → Prop) (T : Finset V) : Prop where
  lawful i : P.Regular (B.u i).zone (B.u i).stamp.ink
  begun i x : x∈(B.u i).stamp.name.support → L x (B.u i).zone
  legible i : Legible P (B.pack i) (B.d i).ink
  sits i x : x∈ (B.d i).name.support → L x (B.pack i).zone
  cover i : i∉T → B.pay i=0
  ins i : Spanned P (base i).zone (base i).stamp.ink
  baseFlag i U : Healthy P.threshold (base i).zone U → (base i).stamp.ink U=0
  zero i : (base i).stamp.name = 0



/-- Direct data to the single-step request at an unmarked run. -/
theorem stocked {B : Brush V G n} (S : Slicer B) (P : Rep G n) (w : V→Pulse G n) (L : V→Support n→Prop)
    [Fintype V] (T : Finset V) (m : ℕ) (χ κ : ℝ) (o : V→Site n) (k : V→ℝ) (η : ℝ) (hk : ∀ i,0≤k i) (he : 0<η)
    (hh : Widens L) (ht : S.Ticket P.p L T m χ) (hx : ∀ z∈allot o k η, S.Endowed P.p m χ κ z) (hv : S.Landed P T w) :
    Supported B (S.package P.p T) P.p L T ∧ Settled B (S.package P.p T) P T w ∧
    ∀ z∈allot o k η, Quoted B (S.package P.p T) P.p κ z := by
  obtain ⟨r,hr,hR⟩:=Desk.permits o k η hk he
  let z (_ : V) := (r:ℂ)
  have hZ : z∈allot o k η := hR (fun i => by change ‖(r:ℂ)‖≤r; simp [abs_of_pos hr])
  exact ⟨S.gathered ht hh,S.loaded ht (hx _ hZ) (fun i _ => Complex.ofReal_ne_zero.mpr hr.ne') hv,
    fun z hz => Slicer.paid_all ht (hx z hz)⟩
end YM.Multi.Vacuum.Tune
