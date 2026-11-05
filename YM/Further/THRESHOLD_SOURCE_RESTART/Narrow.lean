import YM.Further.THRESHOLD_SOURCE_RESTART.Halos
import YM.Push.CORRECTED_COLUMNS.Centering
/-!
# Restart across OLD K's and their blank addresses: a vacuum cut

Representation relative to the *same* labelled vacuum. Don't use that
just one Wilson density transfers `H → P` when changing the mask threshold!
Use a proof from the vacuum builder explicitly at the packet-history cut,
keeping even the unmasked scalar/flag comparisons in the exact spellings.
This is sufficient unmarked input; job of the vacuum threshold reclosure
producer to attain such data including energy/clip/ℓ mask compensations,
extra inspections, path wraps etc. No summability from comparison of
positive hard partitions. Even `balance` here only obtained after assembling
compatible packs for every OLD admissible choice that might have nonzero
events incl old blanks. We lift the representation WITH sources, requiring
no assertion about whether some specific K sits at zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Sill
open Function Set Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}

/-- Mask lowering data for threshold change at the same lattice. `H`
incoming unmarked representation; `P` bookkeeping now at the narrower
good predicate. `balance` corresponds to first reassembling JUST the
extra factors needed to multiply the old densities (the new-violation
packets and optional partnerships with them e.g.), labelled with their
complete incidences with old choices. It is an obligation even for
`s` including zero-payload stamps if admissible/eligible; may require
carrying history placeholders. Includes extra steps explicitly counting
actual reads upon any proposed regrouping. -/
structure Narrows (H P : Rep G n) where
  lowers : P.p.threshold ≤ H.p.threshold
  sites : ℕ → Finset ℕ                    -- old hard owners of i
  contains i j : j ∈ sites i → inspected (oldSites H j) ⊆ oldSites P i
  step : ℕ → Config G n → ℝ               -- REAL comparison/regrouping weight
  registers i : UsesFinal P.p.threshold (oldSites P i) (step i)
  measurable i : Measurable (step i)
  gauge i : GaugeInvariant (step i)
  admitted i U : step i U≠0 → permits P i U
  priced i U : P.activities.K i U=step i U * ∏ j∈sites i, H.activities.K j U
  sent (s : Finset ℕ) (U) : P.activities.admissible P.p U s → (∀ i∈s, step i U ≠ 0) →
    H.activities.admissible H.p U (s.biUnion sites)
  balance (T : Finset ℕ) (U) : H.activities.admissible H.p U T → (∀ i∈T, permits H i U) →
    HasSum (fun s : Finset ℕ => if s.biUnion sites=T ∧ P.activities.admissible P.p U s then ∏ i∈s,step i U else 0)
      (Real.exp (H.exponent U-P.exponent U))

namespace Narrows
variable {H P : Rep G n} (S : Narrows H P) {U : Config G n}
variable {V : Type*} [DecidableEq V] {R : Census V} {o : V → Site n}

include S in
lemma old_predicate {Y : Support n} (h : Healthy P.p.threshold Y U) : Healthy H.p.threshold Y U := h.mono_right
  (fun i hi => by obtain ⟨p,hp,h⟩ := (flags_spec ..).mp hi; exact (flags_spec ..).mpr ⟨p,hp,S.lowers.trans_lt h⟩)



lemma passes i {j} (h : j∈S.sites i) {F : Config G n → Poly R} (hp : Width.LocalCharge H.p o (oldSites H j) F) :
    LocalCharge P.p o (oldSites P i) F where
  gauge := hp.gauge
  borel := hp.borel
  reads U W H _ := (UsesFinal.allReads _ _ _ hp.reads) U W (agrees_mono H (S.contains _ _ h))
  carry U z H x hx := S.contains _ _ h (Halos.enters (hp.carry U z H x hx))

variable (L : Original H o R)

def price (i : ℕ) (U : Config G n) := (S.step i U:ℂ) • ∏ j∈ S.sites i,L.value j U
lemma inherited i : Width.LocalCharge P.p o (oldSites P i) (S.price L i) := by
  have H := Width.product_local (S.sites i) L.value (fun j h => S.passes i h (L.locality _))
  refine ⟨?_, (Complex.continuous_ofReal.measurable.comp (S.measurable i)).smul H.borel, ?_, ?_⟩
  · intro k U; unfold price; rw [S.gauge i k U]; exact congr_arg _ (H.gauge k U)
  · intro U W h he; unfold price; rw [S.registers i U W h he]; exact congr_arg _ (H.reads U W h he)
  intro U x h; refine H.carry _ _ fun e => h (by unfold price; rw [Poly.part_smul,e,mul_zero])

def award : Original P o R where
  value := S.price L
  pure i U := by
    unfold price; rw [Poly.part_smul, S.priced i U,Complex.ofReal_mul,Complex.ofReal_prod]; congr 1
    let f : Poly R →* ℂ :=
      { toFun := fun v => v.part R.quiet
        map_one' := by simp only [Poly.one_part,↓reduceIte]
        map_mul' := Poly.quiet_mul }
    exact Eq.trans (map_prod f ..) (Finset.prod_congr rfl fun b _ => L.pure b U)
  locality i := S.inherited _ _
  keeps i U h := S.admitted i U (fun e => h (by unfold price; rw [e]; simp only [Complex.ofReal_zero,zero_smul]))






end Narrows
end YM.Further.ThresholdSourceRestart.Sill
