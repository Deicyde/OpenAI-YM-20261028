import YM.FullVolume.Cross
import YM.WilsonBulk.Agenda.Schedule

/-!
The native period registry is fixed before the block lengths. Its length
floor and later beta gates are bought on one construction. `registry` is
the exact defining term of `QLocal.Packets.candle`; the separate candle
attachment proves that equality by reflexivity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CommonPeriodPurchase
open Lattice RG RG.Supply Precision Push.PriceCompiler
open WilsonBulk.Parapet WilsonBulk.Parapet.Agenda
open scoped Classical
variable {G : Gauge}

def registry (G : Gauge) (K : KernelChoices) (F : MapPrices) : Lit G K F :=
  Classical.choice (Lit.exists G K F)

structure Plan (G : Gauge) (K : KernelChoices) (F : MapPrices)
    (J : ChartRatio G) where
  floor : ℕ → ℕ
  pre : Prelit (registry G K F) (1/2) floor
  later : (ℕ → Side) → ℕ → ℝ
  dawn (L : ℕ → Side) : Dawn J (1/2) (registry G K F) L (later L)

theorem plan_exists (G : Gauge) (K : KernelChoices) (F : MapPrices)
    (J : ChartRatio G) : Nonempty (Plan G K F J) := by
  obtain ⟨τ, hτ⟩ := (registry G K F).allGates (1/2) (by norm_num)
  refine ⟨⟨τ, hτ, fun L => (allPost J (registry G K F) (1/2) L).choose, ?_⟩⟩
  intro L
  exact (allPost J (registry G K F) (1/2) L).choose_spec

def Funded (F : MapPrices) (J : ChartRatio G) (A : Levels G) : Prop :=
  Arena (A := A) F (registry G A.clock.kernel F) (1/2) J

theorem Plan.arena {K : KernelChoices} {F : MapPrices} {J : ChartRatio G}
    (P : Plan G K F J) (A : Levels G) (hK : A.clock.kernel = K)
    (L : ℕ → Side) (hL : ∀ i, P.floor i ≤ (L i).val)
    (hFactor : A.clock.factor = L)
    (hBeta : ∀ i, P.later L (WilsonBulk.stage A (i+1)) ≤ A.clock.hatBeta i) :
    Funded F J A := by
  subst K
  exact invoice (P.dawn L) P.pre hL hFactor hBeta

/-- After paying the actual length floor, enlarge only the beta-entry
gate. Every later delay and every Paid realization retain this registry. -/
theorem buy {s : Sheet G} {D : Rolls s} {θ : Protection D}
    {F : MapPrices} {J : ChartRatio G}
    (P : Plan G s.kernel F J) (hFloor : ∀ i, P.floor i ≤ (D.L i).val)
    (U : Delays θ) :
    ∃ V : Delays θ, DelayLe U V ∧
      ∀ Z : Delays θ, DelayLe V Z →
        ∀ (B : Bar Z) (W : Wait B) (A : Levels G),
          Paid W A → Funded F J A := by
  let V : Delays θ :=
    { U with betaEntry := fun i => max (U.betaEntry i) (P.later D.L i) }
  refine ⟨V, ⟨fun _ => le_max_left .., le_rfl, le_rfl, le_rfl⟩,
    fun Z hZ B W A hA => ?_⟩
  apply P.arena A hA.kernel D.L hFloor hA.lengths
  intro i
  exact (le_max_right (U.betaEntry (WilsonBulk.stage A (i+1)))
    (P.later D.L (WilsonBulk.stage A (i+1)))).trans ((hZ.beta _).trans (hA.pays i))

end YM.Integration.CommonPeriodPurchase
