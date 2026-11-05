import YM.Next.BOUNDARY.Coordinates
import YM.Next.FLUCTUATIONS.Bare
import YM.Next.FREE_KERNELS.Train
import YM.Next.SCHEDULE.Visa






namespace YM.Next.ProgressOct10

end YM.Next.ProgressOct10
namespace YM.Next.Scheduling
open Filter RG RG.Supply Bid Precision Pressure Weak
/-- The accepted EBare proof discharges the pressure premise of the new numerical scheduler. -/
theorem funded_from_verified {G : Gauge} (hG : G.Simple) (s : Survey G) :

    ∃ K : MapPrices, ∀ (q : Quote) (e : ℕ → ℕ → Exchange),
      ∃ f : ℕ → ℕ, ∀ v ≥ f,
        Nonempty (Rolls (s.metals q K v).p) ∧ Prepaid s K q e v ∧
        ∀ D : Rolls (s.paper q v), ∀ extraW : ℕ → ℕ → ℝ,
          ∃ (B : Beam K D) (R : Radios K D), (∀ i j,extraW i j ≤ R.W i j) ∧
            -- these further post-L bills can be valued now
            ∀ (F : ℕ → ℕ → Postage) (m : ℕ → ℕ) (f : ℕ → Focus)
              (extra : ℕ → ℝ), (∀ i,0 < extra i) → ∃ T : Protection D,T.theta ≤ extra ∧
              ∀ V : Delays T, ∀ c d u, ∃ W : Delays T, Boost V W ∧ Loaded B W e F m f ∧
                Extent d c W ∧ Routed e u W ∧ Bumper e W ∧
                Transmitting R W ∧ Testing.Ringing K R.W W ∧
                ∀ r : ℝ,∃ Y : Bar W,r ≤ Y.value ∧ ∀ J : Wait Y,
                  ∃ I : Wait Y, Behind J I ∧ Billed I e f ∧ ∃ a : Levels G,Paid I a := by
  obtain ⟨K,hK⟩ := funded_prices hG s
  exact ⟨K,fun q e => hK q e (fun i j =>
    YM.Integrated.pressure_grants YM.Next.Fluctuations.bare _)⟩
end YM.Next.Scheduling
