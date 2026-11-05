import YM.Integration.ActualRunNativeComponentRecipe
import YM.Integration.RiderResourceDynamics
import YM.R2I.Campaign.Accepted
import YM.RG12.Burst.Wardrobe

set_option autoImplicit false
noncomputable section
namespace YM.Independent

open Integration PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12

/-- Select the Wilson run from its RG and lattice data. Finite observable comparisons
are proved after this choice. -/
theorem constructionRun {G : Gauge} (hG : G.Simple) {b : ℝ} (hb : 0 < b) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = b ∧
      R2I.Funded (garment10 G) R T ∧ ActualRunNativeComponentRecipe.Attached R := by
  have hTrue : R2I.EventuallyPaid (fun _ : RG.Levels G => True) :=
    fun _ _ _ V => ⟨V, Push.PriceCompiler.DelayLe.refl _, by intros; trivial⟩
  obtain ⟨R,T,hb',hSelected,_,_,_,_,⟨W⟩,hf,_⟩ :=
    R2I.RG05Joint.selectRunWithTreasuryPeriod_preselected_quote_orders_postnumeric
      (RiderResourceDynamics.defaultDynamics G).cultivate (CustodyR.minted G)
      (garment10 G) b hb hG hTrue
      (fun s (_ : Precision.MapPrices) => NativeComponentRecipe.Choice s)
      (fun s _ => NativeComponentRecipe.available hG s)
      NativeComponentRecipe.floor NativeComponentRecipe.numeric
      ActualRunNativeComponentRecipe.postnumeric
  exact ⟨R,T,W,hb',hf,ActualRunNativeComponentRecipe.of_preselection R hSelected⟩
/-- Choose the funded run before any extraction order or observable. -/
def fundedRun {G : Gauge} (hG : G.Simple) {b : ℝ} (hb : 0 < b) : Run G :=
  (constructionRun hG hb).choose

end YM.Independent
