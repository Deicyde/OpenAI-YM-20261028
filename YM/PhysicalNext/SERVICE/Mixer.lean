import YM.AnalyticBridge.VERIFIED_RESET_STEP.Downstream
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Inherited
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Merchant
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import YM.Planned.RECIPE_STARTUP_PORT.Layout


/-!
# Preparing for `VerifiedReset.Use.Machine`

PeriodFuture variant of the bridge. Can still supply normalizations and
witnesses for an unmarked step purchase, on that recipe. We do not need
`Beam`/`Regime` on this port; don't claim every PeriodFuture vertex lawful
without additional hypotheses. Only test its probabilities/continuity of eval
in `proceeds`. `Mixing` is BEFORE even the enormous `Offering` hypothesis to
advance and form a Bolt. These files don't show Offering -- which includes,
among other things, a whole pre-reset interacting atlas and estimates. So Bake
here has the same configuration as that advance port requires (and Origins),
not a trajectory. Larger/other price tests in the campaign must still be
checked on the ACTUAL knuckles; not saying these suffice for other producer
contexts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Service
open ThroughLaunch Function Filter WilsonStartup Set Pressure Work.F05 AnalyticBridge.VerifiedReset
open RG Wilson Precision Lattice RG.Shoot RG.Supply Matrix Further.StrongStartup Next.Scheduling
open Next.Foundations
open Push.PriceCompiler UVNext.CouplingReset Time Org Progress.DirectedRecipe
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} (hG : G.Simple)
section logic
variable {a : Levels G} {W : Horizon a} {O : ChartRatio G} {u : Kin W O} {r : Permissions a}
    {E : ℕ → ℕ → Next.Scheduling.Exchange} {F : PostList} {N m p : ℕ} {U : Rep G (a.S.side m p)}

-- This doesn't need a Beam or imply reload. Keep even gauge & signed-perm.


abbrev simpleOrigins (u : Kin W O) := Progress.DirectedRecipe.Origins u (permissions a)
lemma origins (h : ∀ N,u.path N N=Design.top G (a.params N).clip) (hr : ∀ N,Start.Allows a N) : simpleOrigins u := by
  intro N p
  obtain ⟨ht,H,hc,hx⟩ := YM.Planned.Port.card (p:=p) (hr N) (permissions a) (show YM.Planned.Port.AtTop u from h)
  exact ⟨_,_, fun β hw => ⟨(ht β hw).ingredients,(ht β hw).matches_raw, trivial⟩,H,hc,hx⟩
end logic
variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D} {η g z : ℕ → ℝ}
    {E : ℕ → ℕ → Next.Scheduling.Exchange} {F J : PostList} {p : ResetPrices}
    {I f r b : RatioList} {L : ℕ→ℕ→ℝ→ℝ} {S : Scouts (F:=F)}
    {O T : MapPrices} {C : ℕ → ℝ}

-- After Boost and floors. Need forecasts funded at THESE buys.
structure Mixing (A : Alloy M D) (E : ℕ → ℕ → Next.Scheduling.Exchange) (p : ResetPrices) (I : RatioList) (J : PostList)
    (L : ℕ → ℕ → ℝ → ℝ) {F : PostList} (S : Scouts (F:=F)) (η : ℕ→ℝ) (f r b : RatioList) : Prop where
  ff : Use.Machine A.B E S η p f r b
  localEntry : Inherited A.delay I J L
  boot : simpleOrigins A.B.kin
  waves : ∀ N m t,m<N→ Bid.Sworn (A.B.M.H N m) t G






variable {s : Sheet G} {t : Tariffs} {B : Extra.Multi.Scope} {v v' : ℕ→ℕ}
    {ℓ l : ℕ→ℝ} {w : Bid.Worth} {Z : Rolls (ThroughLaunch.raise s v')} {Θ : Protection Z} {W : Delays Θ}
    {P : PostCost Z} {Δ : Bar W} {Y : Wait Δ} {a : Levels G} {U : Horizon a} {k : Kin U (chart G)}

include hG

end YM.PhysicalNext.Service
