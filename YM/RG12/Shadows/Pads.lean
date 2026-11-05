import YM.RG12.Shadows.Cradle
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Rope
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-!
 # Birth extra wait transcribable at any B phases.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG RG.Supply Wilson Pressure Pressure.Tube Tree Next Next.Foundations Precision
open Push Push.PriceCompiler AnalyticBridge LocalGaussianLaws JointLoad JointLoad.Heir JointLoad.Heir.Suite
open Input Org Extra.Histories Planned.PrimaryIntegral295  Bloch Bid Planned.AtomRegular Planned.AtomRegular.Foliage
open AnalyticBridge.VerifiedReset.Time Next.Scheduling Repeat.Peak VerifiedReset ConnectedActivityE6 Pressure.Testing
open ProofPorts
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G: Gauge}{M : Sheet G} {K : MapPrices}{R:Targets M K}{E: Expenses R}{W : Return.Wages}{q:ℕ→ℝ}

variable (C: Programs M)(D:Rolls M)(Y: ℕ→ℕ→Heir.Record) (r : ℕ→ℕ→ℕ)(B:Register D E W q)
open Push.SectorMeasure
local notation "χ*"=> Chi.canonical
-- Slots on exact Fondation.Claims lic at y.NewPads distinct.
def Hour (j i d:ℕ)(x:ℝ):Prop:= ∀ v:((Labels.frames G).level d).Index,
    Sanction.Medal (query M K j i) (D.L j) (C j i) (M.profile i).power (Y j i) χ* (W j i) (B.o j i) χ* (Cub.title G (M.profile j)) (Sanction.stair d v) (betaF G x (D.L j)^(-(7/8):ℝ)) x
def Pads9 {θ:Protection D}(U:Delays θ):Prop:=∀ j x,U.betaEntry j ≤ x →∀ i,StepStages j i → M.first ≤ i →∀ d ≤ j,Hour C D Y B j i d x
lemma tunes9 {θ:Protection D} (U:Delays θ)(he:∀ j i,StepStages j i→ M.first ≤ i→ (Y j i).ε ≤1/4): ∃ P:Delays θ, DelayLe U P ∧ ∀ X:Delays θ,DelayLe P X→Pads9 C D Y B X:=by
  have hx(j i:ℕ)(hh:StepStages j i):∀ᶠ x in atTop,M.first ≤ i →∀ d≤j,Hour C D Y B j i d x:=by
    by_cases ht:M.first ≤ i
    · have h(d:ℕ)(l: ((Labels.frames G).level d).Index):= Sanction.purchasing (C:=C j i) (P:= query M K j i) (p:=(M.profile i).power) (o:=B.o j i) χ* χ* (L:=D.L j) (Cub.title G (M.profile j)) (Sanction.stair d l) (-(7/8):ℝ) (by norm_num) (le_trans (by norm_num) (M.profile i).order_ge) (he j i hh ht)
      filter_upwards [eventually_all.mpr (fun (d:Fin (j+1))=>eventually_all.mpr (h d))] with x h hx d hd l; exact h (⟨d,Nat.lt_succ_of_le hd⟩:Fin (j+1)) l
    exact Eventually.of_forall fun _ hk=> (ht hk).elim
  obtain ⟨F,_,hF,hB⟩:= collect_upper U.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i=> hx j i))
  exact ⟨{ U with betaEntry:=F },⟨hF,le_rfl,le_rfl,le_rfl⟩,fun X h j x hx=> hB _ _ ((h.beta _).trans hx)⟩
end YM.PhysicalNext.Repeat.Circlet
