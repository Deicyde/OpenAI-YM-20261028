import YM.MergeProof.Rocky
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
import YM.RG12.Spins.Slotty
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Pressure Next.Fluctuations Next.SectorChange Push.SectorMeasure
open WardBin.Lies Planned.PrimaryIntegral295
set_option quotPrecheck false
variable {G:Gauge}{M: Metals G}{D:Rolls M.p}
-- after-L fees.Wall span is whatever requested. η fixed program.Booth for capital tennis.
-- require d ≤ j
protected def Skill (C:Programs M.p)(K:ℕ→ℕ→Teller G)(R:ℕ→ℕ→Record)(b:ℕ→ℕ→ℕ)(ε:ℝ)(j i:ℕ)(x:ℝ): Prop :=
  ∀ β:ℝ,betaF G x (D.L j) / 2 ≤ β→∀{c f: Side}(S:RG.StepData c f)(T:Tube G S), S.patch.L=D.L j → S.patch.J=j → AnalyticBridge.LocalGaussianLaws.Lift.Booth (K j i) S T →100*(1+radiusB x) ≤ c.val →∀ {I:Type}[Fintype I][DecidableEq I]{p:Tree.Forest S.ratio}{A0:Stores S}{X:Support f}{Y:Support c}(a:Museum p x A0 X Y I)(U:Config G f){B B':BudgetPoint},
    B.power=(M.p.profile i).power → B.threshold ≤ 2*B'.threshold → B'.threshold=fiery G x (D.L j) → B'.B ≤ 2*radiusB x → Plays (C j i) (R j i) B B' (K j i) T x →∀{o:Site f},o∈ X → Short S B' X→ Walled S X Y x (b j i) → coverNumber B'.B X≤1 → ∀ (k:S.Choices)(χ q:Chi)(z:ℝ),∀ d≤j, ∀ (l:((Labels.frames G).level d).Index)(w:ℂ→L[ℝ]ℝ),‖w‖ ≤1 → ((((Labels.frames G).level d).grades l).2=2)→let f':=w ∘ Push.Local.presented (localSection G d) o B'.threshold (Place.copy _ l); let σ:=Cub.deem o x T f'
    let Ξ := a.hymn T (coupling β) q z k f' (PhysicalNext.JointLoad.Heir.guard χ G I (coupling β) ((R j i).ε*B'.threshold)) U
    B'.Regular X f' → B'.supBounds o X f' (Cub.title G (M.p.profile j))→∀ v v':Directions G c,B.dirBound (S.ratio.parent o) v→ B.dirBound (S.ratio.parent o) v' → ‖leftDerivs Ξ [v,v'] 1-leftDerivs σ [v,v'] 1‖ ≤ x^ε/x
variable {K:ℕ→ℕ→Teller G}{C: Programs M.p}{R:ℕ→ℕ→Record}{b:ℕ→ℕ→ℕ}{ε:ℝ}
variable {r₀:ℕ→ℕ}
def Pads8 (D:Rolls M.p)(C:Programs M.p) (K:ℕ→ℕ→Teller G) (R:ℕ→ℕ→Record)(b:ℕ→ℕ→ℕ)(ε:ℝ){θ:Protection D}(V:Delays θ):Prop :=
   ∀ j x,V.betaEntry j ≤ x → ∀ i, StepStages j i → M.p.first ≤ i → Legato.Skill (D:=D) C K R b ε j i x
lemma waves8 {θ:Protection D}(V:Delays θ)(hG:G.Simple)(hc:Pitch M.p M.K K C r₀)(hε:0<ε):∃ W:Delays θ,DelayLe V W∧∀ X:Delays θ,DelayLe W X→ Pads8 (M:=M) D C K R b ε X:=by
    have h(j i:ℕ)(hj:StepStages j i)(hi:M.p.first ≤ i):∀ᶠ x in atTop,Legato.Skill (D:=D) C K R b ε j i x :=by
       let P:= Clockwork.patch D hj hi
       have hn : 4 ≤ (M.p.profile i).order:=by linarith [(M.p.profile i).order_ge]
       have ht :0 ≤ Cub.title G (M.p.profile j):= zero_le_one.trans (Cub.title_one ..)
       obtain ⟨_,hQ,hY,hK⟩:=hc.crown.setup.braids j i
       have hr:P.Branches (K j i).bind G:=by rw [← hK]; exact M.p.has P
       have hz (d:Fin (j+1)):= Heir.Payed.purchase (Pt:=K j i) (D:=R j i) (C':=C j i) (localSection G (d:ℕ)) P hr hG (M.p.profile i).power hn _ ht hε (Next.Foundations.valuation G d) (b j i)
       filter_upwards [eventually_all.mpr hz] with x he β hβ c f S T hL hP hB hp X h1 h2 p A0 Y U0 a U B B' hl hs hm hh ht o hQ hD hR hE k q χ z d hd l w hw hδ
       exact he ⟨d,Nat.lt_succ_of_le hd⟩ _ hβ _ T (by cases h:S.patch; rw [h] at hP hL; unfold P Clockwork.patch; congr) hB hp a U hl hs hm hh ht hQ hD hR hE _ _ _ z l w hw hδ
    obtain ⟨A,_,hA,H⟩ := collect_upper V.betaEntry (fun j x=>∀ i, StepStages j i → M.p.first ≤ i → Legato.Skill (D:=D) C K R b ε j i x) (fun j=> eventually_transitions j _ _ (fun i hv=> by
       by_cases hV:M.p.first ≤ i; swap; · exact Eventually.of_forall fun x h'=>False.elim (hV h')
       exact (h j i hv hV).mono (fun x hx _=> hx)))
    -- case syntax invalid
    exact ⟨{V with betaEntry:=A},⟨hA,le_rfl,le_rfl,le_rfl⟩,fun _ h j x hv=> H j x ((h.beta j).trans hv)⟩
end YM.PhysicalNext.Repeat.Legato
