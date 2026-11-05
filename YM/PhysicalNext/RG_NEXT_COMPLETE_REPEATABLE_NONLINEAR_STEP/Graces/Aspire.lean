import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Little
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
/-!
 # pay-base at card table.Then accepts Birth goals separately.L constraints not issued here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
-- Fee.small compared R.p incoming
variable (G) (P : RG.Stage) (d : ℕ)
def vigors := Push.Local.factor (hol G) (localSection G d) P.supportExponent (Next.Foundations.price G (max P.order P.power))
def faded := Push.Local.turnCost P.order P.power
def host := (1+2*|vigors G P d| *(1+Motion.orbitCost ((Labels.frames G).level d)+|faded P|))
def coinFee (L : Side) := Doors.rate L / host G P d
lemma simpleH : 0<host G P d := by unfold host; have he:= Motion.orbitCost_one_le ((Labels.frames G).level d); positivity -- syntax
lemma coin_pos (L:Side):0<coinFee G P d L:=div_pos (Doors.rate_pos _) (simpleH G P d)
-- separate growth vs UV fine.L clock dependency
variable {G}
section epoch
variable {s: Sheet G}{D:Rolls s}{A: Protection D}{K: MapPrices} {R : Targets s K}{V : Expenses R}{w : Return.Wages}{l : ℕ→ℝ}(W: Register D V w l)

def Comply (W : Register D V w l) (T: Delays A) : Prop := ∀ j i, StepStages j i → ∀ d ≤ i,
    let L:=D.L j; let u:= coinFee G (s.profile i) d L
    ∀ x,T.betaEntry j ≤ x →
      (∀ c:Side,∀ (v: RG.Rep G c)(t: Cloud v),
       let m:=v.p.mass t.live.crest t.live.weight; let S:= marvel (Q:=R j i) (L:=L) (x:=x) t; let V:= jewelDebt t.live (R j i) L x
       (L.val:ℝ)^d*(S+S)≤u*m∧(glyph x)⁻¹*((L.val:ℝ)^d*(V+V)*straw (W.μ j i) L G x)≤u*m) ∧
      (∀ C : Levels G,∀ m,C.params m=s.profile i → C.clock.hatBeta m=x → Push.Local.hitWidth (C.budget m) * glyph x ≤ 1)
lemma compass (T: Delays A) :∃ U: Delays A, DelayLe T U∧∀ V:Delays A,DelayLe U V → Comply W V:=by
  let P j i d x:= ∀ (v:Side)(M:Rep G v)(t:Cloud M), let Y:=R j i; let u:= coinFee G (s.profile i) d (D.L j); let m:= M.p.mass t.live.crest t.live.weight; let a:= ((D.L j).val:ℝ)^d; let b:=marvel (Q:=Y) (L:=D.L j) (x:=x) t; let v:=jewelDebt t.live Y (D.L j) x
    a*(b+b)≤u*m∧ (glyph x)⁻¹*(a*(v+v)*straw (W.μ j i) (D.L j) G x) ≤ u*m
  let Y j i d x := P j i d x∧ (∀ C:Levels G,∀ m,C.params m=s.profile i → C.clock.hatBeta m=x → Push.Local.hitWidth (C.budget m)*glyph x ≤ 1)
  have he (j i:ℕ)(h:StepStages j i) d:∀ᶠ x in atTop,Y j i d x:= by
    let P:= s.profile i; let a:= (((D.L j).val:ℝ)^d); obtain ⟨S,H⟩:= Push.Local.delay (localSection G d) P.supportExponent
    filter_upwards [fruition (L:=D.L j) (W.consumes _ _ h|>.2.1) (R j i) a (coinFee G P d _) (coin_pos G P d _), eventually_ge_atTop S] with x hp hx
    refine ⟨?_ ,fun C m H' h=> ?_⟩
    · intro v M t; have hh : ‖(a:ℂ)‖=a := (Complex.norm_real _).trans (Real.norm_of_nonneg (by unfold a; positivity))
      have he:= hp v M t a hh.le; dsimp only at he; rw [hh] at he; exact he
    rw [← h,← Blush.glyph_eq]; exact (H C m ((congr_arg RG.Stage.supportExponent H').le) (h.symm ▸ hx)).1 -- edit
  obtain ⟨u,-,hv,H⟩:= collect_upper T.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i h=> ((Finset.range (i+1)).eventually_all.mpr (fun d hd=> he j i h d))))
  exact ⟨{T with betaEntry:=u},⟨hv,le_rfl,le_rfl,le_rfl⟩, fun _ hz j i hi d hd x hx=> H j x ((hz.beta _).trans hx) i hi d (Finset.mem_range.mpr (by omega))⟩ -- let binder lambda
end epoch
end YM.PhysicalNext.Repeat.Graces
