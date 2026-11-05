import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Seaports
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.Paddle
import YM.MergeProof.Tender
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Reel
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsColumnL
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris



/-! All after-L, all future charts. BUY with same CB. Petroleum requests. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Push
open Mallow Lotus
open YM.MergeProof MergeProof.Accent MergeProof.Menu
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}
section
variable (Q:ℕ→ℕ){M: Sheet G} {P:Rolls M} {θ:Protection P} (Z:Delays θ)
def creek (G:Gauge)(Y:Stage)(Ys: Stage)(d:ℕ) (x y r:ℝ)(L:Side):Prop:=
       fog G d x*Y.columns≤1∧2*Motion.orbitCost ((Labels.frames G).level d)*(r+2*Ys.columns)*fog G d y ≤ 1∧
        Real.exp (Y.supportExponent+2)*(Doors.cameras G d*x^Extra.Histories.degree ((Labels.frames G).level d))*fog G d x ≤ stub x∧
        sap y ≤ 1 ∧ sap y*((L.val:ℝ)^d*Ys.columns)*fog G d x ≤ fog G d y∧ minSide G d ≤ Pressure.radiusB x
local notation "S"=> M.profile
local notation "R"=>P.L
local notation "T"=> Pressure.radiusB
set_option quotPrecheck false
def tableCost (G:Gauge)(Ys:Stage):= 2*(Real.exp Ys.supportExponent*Cub.title G Ys)
def Steam :Prop:= ∀ j i x,StepStages j i → Z.betaEntry j≤ x → let y:= Pressure.betaF G x (R j); 8 ≤ Pressure.radiusB x ∧ y^3 ≤ mintK (Pressure.radiusB x) ∧ let p:=Q j; let t:=Doors.stain x + p*Extra.Multi.siteFactor (Pressure.radiusB x)*stub x
                          (((Pressure.radiusB x+Pressure.radiusB x+1:ℕ):ℝ)^4*t ≤ 3 ∧ Real.exp t-1≤1) ∧ ∀ d:ℕ,d ≤ i → creek G (S i) (S j) d x y (tableCost G (S j)) (R j)
lemma hiss :∃ V:Delays θ, DelayLe Z V ∧ ∀ U:Delays θ,DelayLe V U → Steam Q U:=by
    let b j:= G.slopeConstant*Real.log (P.L j).val; let c j i d x:= creek G (S i) (S j) d x (x+b j) (tableCost G (S j)) (R j)
    let t j x:= Doors.stain x + (Q j)*Extra.Multi.siteFactor (T x)*stub x; let F(j i:ℕ)(x:ℝ):Prop:=8 ≤ T x∧ (x+b j)^3 ≤ mintK (T x)∧ (((T x+T x+1:ℕ):ℝ)^4*t j x ≤ 3∧ Real.exp (t j x)-1≤1) ∧ ∀ d:ℕ,d ≤ i → c j i d x
    have he(j i):∀ᶠ x in atTop,F j i x:=by
       have hc(d):∀ᶠ x in atTop,c j i d x:=by
          filter_upwards [rind G d (S i) (R j) (b j) (S j) (tableCost G (S j)),Work.E01.radiusB_tendsto.eventually_ge_atTop (minSide G d)] with x h hx
          exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,hx⟩
       filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 8,polestar 1 zero_le_one 3 (b j),dew (Q j),(eventually_all_finset (Finset.range (i+1))).mpr (fun d hd=> hc d)] with x hx hv hT he
       rw [one_mul] at hv; exact ⟨hx,hv,hT,fun d hd=>he d (Finset.mem_range.mpr (by omega))⟩
    obtain ⟨r,-,H,hv⟩:= collect_upper Z.betaEntry _ fun j=> eventually_transitions j _ (F j) (fun i _=> he j i) -- check F implicit
    let V:Delays θ := {Z with betaEntry:=r}; refine ⟨V,⟨H,le_rfl,le_rfl,le_rfl⟩,fun U h j i x ht hx=> ?_⟩; exact hv j x ((h.beta j).trans hx) i ht
end
end YM.PhysicalNext.Repeat.Legato.Bandage
