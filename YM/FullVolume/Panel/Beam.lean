import YM.FullVolume.Panel.Hangar
import YM.MergeProof.Escarp
import YM.MergeProof.Crowding
import YM.MergeProof.Largo

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
open Matric
open Guard
-- anchor at Q reference state. annotations only; analytic transport via Fortune.
variable {Y}
structure Boutique (X:Factor A)(meshT:ℕ→∀ p, RG.Shoot.Trail A.B.a p)(N p m:ℕ) where
    stock:Spring X N m p 0 0 (fun _=> ((A.B.bake.make meshT).rep N p (m+1)))
    taught : (A.B.bake.make meshT).rep N p m=stock.result 0
    up: HasSlots ((A.B.bake.make meshT).rep N p (m+1)).p ((A.B.bake.make meshT).rep N p (m+1)).activities
    down: HasSlots ((A.B.bake.make meshT).rep N p m).p ((A.B.bake.make meshT).rep N p m).activities
    hx: m<N
    pays : N≤ stock.ordinal
namespace Boutique
variable {meshT:ℕ→∀ p,RG.Shoot.Trail A.B.a p}{N p m d:ℕ}
local notation "H!"=> A.B.bake.make meshT
local notation "μ"=> (0:ℝ)
def center : Set.Icc (0:ℝ) 0:= ⟨0,le_rfl,le_rfl⟩
variable (U: Boutique X meshT N p m)(choice: (A.B.bake.make meshT).Selected)(hd:d+3 ≤ A.B.a.clock.J m)
local notation "ris"=> (H!).rep N p (m+1)
local notation "R'"=> (H!).rep N p m
abbrev gate := duet (H!) N p m U.taught (show ris = (fun _ => (A.B.bake.make meshT).rep N p (m+1)) (center:ℝ) from rfl) (sandboxK U.stock center)
local notation "fa"=> (Labels.frames G).level d
local notation "J"=> A.B.a.clock.J (m+1)
local notation "t"=> A.B.a.clock.J m
include b U choice hd in
lemma okC: Push.Local.Readable (hol G) (localSection G d) ((ris).p) (A.B.a.S.side (m+1) p) (Cub.title G (M.p.profile J)):=by
    have he: d ≤ J:= ((Nat.le_add_right d 3).trans hd).trans (step_paid A.B.a m).1; rw [(choice.represents N p (m+1) U.hx).vac, show Cub.title G (M.p.profile J) = authors A.B.a (m+1) by unfold Cub.title authors; rw [params_eq A.B.valid] ]; exact lively b.clock he
open Motion
noncomputable def castT:Tool ((Labels.frames G).level d) (A.B.bake.make meshT) N p m:= ⟨Cub.shade U.stock center U.down U.up (U.okC b choice hd), Keeper.sufficient U.up, Keeper.sufficient U.down, fun m'=> (choice.represents N p m U.hx.le).good.labels.moves m'.1 0|>.some⟩
structure Manus : Prop where
   swing:Afford (U.castT b choice hd).plate (hol G) ((H!).rep N p (m+1)) ((H!).rep N p m)
   chamber: ∃ Q V, Tool.Cap (U.castT b choice hd) (localSection G d) (hol G) K U.gate Q (C (A.B.a.clock.J (m+1))) (Doors.rate ((H!).S.block m)) (waybill A.B.a m) V
include hG Y
lemma tickets (hz:Nest X Y): Manus b U choice hd:=by
    refine ⟨Cub.prairie U.hx U.stock center b.r hG U.taught rfl b.clock b.stamp choice U.down U.up b.tunes b.furthering hd (okC b U choice hd),?_⟩
    obtain ⟨V,hV⟩:= ledgerHere U.hx b.songs b.PStage b.wait (Graces.feet hd b.clock) hz b.r U.stock center U.taught rfl hG b.tunes b.furthering b.corners b.shape b.clock b.stamp choice U.down U.up (okC b U choice hd) hd
    let Y':= Keeper.sufficient U.up; let n:=A.B.a.S.side (m+1) p; let A₀:=(0:Site n); let X₀ (i:{i: Support n// A₀∈i}): Wing:=.logKey (Blush.found 0 i.val i.property); let Xk(q : StockTag n): Wing:= Wing.gasKey (cart (R:=ris) Y' q);let V' := Set.range X₀ ∪ Set.range Xk; have hf: V'.Finite:= (Set.finite_range X₀).union (Set.finite_range Xk)
    refine ⟨V,V',⟨choice,U.hx,sound_duet (H!) N p m U.taught _ (sandboxK U.stock center) _ (sounds hG U.hx U.stock center b.r),hf,fun i=> Or.inr ⟨i,rfl⟩,?_ ,b.clock.fits H! rfl m d (by omega),?_,(glyphBound A.B.a (m+1)).2,sound G d⟩⟩
    · unfold waybill; rw [params_eq A.B.valid,← (show ((H!).rep N p (m+1)).p=A.B.a.budget (m+1) from (choice.represents N p (m+1) U.hx).vac)]; exact hV V' (fun i hi=> Or.inl ⟨⟨i,hi⟩,rfl⟩)
    unfold waybill; exact mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Cub.title_one ..)))
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
