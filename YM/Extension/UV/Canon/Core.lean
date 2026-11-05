import YM.Extension.UV.StartCost
import YM.MergeProof.Retreat
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles
import YM.Extension.UV.Shoot

/-!
Adapter retaining more properties of the *same* directed and shooting choices as in
`Serenity`, `Bourse` and `Graces.winnow`. In particular force the kickoff to use the very
`dictionary` from `Start`, not an existential `Origins` to be resolved differently at every
coupling. This strengthens the common underlying UV construction used later without changing
its field normalization. Does not specify a common complete sequence of post-top return maps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV
open Function Filter Set Lattice Wilson Pressure RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open PhysicalNext ThroughLaunch Repeat Graces Roost Mallow
open WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open Progress.DirectedRecipe Ovens Ovens.Pipes
open RG.Shoot
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge} {s:Sheet G} {D : Rolls s} {θ:Protection D} {V:Delays θ} {Z:Bar V} {I:Wait Z} {K:MapPrices} {O:ChartRatio G} {P:PostCost D}
/-- Available pre-merge fields of exactly this directed instance. Keep also the overlaid
stationary paths, for potential comparison; existence separately would not coincide. -/
structure Archive (B:Directed G I O K P) : Prop where
  kinetic : ∃ (X W : Horizon B.a) (u : Kin W O) (O' T:MapPrices) (l:ℕ→ℝ), Craft.Rack B.a O' X ∧ YM.Next.Free.Present B.a X l ∧
    Bid.Retained W X ∧ W.Suffices T ∧ YM.Next.Free.Present B.a W l ∧ (∀ N m t, m ≤ N → Bid.Sworn (W.H N m) t G) ∧
      Stationary.FullPaths u P ∧ B.kin.path=Change.revised u ∧ B.kin.alpha=u.alpha ∧
      (∀ N m p F, m+1<N → B.kin.stationary N m p F=u.stationary N m p F) ∧ Change.Overlay B.M W ∧
      (∀ N m, m<N → (B.M.towers N m).T=(W.towers N m).T)
  top : Planned.Port.AtTop B.kin
  startup (N:ℕ) : Start.Allows B.a N

namespace Archive
section torrent
variable {n : ℕ→ℕ} {T: MapPrices} {D : Rolls (ThroughLaunch.raise s n)} {θ:Protection D} {V:Delays θ} {Z:Bar V} {I:Wait Z} {Q:PostCost D} {a:Levels G} {M : Horizon a} {k:Kin M (chart G)} {O':MapPrices} {l:ℕ→ℝ}
/-- Unpack the archive during the exact `Torrent` pass; defeq checks simultaneously fix all the
record indices. Not a change of tower. -/
lemma pack (hT:Torrent O' T l Q a M k) (hx:Paid I a) (hN:∀ N, Start.Allows a N) {E F} :
    Archive (Progress.DirectedRecipe.prepared k E F (permissions a) hx hT.finalMap (chart_ok _) hT.paths) :=
  { kinetic:=by
      obtain ⟨X,W,u,H⟩:= hT.layer
      exact ⟨X,W,u,O',T,l,H⟩
    top:= hT.top
    startup:= hN }
end torrent
end Archive

section launch
variable {X: Metals G} {D:Rolls X.p}{A:Alloy X D} (R : Factor A) (h:Archive A.B)
include h
lemma topmenu (N p) :
  Menu A.B.kin (permissions A.B.a) N p (Planned.Port.pot A.B.a N p) (Planned.Port.kettle A.B.a N p) := by
  have H:= Planned.Port.card (p:=p) (h.startup N) (permissions A.B.a) h.top
  exact ⟨fun β hx=> ⟨(H.law β hx).ingredients,(H.law β hx).matches_raw,trivial⟩,H.curve,H.atoms,H.common⟩
include R
lemma canStart (N p : ℕ) :
    let f:=Startup.canonical A.B.kin N p
    ∀ β∈ band A.B.a N,(f β).beta=β∧Lives A.B.bake N N p (f β) ∧ A.B.bake.Starter N p (f β) ∧ HasSlots (f β).p (f β).activities := by
  intro f β hx; have hX:= topmenu h N p
  let B:=A.B
  let X':=Planned.Port.pot B.a N p
  let D:=Planned.Port.kettle B.a N p
  change (fromTop B.kin N p β X' (D β)).beta=β∧Lives A.B.bake _ _ _ (fromTop B.kin N p β X' (D β))∧A.B.bake.Starter _ _ (fromTop B.kin N p β X' (D β))∧HasSlots (fromTop B.kin N p β X' (D β)).p (fromTop B.kin N p β X' (D β)).activities
  refine ⟨rfl,?_,?_,(hX.law β hx).ingredients.spare_room (B.kin.path N N) (B.a.params N).clip β 0⟩
  · rw [R.machine.ready]; exact ⟨rfl,rfl,rfl,⟨B.support.cap N N le_rfl,(hX.law β hx).ingredients.gates ..⟩, PeriodFuture.begin hx (hX.law β hx)⟩
  rw [R.machine.ready]; exact starter (hX.law β hx) hx _ _

set_option linter.unusedVariables false in
lemma winnowCanonical (g:G.Simple) : ∃ Y:Bolt A,Nest R Y∧
     ∀ N p, Y.history N p N=Startup.canonical A.B.kin N p ((Y.history N p N).beta):=by
  let B:= A.B
  let Y := { A.B.bake with next:=fun N m p u v=> A.B.Move N m p u v ∧ Protected R N m p u v∧Accurate A.B R.post N m p u v,
                           first:=fun N p v=> A.B.bake.first N p v∧ HasSlots v.p v.activities ∧ v=Startup.canonical A.B.kin N p v.beta }
  have he N m p u: Lives Y N m p u ↔ Lives A.B.bake N m p u := by constructor <;> rintro ⟨a,b,c,d,e⟩ <;> exact ⟨a,b,c,d,e⟩
  have hp N p:Y.Issues N p:=by
    constructor
    · have hX := topmenu h N p
      refine ⟨_,hX.starts,?_⟩; intro x hx
      obtain ⟨hv,hB,ht,hZ⟩:= canStart R h N p x hx; exact ⟨hv,(he ..).2 hB,ht.scalars,ht.raw,ht.inits,hZ,rfl⟩
    intro m hm l t hl Q hc hx
    obtain ⟨H⟩:= faces R Q hl hc (fun x hy=> ⟨(he ..).1 (hx x hy).1,(hx x hy).2⟩) hm
    obtain ⟨hq,hp⟩:= H.moves g hm
    refine ⟨H.result,hq,fun x hy=>?_⟩; obtain ⟨hx,hK,-,-⟩:= hp x hy; exact ⟨(he ..).2 hx.bundle,hx.ident,(A.B.links hm hx).drift,hx,⟨l,t,Q,H,x,hy,rfl,rfl⟩,(by rw [show Accurate A.B R.post N m p (H.result x) (Q x)= (|(H.result x).beta - UVNext.CouplingReset.predictor A.B N Q x| ≤ UVNext.CouplingReset.width A.B.a m R.post) from by unfold Accurate UVNext.CouplingReset.predictor; rw [sub_add_eq_sub_sub]]; exact hK)⟩
  obtain ⟨T,hT,H⟩:= Y.races g hp (Drifting.pay A.B.valid)
  have hM (N m p:ℕ)(hm:m<N): A.B.Move N m p (T N p m) (T N p (m+1)):= ((hT N p).persists m (Nat.zero_le _) hm).continues.1
  have hz : A.B.bake.Stays T := by intro N p; have hf:= (hT N p).fromTop; exact ⟨fun i hi hj=> ⟨(he ..).1 ((hT N p).prices i hi hj).1,((hT N p).prices i hi hj).2⟩,⟨hf.scalars,hf.raw,hf.inits.1⟩,fun i hi hi'=>A.B.links hi' (hM N i p hi')⟩
  refine ⟨⟨R.worksNow g,T,hz,H,hM⟩, ⟨fun N p=> (hT N p).fromTop.inits.2.1,
    fun N m p hm=> ((hT N p).persists m (Nat.zero_le _) hm).continues.2⟩, fun N p=> (hT N p).fromTop.inits.2.2⟩
end launch
end YM.Extension.UV
