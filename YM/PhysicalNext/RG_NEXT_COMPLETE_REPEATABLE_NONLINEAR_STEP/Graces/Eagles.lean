import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
/-! # Same issuance including later retirement number.Formally enhanced Bake proves
      extra *properties of choices*, doesn't assume strokes of a history. Needs same Prog.D
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
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus  Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X: Metals G} {D:Rolls X.p}{A:Alloy X D} (R : Factor A)
def Protected (N m n : ℕ) (u:Rep G (A.B.a.S.side m n)) (v: Rep G (A.B.a.S.side (m+1) n)):Prop:=
    ∃ l t Q, ∃ H : Spring R N m n l t Q, ∃ x, x∈ Icc l t ∧ v=Q x∧u=H.result x
include R in
lemma hops (N p:ℕ):∃ F,Curve (A.B.a.budget N) (n:=A.B.a.S.side N p) F (band A.B.a N) ∧
    ∀ β∈band A.B.a N,(F β).beta=β ∧ Lives A.B.bake N N p (F β) ∧ A.B.bake.Starter N p (F β)∧ HasSlots (F β).p (F β).activities:=by
  let h:=R.machine; obtain ⟨X,d,hX⟩:= R.pledging.conducts.starts N p; let B:=A.B
  refine ⟨fun x=> fromTop A.B.kin N p x X (d x),hX.starts,fun β hp=> ⟨rfl,?_,?_,(hX.law β hp).ingredients.spare_room (B.kin.path N N) (B.a.params N).clip β 0⟩⟩
  · rw [h.ready]; exact ⟨rfl,rfl,rfl,⟨A.B.support.cap N N le_rfl,(hX.law β hp).ingredients.gates ..⟩, PeriodFuture.begin hp (hX.law β hp)⟩
  rw [h.ready]; exact starter (hX.law β hp) hp _ _

structure Nest (V:Bolt A) : Prop where
   born N p : HasSlots (V.history N p N).p (V.history N p N).activities
   held N m p (h: m<N):Protected R N m p (V.history N p m) (V.history N p (m+1)) ∧ Accurate A.B R.post N m p (V.history N p m) (V.history N p (m+1))
include g
lemma winnow : ∃ V:Bolt A,Nest R V:=by
  let B:= A.B
  let Y := { A.B.bake with next:=fun N m p u v=> A.B.Move N m p u v ∧ Protected R N m p u v∧Accurate A.B R.post N m p u v,
                           first:=fun N p v=> A.B.bake.first N p v∧ HasSlots v.p v.activities }
  have he N m p u: Lives Y N m p u ↔ Lives A.B.bake N m p u := by constructor <;> rintro ⟨a,b,c,d,e⟩ <;> exact ⟨a,b,c,d,e⟩
  have hp N p:Y.Issues N p:=by
    constructor
    · obtain ⟨F,h,hF⟩:= hops R N p
      exact ⟨F,h,fun x hx=> by obtain ⟨hv,hB,ht,hZ⟩:= hF x hx; exact ⟨hv,(he ..).2 hB,ht.scalars,ht.raw,ht.inits,hZ⟩⟩
    intro m hm l t hl Q hc hx
    obtain ⟨H⟩:= faces R Q hl hc (fun x hy=> ⟨(he ..).1 (hx x hy).1,(hx x hy).2⟩) hm
    obtain ⟨hq,hp⟩:= H.moves g hm
    refine ⟨H.result,hq,fun x hy=>?_⟩; obtain ⟨h,hK,hp,hV⟩:= hp x hy; exact ⟨(he ..).2 h.bundle,h.ident,(A.B.links hm h).drift,h,⟨l,t,Q,H,x,hy,rfl,rfl⟩,(by rw [show Accurate A.B R.post N m p (H.result x) (Q x)= (|(H.result x).beta - UVNext.CouplingReset.predictor A.B N Q x| ≤ UVNext.CouplingReset.width A.B.a m R.post) from by unfold Accurate UVNext.CouplingReset.predictor; rw [sub_add_eq_sub_sub]]; exact hK)⟩
  obtain ⟨T,hT,H⟩:= Y.races g hp (Drifting.pay A.B.valid)
  have hM (N m p:ℕ)(hm:m<N): A.B.Move N m p (T N p m) (T N p (m+1)):= ((hT N p).persists m (Nat.zero_le _) hm).continues.1
  have hz : A.B.bake.Stays T := by intro N p; have hf:= (hT N p).fromTop; exact ⟨fun i hi hj=> ⟨(he ..).1 ((hT N p).prices i hi hj).1,((hT N p).prices i hi hj).2⟩,⟨hf.scalars,hf.raw,hf.inits.1⟩,fun i hi hi'=>A.B.links hi' (hM N i p hi')⟩
  refine ⟨⟨R.worksNow g,T,hz,H,hM⟩,fun N p=>?_,fun N m p hm=> ((hT N p).persists m (Nat.zero_le _) hm).continues.2⟩
  exact (hT N p).fromTop.inits.2
namespace Nest
variable {R} {X':Bolt A}
local notation "H"=> Issue.trail X'
lemma samples (h:Nest R X') (N m p:ℕ)(hm:m≤N):HasSlots ((H).rep N p m).p ((H).rep N p m).activities:=by
  rcases eq_or_lt_of_le hm with hm|hf
  · subst m; exact h.born ..
  obtain ⟨l,t,Q,hT,x,hx,hQ,hK⟩:= (h.held N m p hf).1
  change HasSlots (X'.history N p m).p (X'.history N p m).activities; rw [hK,hT.owns g hf hx]
  have hb:= hT.core hf x hx; have hp:= (R.machine.passes hf hT.knows).1
  exact (hb.renew g (A.B.support.cap N m hf.le) hp.decent hp.width _ (Return.enough_room ..) (hp.fees x hx)).spare_room ..
end Nest
end YM.PhysicalNext.Repeat.Graces
