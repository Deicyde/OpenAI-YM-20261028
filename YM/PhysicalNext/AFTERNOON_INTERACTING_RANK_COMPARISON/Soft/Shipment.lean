import YM.AnalyticNext.QUARTIC_MATCH.Radius.Basin
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Fruit
import YM.Further.QUANTUM_RATES_PORT.Radiation
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Gush
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Tissue
import YM.Progress.CLASSICAL_KIN_RECURSION.Customs
import YM.Progress.CLASSICAL_KIN_RECURSION.Delta
import YM.Push.LOOP_COEFFICIENT.Block.Spend
import YM.Push.LOOP_COEFFICIENT.Resolution
/-! # Need Voyage involving K, relying on its Moves in the whitened calculation

(From stage-1 Waylay, don't assume forest transports for
c satisfying only nominal invariance.) -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pump Pump.Pot Pump.Vale Marker Next.Rank Next.Rank.Value
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W : ℝ} {A : Stores S} {v : Dyed G S} {P : Teller G}
variable (H : Draft v P x W) (M : Plate v x W) (O : Orchard S)
local notation "can"=> Orchard.canopy S
local notation "bank"=>amount H M can
local notation "branch"=> Sprigs H M can
lemma husks (R : Rep G c) {o m Λ δ η : ℝ} (hR : (white v.source).Lawful o m Λ δ η) (hm : R.p=v.bp) (he : 25*radiusB x+30≤ R.p.B) (e : Wheel c):
    let p:=fun i=> shiftZ can hm.symm (sprouting H M can i)
    Nonempty (Voyage (unmarked (white v.source) R p (L:=foliage H) H.enrolled he (blink S) hR) e.1 e.2):= by
  intro w; let Q:= unmarked (white v.source) R w (L:=foliage H) H.enrolled he (blink S) hR
  let F:= abroad H M can e; let E:= Equiv.sumCongr (Equiv.sumCongr F.crosses (reenact (inflow S e))) (Equiv.refl Empty)
  obtain ⟨κ,hκ⟩:= progress_tag (Orchard.transportable S e.1 e.2)
  -- shiftZ motion
  have hx (Q : BudgetPoint) (he : Q=v.bp) (i : branch):
      let X:=sprouting H M can i; let u:= shiftZ can he.symm X
      X.zone=u.zone ∧ X.up=u.up ∧ X.down=u.down ∧ X.data=u.data ∧ X.weight=u.weight:= by rintro X u; subst Q; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have hp (i) : (w (F.crosses i)).zone=pushed e (w i).zone ∧ (w (F.crosses i)).down=pushed e (w i).down ∧ (w (F.crosses i)).up=pushed (inflow S e) (w i).up ∧ (w (F.crosses i)).data.1=(w i).data.1.map (shiftFaces e.1 (S.ratio.embed e.2)).toEmbedding ∧ (w (F.crosses i)).data.2=(w i).data.2.map (StepData.sendBonds e.1 e.2).toEmbedding:= by unfold w; simp_rw [fun i=> (hx _ hm i).1.symm, fun i=>(hx _ hm i).2.1.symm, fun i=>(hx _ hm i).2.2.1.symm, fun i=>(hx _ hm i).2.2.2.1.symm]; exact carrying H M can i e
  refine ⟨⟨E,?_,κ,(fun k=>(hκ k).1),(fun k=>(hκ k).2),?_,?_⟩⟩
  · constructor <;> rintro ((i|i)|i) <;> first|exact i.elim|exact (hp _).1|exact (hp i).1|exact (hp i).2.1|exact (hp i).2.2.1|rfl|exact (ship_wing e i.val.1 R.p.B (S:=S)).symm
  · rintro ((i|i)|i)
    · exact (hp i).2.2.2
    · exact ⟨(Finset.map_empty ..).symm,(Finset.map_empty ..).symm⟩
    exact i.elim
  rintro ((i|i)|i) V A hV k y
  · change (w i).weight _ _ _ _= (w (F.crosses i)).weight A _ _ _
    unfold w; simp_rw [fun i=>(hx _ hm i).2.2.2.2.symm,contracts]
    let p:Pilot G S x:= ⟨A,k.wood,k.tag,V,y⟩; have hr:=sees_moon can _ _ k (κ k) V y e rfl ((hκ k).2) ((hκ k).1)
    refine congr_arg Complex.ofReal (Eq.trans ?_ (show (∏ j∈i.val,atomP W v M j (spires e p))=_ from ?_))
    · exact congr_arg (fun p=> (∏ j∈ i.val,atomP W v M j p)) hr.symm
    change _= ∏ j∈i.val.map (Equiv.toEmbedding (travelHerb S x e)),atomP W v M j p; rw [prod_map]
    exact prod_congr rfl fun j _=> (plate_tag _ _ M H.enrolled H.width H.pos H.radius j|>.2.2 p e).symm
  · let b:= spires e ⟨A,k.wood,k.tag,V,y⟩; let V':=v.top b
    change (↑(Archive _ i (gazed v.things _ (foliage H).χ _ _ _ (foliage H).hood _)):ℂ)=↑(Archive _ (reenact (inflow S e) i) (gazed v.things _ (foliage H).χ _ _ _ (foliage H).hood _))
    apply congr_arg
    have hr := sees_moon can _ _ k (κ k) V y e rfl ((hκ k).2) ((hκ k).1); have hz := congr_arg v.top hr
    exact (congr_arg (Archive _ i) (hz.symm.trans (v.top_ship e H.enrolled.funded _))).trans (archive_turn (inflow S e) _ (hR.labels.moves _ _).some i _)
  exact i.elim
end YM.PhysicalNext.InteractingRank.Soft
