import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Seaports
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Seers
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Sequence
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.MergeProof.Buys
import YM.MergeProof.Tongue
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Views
import YM.Next.RANK.HomeSync
import YM.Next.RANK.SealMix
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsColumnL
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Gala


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type}[Countable ι]{d:ℕ}{F:Labels.Frame G d}{o:Site n}{R:Rep G n}
private abbrev glass (A:Activities G n) := { A with forced:=fun i=> {A.forced i with extraTest:=fun _ => True} }
private abbrev glassPlate (R:Rep G n) := { R with activities := glass R.activities }
private def crossed (A : Activities G n) {ι : Type*} (X : ι → Support n) : Letters (glass A) X ≃ Letters A X :=
  Equiv.sigmaCongrRight fun _i => (Equiv.refl (Finset ℕ)).subtypeEquiv
    (fun _x => ⟨fun h => ⟨h.1,h.2,h.3⟩,fun h => ⟨h.1,h.2,h.3⟩⟩)
private def cups {ι:Type*}{X:ι →Support n}(S : Berths R.p R.activities X) : Push.Local.Slots (glassPlate R).activities X where
  label := (crossed R.activities X).toEmbedding.trans S.label
  support u := S.support ((crossed R.activities X) u)
  inventory u := S.inventory ((crossed R.activities X) u)
  allows _ _ := trivial
omit [Countable ι] in
private lemma capute {X:ι→Support n} (Y:Berths R.p R.activities X) (p:ι→ Config G n→ℂ) (hs:Dominated ((cups Y).pack R.p.threshold p)):
   profile R.activities ((cups Y).pack R.p.threshold p)= hook R.activities R.p.threshold (clipSum X p):=by
   let A:= R.activities; let T:=cups Y; let x:=R.p.threshold
   have hev(q U): T.pack x p (Y.label q) U=p q.1 U*grasp A x (X q.1) q.2.val (fusionBox A (X q.1) q.2.val) U:=by
     let J:=crossed A X; obtain ⟨i,rfl⟩:= J.surjective q
     rw [show Y.label (J i)= T.label i from rfl,T.pack_label]
     unfold Slots.payload; change _ = p i.1 U*grasp A x (X i.1) i.2.val (fusionBox A (X i.1) i.2.val) U; unfold grasp
     have hP: Local.Packs A (X i.fst) (i.2.val):=(J i).2.property
     have he : ((glassPlate R).activities.forced (T.label i)).eligible x U ↔ (fusionBox A (X i.fst) (i.2.val)).1∩flags x U=(fusionBox A (X i.fst) (i.2.val)).2:=by
          unfold ForcedAddress.eligible
          rw [show ((glassPlate R).activities.forced (T.label i)).support = _ from T.support i, show ((glassPlate R).activities.forced (T.label i)).inventory = _ from T.inventory i]; exact ⟨fun h=> h.1,fun h=>⟨h,trivial⟩⟩
     split_ifs with h h'
     · rfl
     · exact (h' ⟨hP,rfl,he.1 h⟩).elim
     · rename_i h'; exact (h (he.2 h'.2.2)).elim
     rw [mul_zero]
   apply toll (e:= Y.label) (fun i=>Prod.ext (Y.support _) (Y.inventory _)) hev (fun i hi=> ?_) hs
   apply Push.Local.Slots.pack_none
   rintro ⟨i,h⟩; exact hi ⟨crossed R.activities X i,h⟩
private lemma glassWorks {η σ w C Λ:ℝ}(hx:R.Lawful σ C Λ w η) : (glassPlate R).Lawful σ C Λ w η:=by
  let K := (glass R.activities)
  have hu := hx.labels
  have hf := hu.forced
  have he : K.ForcedFamily R.p := ⟨hf.sym, fun _ _ _ => Iff.rfl, hf.meas, fun _ => MeasurableSet.univ, hf.reads, fun _ _ _ _ _ => rfl,
    fun i U h => ⟨(hf.permit i U h).1,trivial⟩⟩
  refine ⟨hx.paths,⟨hu.regular.smooth,hu.regular.at_flat,hu.regular.vanish⟩,he,fun s o => ?_,hu.boundE,hu.boundK⟩
  obtain ⟨m⟩ := hu.moves s o
  exact ⟨m.ep,m.kp,m.reg_site,m.reg_support,m.forced_support,m.forced_inventory,fun _ _ => Iff.rfl,m.valuesE,m.valuesK⟩
section
variable (R : Rep G n) {f:ι→ Config G n→ℂ} {A:ι→ℝ} {η σ w C Λ t:ℝ} (h:R.Lawful σ C Λ w η){X:ι→Support n}(S:Berths R.p R.activities X)
set_option quotPrecheck false
include h S
local notation "F!"=> ((cups S).pack R.p.threshold f)
omit [Countable ι] in
lemma garnish (hp:∀ i,o∈X i)(hf:∀ i, Attaches R.p.threshold (X i) (f i))(ht:∀ i,0 ≤ A i)(hx:∀ i U,‖f i U‖≤ A i)(hd:SumBudget (fun i=>mergePrice R.p η (X i) (A i)) t) (hQ:Summable A):∃ F:ℕ → Config G n→ℂ,ForceFormat R.p R.activities o F∧ ForceCost R.p R.activities F t∧ profile R.activities F= hook R.activities R.p.threshold (clipSum X f) ∧ ∀ U:Config G n, HasSum (fun b=> gasMark R.p R.activities U b F) ((∑' i,f i U)*(R.activities.gas R.p U:ℂ)):=by
    let e:= cups S; have hh: ForceCost R.p R.activities (F!) t:= Slots.forceCost e h.labels.boundK hd ht hx -- test accepting different A
    have hy:= glassWorks h; have hz:= e.forceFormat hy.labels.forced hp hf
    have hP: Dominated (F!):=by obtain ⟨v,h,q⟩:=hh; exact ⟨_,h.2.1,fun i x=> ((q i).2 _).trans (R.p.loMass _ _ (q i).1)⟩
    refine ⟨_,⟨fun i U he=> ?_,hz.carried,hz.invariant,hz.supported,hz.borel⟩,hh,capute S f hP, fun U=>?_⟩
    · refine ⟨(hz.forcing i U he).1,?_⟩
      obtain ⟨s,hs⟩:∃ s,S.label s=i:=by by_contra H; apply (he (?_)).elim; apply (congr_fun (e.pack_none R.p.threshold f i (fun ⟨s,hs⟩=>H ⟨crossed _ _ s,hs⟩)) U)
      subst i; exact S.pass s U ((hz.forcing _ U he).1)
    have hh:= e.recover R.p U f hf hy.labels (Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=> hx i U) hQ)
    -- Function defeq might fail Classical.dec predicates
    convert hh using 1 <;> rfl
end
end YM.MergeProof
