import YM.MergeProof.Tongue
/-! Spicy actual rebate budget independent of λ touches. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}{B:SectionData F}
    {R:Rep G n}
structure Attainment (P:BudgetPoint)(o:Site n)(f:Response G n) (x:ℝ):Prop where
   shaped i: Local.Attaches P.threshold i (f i)
   marked i:f i≠0 → o∈i
   toll:∃ v: Support n→ℝ, SumBudget (fun i=>reservedMass P i (v i)) x ∧∀ i,0≤v i∧∀ U,‖f i U‖ ≤ v i
lemma Attainment.blank (P:BudgetPoint): Attainment (G:=G) P o 0 0:= ⟨fun _ =>Attaches.zero _ _,by simp,fun _=>0,by simp [SumBudget,reservedMass]⟩
variable {X:ℕ→Support n}{M:Local.Raw F n} {Z:Hol G}{a b c w v y z g g' c':ℝ}
private abbrev glass (A:Activities G n) := { A with forced:=fun i=> {A.forced i with extraTest:=fun _ => True} }
private abbrev glassPlate (R:Rep G n) := { R with activities := glass R.activities }
private def crossed (A : Activities G n) {ι : Type*} (X : ι → Support n) : Letters (glass A) X ≃ Letters A X :=
  Equiv.sigmaCongrRight fun _i => (Equiv.refl (Finset ℕ)).subtypeEquiv
    (fun _x => ⟨fun h => ⟨h.1,h.2,h.3⟩,fun h => ⟨h.1,h.2,h.3⟩⟩)
private def cusps (S : Berths R.p R.activities X) : Push.Local.Slots (glassPlate R).activities X where
  label := (crossed R.activities X).toEmbedding.trans S.label
  support u := S.support ((crossed R.activities X) u)
  inventory u := S.inventory ((crossed R.activities X) u)
  allows _ _ := trivial
variable (S:Berths R.p R.activities (fun i=> joint B o (X i)))
private lemma caput {X:ℕ→Support n} (Y:Berths R.p R.activities X) (p:ℕ→Config G n→ℂ) (hs:Dominated ((cusps Y).pack R.p.threshold p)):
   profile R.activities ((cusps Y).pack R.p.threshold p)= hook R.activities R.p.threshold (clipSum X p):=by
   let A:= R.activities; let T:=cusps Y; let x:=R.p.threshold
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
lemma limb (h: Local.ForceCost R.p R.activities M.forced b): Dominated M.forced:=by
   obtain ⟨v,h,q⟩:=h; exact ⟨_,h.2.1,fun i x=> ((q i).2 _).trans (R.p.loMass _ _ (q i).1)⟩
lemma budgetProfile (h:Tare M o X Z B R v w c a b y)(hf:M.Format o X R)(hu:Readable Z B R.p n v) (hw:R.Lawful z g g' c' w)(hc:0<c):
    profile R.activities (mint S M Z).forced= profile R.activities M.forced + hook R.activities R.p.threshold (clipSum (fun i=>joint B o (X i)) (fun i=> rebate Z B o (X i) R.p.threshold (M.bulk i))):=by
    let f:= M.forced; let F (i):= rebate Z B o (X i) R.p.threshold (M.bulk i); let g:= (cusps S).pack R.p.threshold F
    have he:(mint S M Z).forced=f+g:=rfl -- may fail
    have hT:=tab_mint S hf hw hc hu h; have hd : Dominated f:= limb h.packets; have hp:Dominated g:=by
       have hh := rem_dominated (hT.bound le_rfl); rw [he] at hh
       obtain ⟨a,ha,hq⟩:=hh; obtain ⟨c,hc,h⟩:=hd; refine ⟨_,ha.add hc,fun i U=>?_⟩
       rw [show g i U=(f+g) i U-f i U by simp]; exact (norm_sub_le ..).trans (add_le_add (hq ..) (h ..))
    rw [he,← caput S F hp]; funext i U
    change ∑' j : {j // barcode R.activities j=i},(f j U+g j U)=_+_
    exact Summable.tsum_add ((hd.summable U).comp_injective Subtype.val_injective) ((hp.summable U).comp_injective Subtype.val_injective)
def coda (B:SectionData F)(Z:Hol G)(o:Site n)(X:ℕ→Support n)(M:Local.Raw F n)(R:Rep G n):= clipSum (fun i=>joint B o (X i)) (fun i=> rebate Z B o (X i) R.p.threshold (M.bulk i))
lemma vigor (h:Planned.GuardedAtom.Deck M o X R c a b)(hf:M.Format o X R)(he:Readable Z B R.p n v): Attainment R.p o (coda B Z o X M R) (Local.factor Z B R.p.supportExponent v*a):=by
   let Y i:=joint B o (X i); let f i:= rebate Z B o (X i) R.p.threshold (M.bulk i); let c:= coda B Z o X M R
   have hx(i): Attaches R.p.threshold (Y i) (f i):= (convert_atom o he (hf.regular i)).2.2.2
   have hu(p:Support n)(i:{i// Y i=p}): Attaches R.p.threshold p (f i.val):= (congr_arg (fun j=> Attaches R.p.threshold j (f i.val)) i.property).mp (hx i.val)
   have hh p: Attaches R.p.threshold p (c p):=by
      refine ⟨fun U V hA ht=>tsum_congr (fun i=> (hu p i).sites U V hA ht),fun g U=> tsum_congr (fun i=> (hu p i).symmetry g U),Measurable.tsum (fun i=> (hu p i).borel),fun U hU=>?_⟩; exact (tsum_congr (fun i=> (hu p i).healthy_zero U hU)).trans tsum_zero
   obtain ⟨e,hp,hq⟩:= h.bulk
   have hZ:=he.nonneg
   let u:= atomPrice Z F v; have hz: 0≤ u:= zero_le_one.trans (atomPrice_ge_one Z F he.nonneg)
   let y:= Local.factor Z B R.p.supportExponent v; have hy:0≤ y:=mul_nonneg (Real.exp_pos _).le hz
   let d i:= u*e i; have hd i:d i≥0:=mul_nonneg hz (hp i).1
   let g i:= reservedMass R.p (Y i) (d i)
   have ht: SumBudget g (y*a):= Local.sumBudget_mono (Local.sumBudget_mul_left hq hy) (fun i=> mul_nonneg (Real.exp_pos _).le (hd i)) (fun i=> price_join B Z o (hf.origin i) he.sound he.nonneg (hp i).1) le_rfl
   have hg:= heavy Y ht.2.1
   have hdq:Summable d:= ht.2.1.of_nonneg_of_le hd (fun i=>le_mul_of_one_le_left (hd i) (Real.one_le_exp (mul_nonneg (add_nonneg R.p.exponent_pos.le zero_le_two) (by positivity))))
   have hfp (p:Support n) : reservedMass R.p p (cram Y d p)= cram Y g p:=by
      unfold reservedMass cram; rw [← tsum_mul_left]; exact tsum_congr fun i=>congr_arg (fun p=>reservedMass R.p p (d i.val)) i.property.symm
   refine ⟨hh,fun i h=> ?_,cram Y d,⟨fun i=>mul_nonneg (Real.exp_pos _).le (tsum_nonneg (fun i=> hd i.val)),?_,?_⟩,fun i=>⟨tsum_nonneg (fun j=>hd j.val),fun U=>metric_cram _ hdq (fun i=> (charge_atom o he (hf.regular i) (hp i)).2 U) i⟩⟩ -- renamed hf shadow
   · by_contra hi; haveI : IsEmpty {j// Y j=i}:=⟨fun ⟨j,h⟩=> hi (h ▸ ((convert_atom o he (hf.regular j)).2.1))⟩ -- edit anchor; j hx. M hf
     apply h; funext U; change cram Y (fun i=> f i U) i=0; unfold cram;rw [tsum_empty]
   · simp_rw [hfp]; exact hg.summable
   simp_rw [hfp,hg.tsum_eq]; exact ht.2.2
end YM.MergeProof
