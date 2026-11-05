import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Parades
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Arc.Frames
import YM.Push.LOCAL_SPLITTING.Padding
import YM.SectorNext.RECONNECTED_LOCALITY.Cleft
/-!
# Forest voyage each unmarked bill

Symmetry data from the reads & forest law *before* integration;
give the Layout's registers after integration and assembly
on that very park and alphabet. Nothing about whether the appraisal
fits that path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussianLaws.Local AnalyticBridge.GaussianFieldAlignment.Gauges AnalyticBridge.GaussianFieldAlignment.Tensor SectorTools.PhysicalGaussianSwitch AnalyticBridge.GaussianFieldAlignment.Agreements
     Flux Bid SectorNext.Vacuum Precision AnalyticBridge.GaussianFieldAlignment
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S} {O : Orchard S} {R : Rep G c}
    {A B : Stores S} {P : Teller G} {W ι κ α β : Type} [Fintype W] [DecidableEq W] {u : W → Site c}

lemma turn_walk (s : Signed) (b : Site c) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) (h : P.Funds S T) (he : (palette T A F k x V .endpoint).PosDef) : MeasurePreserving (fun y : RoomView A x F G => cusps A F s b x V y)
    (viewer T A x F k V) (viewer T (Locations.book s b A) x (Locations.forest s b F) (Channels.ticket s b k) (pull s b V)):=by
  have hf : MeasurePreserving (Channels.rollY s b x A F) (piHaar G (Frozen A x F)) (piHaar G (Frozen (Locations.book s b A) x (Locations.forest s b F))):= by
    let Y := Locations.book s b A; let F':=Locations.forest s b F
    let q := Locations.frozen s b A F x
    let p (i : Frozen Y x F') (u : G.El):= if s.flip i.val.val.2 then u⁻¹ else u
    have hP i : MeasurePreserving (p i) G.probHaar G.probHaar:= by unfold p; split; exact G.preserve_inv; exact MeasurePreserving.id _
    exact (measurePreserving_pi _ _ hP).comp (AnalyticBridge.Sharp.Projection.pi_projection G.probHaar q.toEmbedding)
  have hz:= fanMap A F s b k h x V he
  -- explicit marginal via accepted aligned positive table
  obtain ⟨z,b',hc,_⟩:= h.feeds
  let J:= Orthogonal.warp (onBond (Channels.fiber s b V S)) (Locations.active s b A F x) (palette T A F k x V .endpoint)
  have hJ : palette T (Locations.book s b A) (Locations.forest s b F) (Channels.ticket s b k) x (pull s b V) .endpoint=J:= by
    unfold J; simp_rw [← Q_endpoint]; exact (Channels.turned_cov s b V k T x (h.knobs.symm ▸ h.kernel) A F (h.high.symm ▸ hc)).fog
  unfold viewer; rw [hJ]; exact hf.prod (warp_cloud _ _ _ he)
lemma dispatched (s : Signed) (x : Site c) {U : Config G c} : flags τ U = (flags τ (pull s x U)).map (StepData.sendSites s x).toEmbedding:= by rw [map_eq_image]; exact (Thirst.s_flags ..).symm
lemma progress_tag {s : Signed} {b : Site c} (hx : ∃ E : Equiv.Perm O.Seeds, ∀ t,O.grow (E t)=Locations.forest s b (O.grow t)) :
    ∃ j : Equiv.Perm (Streak O),∀ k,(j k).wood=Locations.forest s b k.wood ∧ (j k).tag=Channels.ticket s b k.tag:= by
  obtain ⟨E,H⟩:=hx
  let e:=Streak.entered S O
  exact ⟨(e.trans (E.prodCongr (S.withinChoice s b).symm)).trans e.symm,fun k=>⟨H _,rfl⟩⟩

section
variable {D : Forest S.ratio}
    {Y : Forest S.ratio} {V : Config G c}
-- no fake defEq of forest receipts
-- tree equality and store equality rather than quotient

def transit {s b} (h : Y=Locations.forest s b D) (he : B=Locations.book s b A) (V : Config G c) (y : RoomView A x D G) : RoomView B x Y G:=
  h.symm ▸ (he.symm ▸ cusps A D s b x V y)
lemma oriented (t u) {s b} (ht : t=Channels.ticket (S:=S) s b u) (h : Y=Locations.forest s b D) (he : B=Locations.book s b A) (hg : Boosted T P x) (hl : Positioned x A V):
    MeasurePreserving (transit h he V) (viewer T A x D u V) (viewer T B x Y t (pull s b V)):=by subst B;subst Y;subst t; exact turn_walk s b D u V hg.funded (hg.fogged _ _ _ _ hl)
end
section
variable (Q : ι→ PaintCan S G x O u τ)
-- buckets and affiliation ALWAYS located at site & tag. Here each partial
-- read also checks MP when consuming, even if not every tag occurs.
structure Voyage (s : Signed) (b : Site c) where
  orbit : Equiv.Perm ι
  orientation : Across Q Q orbit (StepData.sendSites s b) (StepData.sendSites s (S.ratio.embed b))
  turn : Equiv.Perm (Streak O)
  tree k : (turn k).wood=Locations.forest s b k.wood
  branch k : (turn k).tag=Channels.ticket s b k.tag
  tables i :
    (Q (orbit i)).permit.1=(Q i).permit.1.map (Locations.shiftFaces s (S.ratio.embed b)).toEmbedding ∧
    (Q (orbit i)).permit.2=(Q i).permit.2.map (StepData.sendBonds s b).toEmbedding
  exactAround i (V:Config G c) A (hV : Positioned x A V) k y :
    (Q i).lamp (Locations.book s b A) (turn k) (pull s b V) (transit (tree k) rfl V y)=(Q (orbit i)).lamp A k V y

namespace Voyage
variable {s : Signed} {b : Site c} {Q} (T' : Voyage Q s b)
lemma purchased i (U : Config G c): stapled x (glow Q i.val) (pull s b U)=Locations.book s b (stapled x (glow Q (T'.orientation.crosses i).val) U):= by
  let m:= glow Q i.val; let M:= glow Q (T'.orientation.crosses i).val
  let A:=stapled x M U
  let f := Locations.shiftFaces s (S.ratio.embed b); let F:=StepData.sendBonds s b
  have ht (s : Finset ι): (glow Q (s.map T'.orbit.toEmbedding)).1=(glow Q s).1.map f.toEmbedding ∧ (glow Q (s.map T'.orbit.toEmbedding)).2=(glow Q s).2.map F.toEmbedding:=by
    induction s using Finset.induction_on with
    | empty=>exact ⟨by simp [glow],by simp [glow]⟩
    | insert j s he ih=>
      unfold glow; rw [Finset.map_insert, sup_insert,sup_insert]; simp only [Equiv.toEmbedding_apply, Prod.fst_sup, Prod.snd_sup,(T'.tables j).1,(T'.tables j).2]; constructor
      · show _=_; change _∪(glow Q _).1= ((_∪(glow Q s).1).map _); rw [ih.1, Finset.map_union]
      change _∪(glow Q _).2= ((_∪(glow Q s).2).map _); rw [ih.2,Finset.map_union]
  have hF:(Locations.book s b A).flags=(stapled x m (pull s b U)).flags:= turns_marks s b A U (temp x) rfl
  have hh : M.1=m.1.map f.toEmbedding ∧ M.2=m.2.map F.toEmbedding:= ht i.val
  show (⟨m.1,m.2, flags (temp x) (pull s b U)⟩:Stores S)=⟨M.1.map f.symm.toEmbedding, M.2.map F.symm.toEmbedding,(Locations.book s b A).flags⟩
  congr 1
  · ext j; simp only [hh.1,mem_map_equiv,Equiv.symm_symm,Equiv.symm_apply_apply]
  · ext j; simp only [hh.2,mem_map_equiv,Equiv.symm_symm,Equiv.symm_apply_apply]
  exact hF.symm
lemma tribute (ht : Boosted T P x) (i : Club Q) (U : Config G c) : letter Q (T:=T) i (pull s b U)= letter Q (T:=T) (T'.orientation.crosses i) U:=by
  let j:= T'.orientation.crosses i; let C:= stapled x (glow Q i.val) (pull s b U); let A:=stapled x (glow Q j.val) U
  let X:=T'.turn
  unfold letter glance; apply Fintype.sum_equiv X.symm; intro k'; obtain ⟨k,rfl⟩:= X.surjective k'
  rw [Equiv.symm_apply_apply]
  have hf:(X k).share=k.share:= rfl
  rw [hf]; apply congr_arg
  let μ:=viewer T A x k.wood k.tag U; let ν:=viewer T C x (X k).wood (X k).tag (pull s b U)
  let w:= transit (T'.tree k) (show C=Locations.book s b A from T'.purchased i U) U (x:=x)
  have hz : MeasurePreserving w μ ν:= oriented _ _ (T'.branch k) (T'.tree k) (T'.purchased i U) ht (position ..)
  let H:=stage Q i.val C (X k) (pull s b U)
  have he:=pay_pull hz H (((observer Q i).placed C _|>.atLens (position ..)).aestronglyMeasurable)
  refine he.2.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun y=>?_))
  have h: ∀ (B : Stores S) (hv : B=Locations.book s b A),stage Q i.val B (X k) (pull s b U) (transit (T'.tree k) hv U y)=stage Q j.val A k U y:=by
    rintro B rfl
    unfold stage; change _=∏ a∈ i.val.map T'.orbit.toEmbedding, _
    rw [Finset.prod_map]
    exact prod_congr rfl fun a _=> T'.exactAround a U A (position ..) k y
  exact h _ _
lemma rebuilt (ht : Boosted T P x) : Waking (pull s b) (StepData.sendSites s b) T'.orientation.inn (gruel Q ht T'.orientation.shade) (gruel Q ht T'.orientation.shade):=by
  let H:=T'.orientation
  have hP(i:Inn Q):(gruel Q ht H.shade i).fires=quiet _:= Across.rises H.shade _
  refine ⟨fun i=>H.zone_covers i.val,fun i=>H.ticket_covers i.val,fun i U=> ?_,hP,hP⟩
  unfold gruel; simp only [foundering]
  have hz:validArea Q i.val (pull s b U)↔ validArea Q (H.inn i).val U:= by
    change _↔ validArea Q (H.crosses i.val) U; unfold validArea; rw [H.zone_covers,H.ticket_covers]; exact mark_pass _ _ _ _ _ (dispatched ..)
  exact if_congr hz (tribute T' ht _ _) rfl
end Voyage
end
end YM.PhysicalNext.InteractingRank.Display.Sew
