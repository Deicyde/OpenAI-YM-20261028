import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Vegetal

/-!
# Orbit obligations on v.R sprint unmarked
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Vale
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pot Marker Next.Rank Next.Rank.Value
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W : ℝ} {A : Stores S} {v : Dyed G S} {P : Teller G}
variable (H : Draft v P x W) (M : Plate v x W) (O : Orchard S)
local notation "Z"=>amount H M O
local notation "T"=>sprouting H M O

def travelHerb (S : StepData c f) (x : ℝ) (e : Wheel c) : Equiv.Perm (Herbs S x) := Equiv.sumCongr (traveling S x e) (Equiv.sumCongr (pursuit S e) (garden (orient e)))
lemma carries (i:Herbs S x) (e : Wheel c) :
    let a:= Z i; let b:= Z (travelHerb S x e i)
    b.X=pushed e a.X ∧ b.supplies=pushed (inflow S e) a.supplies ∧ b.goal=pushed e a.goal ∧ b.permit.1=a.permit.1.map (Locations.shiftFaces e.1 (S.ratio.embed e.2)).toEmbedding ∧ b.permit.2=a.permit.2.map (StepData.sendBonds e.1 e.2).toEmbedding:= by
  intro a b; rcases i with i|i|i
  · let j:=(hoop S x e).symm (rips i)
    have hx:rips (traveling S x e i)=j:=rfl
    have h': hoop S x e j=rips i:= Equiv.apply_symm_apply ..
    have ht:j.val.flags=pushed e (rips i).val.flags ∧ j.val.costs=(rips i).val.costs.map (Locations.shiftFaces e.1 (S.ratio.embed e.2)).toEmbedding ∧ j.val.aisles=(rips i).val.aisles.map (StepData.sendBonds e.1 e.2).toEmbedding:= by
      have hm (V : Stores S) (hp : V=book e.1 e.2 j.val): j.val.flags=pushed e V.flags ∧ j.val.costs=V.costs.map (Locations.shiftFaces e.1 (S.ratio.embed e.2)).toEmbedding ∧ j.val.aisles=V.aisles.map (StepData.sendBonds e.1 e.2).toEmbedding:=by subst V; refine ⟨?_,?_,?_⟩ <;> (ext; simp only [pushed,book,mem_map_equiv,Equiv.symm_symm,orient,Equiv.apply_symm_apply])
      exact hm _ (congr_arg Subtype.val h'.symm)
    have he:=hoop_day S x e j; rw [h'] at he; exact ⟨he.symm,rfl,ht⟩
  · refine ⟨flight ..,Finset.map_empty ..|>.symm,?_⟩
    change (store S ∅).flags = _ ∧ (store S ∅).costs=_ ∧ (store S ∅).aisles=_
    refine ⟨?_,?_,?_⟩ <;> (ext; simp [store,a,bread, amount, pushed])
  refine ⟨rfl,Finset.map_empty ..|>.symm,?_⟩
  change (store S ∅).flags=_ ∧ (store S ∅).costs=_ ∧ (store S ∅).aisles=_
  refine ⟨?_,?_,?_⟩ <;> (ext; simp [store,a,bread, amount, pushed])

lemma abroad (e : Wheel c) : Across Z Z (travelHerb S x e) (orient e) (orient (inflow S e)) := by
  let D:= travelHerb S x e; have h i:= carries H M O i e
  refine ⟨fun i=>(h i).1,fun i=>(h i).2.2.1,fun i=>(h i).2.1,fun i=>(h i).2.1,fun i=>?_,fun _=> Finset.map_empty .. |>.symm,fun _=>rfl,fun _=>rfl⟩
  rcases i with i|i; exact (h (.inl i)).1
  exact Finset.map_empty .. |>.symm
local notation "Rin"=>Sprigs H M O
lemma carrying (i : Rin) (e : Wheel c) :
    let a:=T i; let b:= T ((abroad H M O e).crosses i)
    b.zone=pushed e a.zone ∧ b.down=pushed e a.down ∧ b.up=pushed (inflow S e) a.up ∧ b.data.1=Finset.map (shiftFaces e.1 (S.ratio.embed e.2)).toEmbedding a.data.1 ∧ b.data.2= Finset.map (StepData.sendBonds e.1 e.2).toEmbedding a.data.2:= by
  intro a b; let F:=abroad H M O e
  refine ⟨F.zone_covers i,F.ticket_covers i,migration (orient (inflow _ _)) _ _ _ _ F.marks,?_⟩
  suffices h:∀ s:Finset (Herbs S x),(glow Z (s.map (travelHerb S x e).toEmbedding)).1=(glow Z s).1.map (shiftFaces e.1 (S.ratio.embed e.2)).toEmbedding ∧ (glow Z (s.map (travelHerb S x e).toEmbedding)).2= (glow Z s).2.map (StepData.sendBonds e.1 e.2).toEmbedding from h i.val
  intro s; induction s using Finset.induction_on with
  | empty=> simp [glow]
  | insert i s he ih=>
    unfold glow at *; simp only [map_insert, sup_insert, Equiv.toEmbedding_apply, Prod.fst_sup,Prod.snd_sup,ih.1,ih.2,(carries H M O i e).2.2.2.1,(carries H M O i e).2.2.2.2]; exact ⟨(Finset.map_union ..).symm,(Finset.map_union ..).symm⟩

-- fresh key Archive.No-mark summable via genuine source. Need move across supports alone, no exchange K equalities needed

def reenact (e : Wheel f): Equiv.Perm (addressKey f) := Equiv.subtypeEquiv ((orient e).finsetCongr.prodCongr (orient e).finsetCongr) fun _ => and_congr Finset.map_nonempty.symm Finset.map_subset_map.symm

lemma archive_turn (e : Wheel f) (A : Activities G f) (M : A.Moves e.1 e.2) (i : addressKey f) (U : Config G f): Archive A i (pull e.1 e.2 U)= Archive A (reenact e i) U:= by
  unfold Archive; nth_rw 2 [← (M.kp).tsum_eq ..]
  apply tsum_congr; intro j
  have he : meterAddress (A.forced (M.kp j)) = reenact e (meterAddress (A.forced j)):= by
    apply Subtype.ext; apply Prod.ext
    · change _=Finset.map _ (A.forced j).support; rw [Finset.map_eq_image]; exact M.forced_support j
    change _=Finset.map _ (A.forced j).inventory; rw [Finset.map_eq_image]; exact M.forced_inventory j
  refine if_congr (by rw [he]; exact (reenact e).injective.eq_iff.symm) (M.valuesK ..).symm rfl

lemma sees_moon (A B : Stores S) (k t : Streak O) (p:Config G c) (y : RoomView A x k.wood G) (e : Wheel c) (he : B=book e.1 e.2 A) (ht : t.tag=ticket e.1 e.2 k.tag) (hp : t.wood=Locations.forest e.1 e.2 k.wood) :
    spires e ⟨A,k.wood,k.tag,p,y⟩=(⟨B,t.wood,t.tag,pull e.1 e.2 p, transit hp he p y⟩:Pilot G S x):= by
  suffices H:∀ (V₀ : Forest S.ratio) (k' : S.Choices) (B : Stores S) (he : B=book e.1 e.2 A) (hp : V₀=Locations.forest e.1 e.2 k.wood), k'=ticket e.1 e.2 k.tag → spires e ⟨A,k.wood,k.tag,p,y⟩=(⟨B,V₀,k',pull e.1 e.2 p,transit hp he p y⟩:Pilot G S x) from H _ _ _ he hp ht
  rintro V₀ k' B rfl rfl rfl; rfl

lemma ship_wing (e : Wheel c) (Q : Support f) (B : ℕ): pushed e (wings S B Q)=wings S B (pushed (inflow S e) Q):= by
  unfold wings; rw [push_walk]; congr 1; unfold pushed; simp_rw [Finset.map_eq_image,image_image]; congr 1; funext i; exact (parent_map ..).symm

local notation "can"=> Orchard.canopy S
local notation "bank"=>amount H M can
local notation "branch"=> Sprigs H M can
-- lantern signs

def foliage : Lantern G S:=⟨v.chi,v.arc,H.pos,H.radius,can⟩

def shiftZ {p q : BudgetPoint} (h : p=q) (a : Zest G S x O p.threshold) : Zest G S x O q.threshold:= h ▸ a
lemma vessels (R : Rep G c) {o m Λ δ η : ℝ} (hR : v.source.Lawful o m Λ δ η) (hm : R.p=v.bp) (he : 25*radiusB x+30≤ R.p.B) (e : Wheel c):
    let p:=fun i=> shiftZ can hm.symm (sprouting H M can i)
    Nonempty (Voyage (unmarked v.source R p (L:=foliage H) H.enrolled he (blink S) hR) e.1 e.2):= by
  intro w; let Q:= unmarked v.source R w (L:=foliage H) H.enrolled he (blink S) hR
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
end YM.PhysicalNext.InteractingRank.Pump.Vale
