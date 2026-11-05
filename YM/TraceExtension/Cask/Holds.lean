import YM.TraceExtension.Cask.Incidence
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Function
open scoped Classical
variable {I V:Type*}[DecidableEq I][DecidableEq V]{n:Side}
variable (P:Staff V I n) {q r:Finset I} {T:Support n}{i b:Finset (Finset I)}
abbrev bulk (i b:Finset (Finset I)):= (i∪b).biUnion id
def flot (T:Support n) (q:Finset I) := (cohorts P q).filter (fun s=> Disjoint (hill P s) T)
def hang (T:Support n)(q:Finset I):=cohorts P q \ flot P T q
def base (T:Support n)(q:Finset I):= Ac.Parts P.foot ((hang P T q).biUnion id)
variable {P}
lemma cohort_fill (h:((i:Set (Finset I))).PairwiseDisjoint (crew P)): cohorts P (i.biUnion id)=i.biUnion (cohorts P):=by
   let Q:=i.biUnion (cohorts P)
   have hx: Q.biUnion id=i.biUnion id:=by rw[show Q=_ from rfl,biUnion_biUnion]; simp only [cohorts,reconstruct]; rfl
   rw[← hx]; refine Ac.separates _ _ (fun t ht=> ?_) (fun u hu v hv huv=> ?_)
   · obtain ⟨q,hq,ht⟩:= mem_biUnion.mp ht; exact (Ac.lives _ _ ht).2
   change u∈Q at hu; change v∈Q at hv; obtain ⟨s,hs,hp⟩:= mem_biUnion.mp hu; obtain ⟨t,ht,hq⟩:= mem_biUnion.mp hv
   by_cases he:s=t
   · subst t; exact Ac.separate _ s hp hq huv
   simp_rw [net P]; refine disjoint_left.mpr fun x hx hy=> ?_
   obtain ⟨a,ha,rfl⟩:= mem_image.mp hx; obtain ⟨j,hb,e⟩:=mem_image.mp hy; obtain rfl:= P.seat.injective e
   obtain ⟨c,hc,hx⟩:=mem_biUnion.mp ha; obtain ⟨d,hd,hy⟩:=mem_biUnion.mp hb; exact disjoint_left.mp (h hs ht he) (mem_biUnion.mpr ⟨c,(lives _ _ hp).1 hc,hx⟩) (mem_biUnion.mpr ⟨d,(lives _ _ hq).1 hd,hy⟩)
lemma tank_coh (q:Finset I): ((Ac.Parts P.foot q):Set _).PairwiseDisjoint (crew P):=by
    intro s hs t ht h; apply disjoint_left.mpr; intro j hj hx; exact disjoint_left.mp (Ac.separate P.foot q hs ht h) (starred P s (mem_image_of_mem _ hj)) (starred P t (mem_image_of_mem _ hx))
lemma group_pull (s r : Finset I) (hr:s∈Parts P.foot r)(t:Finset I)(ht:t∈cohorts P s): t∈cohorts P r:=by
   have hx : cohorts P r=(Parts P.foot r).biUnion (cohorts P):=by simpa only [reconstruct] using cohort_fill (P:=P) (tank_coh r)
   rw [hx]; exact mem_biUnion.mpr ⟨s,hr,ht⟩
lemma Haven.separateX (h:Haven P T i b) : i.biUnion (cohorts P)=i:=by
   have ht s (hs:s∈i): cohorts P s={s}:=by
       have hz:= Ac.separates (sector P) {s} (fun t ht=> (mem_singleton.mp ht).symm ▸ ((h.ice s hs).1.force)) (by simp)
       simpa using hz
   calc
    i.biUnion _ = i.biUnion (fun s=>{s}):= by
       ext t; simp only [mem_biUnion]; exact exists_congr fun s=> and_congr_right fun hs=> by rw [ht s hs]
    _ = _:=by ext; simp
lemma Haven.no_overlap (h:Haven P T i b): Disjoint i (b.biUnion (cohorts P)):=by
    refine disjoint_left.mpr fun u hu h'=>?_ ; obtain ⟨s,hs,H⟩:=mem_biUnion.mp h'; exact (h.boat s hs).2.1 u H (h.ice u hu).2
lemma Haven.recover (h:Haven P T i b): flot P T (bulk i b)=i ∧ base P T (bulk i b)=b:=by
    have hy:cohorts P (bulk i b)=i∪(b.biUnion (cohorts P)):=by rw[bulk,cohort_fill h.apart,union_biUnion,h.separateX]
    have hx:flot P T (bulk i b)=i:=by
       rw [flot,hy]; ext v; constructor
       · intro he; obtain ⟨he,hx⟩:=mem_filter.mp he; refine (mem_union.mp he).resolve_right (fun H=>?_); obtain ⟨s,hs,h⟩:=mem_biUnion.mp H; exact absurd hx ((Haven.boat (P:=P) ‹_› _ hs).2.1 _ h)
       intro ht; exact mem_filter.mpr ⟨mem_union_left _ ht,(h.ice v ht).2⟩
    refine ⟨hx,?_ ⟩
    unfold base hang; have hp:=h.spatial; rw [hx,hy, union_sdiff_left, sdiff_eq_self_of_disjoint (Haven.no_overlap h).symm,biUnion_biUnion]; simp_rw [cohorts,reconstruct]; exact Ac.separates _ _ (fun s hs=> (h.boat s hs).1.force) hp
lemma Haven.dry (h:Haven P T i b):Disjoint i b:= by refine disjoint_left.mpr fun t ht hh=> ?_; exact (h.boat t hh).1.wet.ne_empty (h.ice t ht).1.dry
lemma Haven.pieces (h:Haven P T i b): ((↑(i∪b)):Set (Finset I)).PairwiseDisjoint id:=by
   intro s hs t ht hD; apply disjoint_left.mpr; intro x hx hy
   rcases P.root x with hq|⟨v,hv⟩
   · obtain ⟨p,hp⟩:= P.needs x hq
     have hi : p∈gem P s:=mem_biUnion.mpr ⟨x,hx,hp⟩; have hj : p∈gem P t:= mem_biUnion.mpr ⟨x,hy,hp⟩
     have hh {u:Finset I} (hu:p∈gem P u)(hv:u∈i∪b):u∈b:=(mem_union.mp hv).resolve_left (fun H'=> Nonempty.ne_empty ⟨p,hu⟩ (h.ice u H').1.dry)
     exact disjoint_left.mp (h.spatial (hh hi hs) (hh hj ht) hD) ((owns P _) hi) ((owns P _) hj)
   exact disjoint_left.mp (h.apart hs ht hD) (mem_biUnion.mpr ⟨x,hx,hv⟩) (mem_biUnion.mpr ⟨x,hy,hv⟩)
lemma Haven.compact (h:Haven P T i b) (hp:∀ x∈bulk i b, P.pole x∩T=P.flag x) : Basic P T (bulk i b):=by
   refine ⟨Woven.union (fun s hs=>(h.ice s hs).1) (fun s hs=>(h.boat s hs).1) h.apart h.spatial,?_,hp⟩
   have ht:i.biUnion (gem P)=∅:=by apply eq_empty_iff_forall_notMem.mpr; intro x hx; obtain ⟨s,hs,H⟩:=mem_biUnion.mp hx; exact Nonempty.ne_empty ⟨_,H⟩ (h.ice s hs).1.dry
   unfold gem bulk; rw[Finset.biUnion_biUnion,Finset.union_biUnion]; change i.biUnion (gem P) ∪ b.biUnion (gem P)= T; rw [ht, Finset.empty_union,h.flags]
private lemma part_in (S:I→Support n) (r:Finset I) (s:Finset (Finset I))(hr:r∈Parts S (s.biUnion id)): r⊆s.biUnion id:= (lives _ _ hr).1
lemma bulk_id : bulk (flot P T q) (base P T q)=q:=by
    unfold base bulk; rw[union_biUnion,reconstruct,← union_biUnion,show flot P T q∪hang P T q=cohorts P q from union_sdiff_of_subset (filter_subset ..), Ac.reconstruct]
set_option maxHeartbeats 400000 in
lemma Basic.splits (H:Basic P T q) : Haven P T (flot P T q) (base P T q):= by
    let w:=flot P T q; let o:=hang P T q; let r:=o.biUnion id; let b:= base P T q
    have ho : o⊆cohorts P q:=sdiff_subset ..
    have hx : cohorts P r=o:= Ac.separates _ _ (fun j hj=> (Ac.lives _ _ (ho hj)).2) ((Ac.separate _ _).subset (coe_subset.mpr ho))
    have he : r⊆q:=by intro i hi; obtain ⟨t,ht,hm⟩:= mem_biUnion.mp hi; exact (lives _ _ (ho ht)).1 hm
    have hm : Woven P r:=by
       have hQ s (hs:s∈r) (t)(ht:t∈q) v (hb:v∈P.cast s)(hc:v∈P.cast t): t∈r:= by
          obtain ⟨i,hi,hp⟩:=mem_biUnion.mp hs
          refine mem_biUnion.mpr ⟨_,hi,?_⟩; rw[← contains (sector P) (ho hi) s hp]; exact (bright _ _ _).2 ⟨ht,.single ⟨(lives _ _ (ho hi)).1 hp,ht,P.seat v,mem_image_of_mem _ hb, mem_image_of_mem _ hc⟩⟩
       refine ⟨fun v hv=> ?_,fun v hv=> ?_, H.formed.pole.subset (coe_subset.mpr he)⟩
       · obtain ⟨t,ht,Hv⟩:= mem_biUnion.mp hv; obtain ⟨i,⟨hi,hu,hx⟩,h'⟩:= H.formed.actor v (mem_biUnion.mpr ⟨t,he ht,Hv⟩); exact ⟨i,⟨hQ t ht i hi v Hv hu,hu,hx⟩,fun i h=> h' i ⟨he h.1,h.2⟩⟩
       obtain ⟨t,ht,Hv⟩:= mem_biUnion.mp hv; obtain ⟨i,hi,hu,hx⟩:=H.formed.host v (mem_biUnion.mpr ⟨t,he ht,Hv⟩); exact ⟨i,hQ _ ht _ hi v Hv hu,hu,hx⟩
    have hG (s)(hs:s∈w): Ice P s∧Disjoint (hill P s) T:= by
       obtain ⟨ht,h'⟩ := mem_filter.mp hs; have hH := lives (sector P) q ht
       have hI:Woven P s:=H.formed.parts le_rfl ht
       refine ⟨⟨hI,hH.2,eq_empty_iff_forall_notMem.mpr ?_⟩,h'⟩; intro i hx; exact disjoint_left.mp h' ((owns _ s) hx) (by obtain ⟨a,ha,hx⟩:=mem_biUnion.mp hx; rw [← H.location a (hH.1 ha)] at hx; exact (mem_inter.mp hx).2)
    have hZ : b.biUnion (gem P)=T:=by
       have h1 :gem P q=w.biUnion (gem P) ∪ b.biUnion (gem P):=by calc
          _ = gem P (bulk w b):= congr_arg (gem P) bulk_id.symm
          _ = _:=by unfold bulk gem;rw[biUnion_biUnion,union_biUnion];rfl
       rw [← H.complete,h1,show w.biUnion (gem P)=∅ from eq_empty_iff_forall_notMem.mpr (fun i hi=> by obtain ⟨s,hs,hQ⟩:=mem_biUnion.mp hi; exact Nonempty.ne_empty ⟨i,hQ⟩ (hG s hs).1.dry),empty_union]
    have hb : (b:Set _).PairwiseDisjoint (hill P):= Ac.separate P.foot _
    refine ⟨hG,fun s hs=> ?_,fun x hx' y hy hxy=> ?_,hb,hZ⟩
    · have hS:= Ac.lives P.foot _ hs; have hp:= hm.parts (S:=P.foot) (fare P) hs
      have hγ : hill P s∩T=gem P s:=by
         apply Finset.Subset.antisymm
         · intro x hx; obtain ⟨hs',h⟩:= mem_inter.mp hx; rw[← hZ] at h; obtain ⟨t,ht,hm⟩:= mem_biUnion.mp h; obtain rfl:t=s:= of_not_not fun hh=> disjoint_left.mp (hb ht hs hh) ((owns _ _) hm) hs'; exact hm
         intro x hx; refine mem_inter.mpr ⟨(owns _ _) hx,?_⟩; rw[← hZ]; exact mem_biUnion.mpr ⟨s,hs,hx⟩
      have ht(i)(hi:i∈cohorts P s): ¬ Disjoint (hill P i) T:=by
          have hp:i∈cohorts P r:= group_pull s r hs i hi; rw [hx] at hp; change i∈ hang P T q at hp; obtain ⟨hm,hu⟩:=mem_sdiff.mp hp; exact fun h'=>hu (mem_filter.mpr ⟨hm,h'⟩)
      refine ⟨⟨hp,hS.2,?_⟩, ht,hγ⟩
      obtain ⟨i,hi⟩:= hS.2.1; let y:= Ac.burst (sector P) s i; have hy:y∈cohorts P s:=mem_image_of_mem _ hi
      obtain ⟨x,h₀,h'⟩:= not_disjoint_iff.mp (ht _ hy)
      refine ⟨x,hγ ▸ mem_inter.mpr ⟨?_,h'⟩⟩; obtain ⟨k,hk,hu⟩:= mem_biUnion.mp h₀; exact mem_biUnion.mpr ⟨k,(Ac.lives _ _ hy).1 hk,hu⟩
    have hD(x)(hx:x∈w)(y)(hy:y∈w)(H:x≠y): Disjoint (crew P x) (crew P y):=by
       let A:=sector P; have hp:= Ac.separate A q (mem_filter.mp hx).1 (mem_filter.mp hy).1 H; refine disjoint_left.mpr fun k hk hm=> disjoint_left.mp hp (show P.seat k ∈ x.biUnion A from ?_) ?_
       · unfold A; rw[net]; exact mem_image_of_mem _ hk
       change P.seat k∈y.biUnion (sector P); rw [net]; exact mem_image_of_mem _ hm
    have hT(x)(h:x∈w)(y)(hy:y∈b): Disjoint (crew P x) (crew P y):= by
       refine disjoint_left.mpr fun v hx hv=> ?_
       obtain ⟨i,hi,hi'⟩:= mem_biUnion.mp hx; obtain ⟨u,hu,hk⟩:= mem_biUnion.mp hv; obtain ⟨z,hz,hϕ⟩:= mem_biUnion.mp ((lives _ _ hy).1 hu)
       have hq:= (mem_filter.mp h).1; have H':x≠ z:= fun H=> (mem_sdiff.mp hz).2 (H ▸ h); apply disjoint_left.mp (Ac.separate (sector P) q hq (ho hz) H')
       · exact mem_biUnion.mpr ⟨i,hi,mem_image_of_mem _ hi'⟩
       exact mem_biUnion.mpr ⟨u,hϕ,mem_image_of_mem _ hk⟩
    exact (mem_union.mp hx').elim (fun h=> (mem_union.mp hy).elim (fun hp=>hD x h y hp hxy) (fun hp=>hT x h y hp)) (fun h=>(mem_union.mp hy).elim (fun hp=>(hT _ hp x h).symm) (fun hp=>tank_coh _ h hp hxy))
end YM.Trace.Cask
