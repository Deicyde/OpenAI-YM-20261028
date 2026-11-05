import YM.TraceExtension.Wicket.Taste
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{R:Rep G n}{o:Edge (Site n)}{U:Config G n}
abbrev Vest (n:Side):=Finset (Badge n)
def stageZ (R:Rep G n)(n':ℕ)(H:Vest n): Vest n := H.filter fun i=> coverNumber R.p.B (boothC R i) ≤ n'
def cabinet (R:Rep G n)(m:ℕ)(H:Vest n)(U:Config G n):= R.v*Fintype.card (Site n)+∑ i∈stageZ R m H,pieceC R i U
def zestY(R:Rep G n)(I:Vest n)(o:Edge (Site n)):= I.filter (fun i=> o.1∈boothC R i)
def flavor(R:Rep G n)(I:Vest n)(r:ℕ)(o:Edge (Site n)):= (zestY R I o).filter (fun i=>i.elim (fun i=>r< mote R i.2) (fun _=>True))
lemma flair (R:Rep G n)(I:Vest n)(m l:ℕ)(o:Edge (Site n)): Below R o l m (flavor R (stageZ R m I) l o):=by
    intro i hi; obtain ⟨H,he⟩:=mem_filter.mp hi; obtain ⟨hh,hx⟩:= mem_filter.mp H; exact ⟨hx,(mem_filter.mp hh).2,he⟩
lemma healthyLift (B:ℝ)(X:Support n)(U:Config G n){P:Support n}{A:ℝ}(hh:X⊆P)(ha:A ≤ B)(h:Healthy A P U) : Healthy B X U := by
   refine Disjoint.mono_right ?_ (Disjoint.mono_left hh h); intro i hi; obtain ⟨x,hx,hv⟩:= (flags_spec ..).mp hi; exact (flags_spec ..).mpr ⟨_,hx,ha.trans_lt hv⟩
lemma echo_feat (R:Rep G n)(m r:ℕ)(o:Edge (Site n))(D:ℝ)(s:ℝ)(x:G.Color)(U:Config G n)(I:Vest n){σ A Λ δ w:ℝ}(hp:R.Lawful σ A Λ δ w) (ht: WilsonStartup.Decent R.clip R.p)(hv:64*D≤ R.p.threshold)(he:G.chord (G.lieExp (s • x))≤ D) (hq:ringsZ R o m r)(hX:o.1∈ tower r) (hV:Healthy (R.p.threshold/16) (tower r) U) :
    let V:=Tint o x s U; cabinet R m I V-cabinet R m I U=∑ i∈zestY R (stageZ R m I) o,zest R o s i U x:=by
   let t:=R.p.threshold; have h₀:= R.p.threshold_pos; have hQ:Healthy (t/8) {o.1} U:= healthyLift _ _ U (singleton_subset_iff.mpr hX) (by linarith only[h₀]) hV; let V:= Tint o x s U; have hh:flags R.p.threshold U=flags R.p.threshold V:= Tint.gate he hv hQ; let z:=stageZ R m I; let p(i):=pieceC R i V-pieceC R i U; have hy: (∑ i∈z,p i)=∑ i∈zestY R z o,p i:=by
      refine Eq.symm (sum_subset (filter_subset ..) fun i hi hk=> sub_eq_zero.mpr (Eq.symm ((bare_not R hp (q:=i) ht).2.2 U V ?_ (congr_arg _ hh)))); unfold V Tint; rw[seatB]; exact modify_off _ _ _ _ _ (fun h=> hk (mem_filter.mpr ⟨hi,h⟩))
   unfold cabinet; intro R'; rw[add_sub_add_left_eq_sub,← sum_sub_distrib,show (∑ i∈_, (pieceC R i R'-pieceC R i U))=_ from hy]; apply sum_congr rfl; intro i hi; obtain ⟨hp',hx⟩:=mem_filter.mp hi; have hp: Healthy t (boothC R i) U:=healthyLift t _ U (hq _ hx (mem_filter.mp hp'|>.2)) (by linarith only[h₀]) hV; have hz:Healthy t (boothC R i) V:= by unfold Healthy; rw[← hh]; exact hp
   cases i with
   | inl i=> change pieceC R _ V-pieceC R _ U= Shepherd.wake R i.2*(fer R i.1 i.2 U-fer R i.1 i.2 V); rw[ceast _ _ _ ht hz,ceast _ _ _ ht hp]; ring
   | inr j=> change -(masked _ _ _ _) - -(masked _ _ _ _)= dapple o.1 R.p U*(R.activities.E j U-R.activities.E j V); rw [warm (Disjoint.mono_left (singleton_subset_iff.mpr hX) hV),one_mul]; rw [masked_eq R.p.threshold (R.activities.reg j).support _ _ hz, masked_eq R.p.threshold (R.activities.reg j).support _ _ hp]; ring
variable {I:Type}
def spp (f:I↪ Barley): Seat n × I ↪ Badge n:= (Function.Embedding.prodMap (Function.Embedding.refl _) f).trans Function.Embedding.inl
lemma s_init (i:Seat n × I)(f:I↪Barley): spp f i=Sum.inl (i.1,f i.2):=rfl
def pelletF : GreenA ↪ Barley:=⟨legF,fun i j h=>by cases i<;>cases j<;> simpa only[legF, Sum.elim_inl, Sum.elim_inr,Function.comp_apply, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] using h ⟩
def spurL : ℕ ↪ Barley:=⟨loopF,Sum.inr_injective.comp Sum.inr_injective⟩
def lineE : ℕ ↪ Badge n:= Function.Embedding.inr
def shelves (n:Side) (A:Finset GreenA)(V L:Finset ℕ): Vest n:= ((univ ×ˢ A).map (spp pelletF)) ∪ ((univ ×ˢ V).map (spp spurL))∪L.map lineE
lemma tallShelves (n:Side)(X:Vest n):∀ᶠ A:Finset GreenA in atTop,∀ᶠ V:Finset ℕ in atTop,∀ᶠ L:Finset ℕ in atTop,X⊆ shelves n A V L:=by
    have ht(i:Badge n):∀ᶠ A:Finset GreenA in atTop,∀ᶠ V:Finset ℕ in atTop,∀ᶠ L:Finset ℕ in atTop,i∈shelves n A V L:=by
        have hp(j:Seat n × GreenA):∀ᶠ A:Finset GreenA in atTop,∀ᶠ V:Finset ℕ in atTop,∀ᶠ L:Finset ℕ in atTop,spp pelletF j ∈shelves n A V L:=by
            filter_upwards [eventually_ge_atTop ({j.2}:Finset GreenA)] with A hA; filter_upwards with V; filter_upwards with L; exact mem_union_left _ (mem_union_left _ (mem_map.mpr ⟨_,mem_product.mpr ⟨mem_univ _,hA (mem_singleton_self j.2)⟩,rfl⟩))
        rcases i with ⟨s,i|i|i⟩|i; exact hp (s,.inl i); exact hp (s,.inr i)
        · filter_upwards with A; filter_upwards [eventually_ge_atTop ({i}:Finset ℕ)] with V hV; filter_upwards with L; exact mem_union_left _ (mem_union_right _ (mem_map.mpr ⟨(s,i),mem_product.mpr ⟨mem_univ _,hV (mem_singleton_self _)⟩,rfl⟩))
        filter_upwards with A; filter_upwards with V; filter_upwards [eventually_ge_atTop ({i}:Finset ℕ)] with L hL; exact mem_union_right _ (mem_map.mpr ⟨_,hL (mem_singleton_self i),rfl⟩)
    have hx:= X.eventually_all.mpr (fun i _=> ht i); filter_upwards [hx] with A hA; filter_upwards [X.eventually_all.mpr hA] with V hV; filter_upwards [X.eventually_all.mpr hV] with L hL; exact fun i hi=> hL i hi
-- Core flocks restricted if x.1 impacted (may retain others non-intersecting in core S too).
def zoneZ (R:Rep G n)(b:I↪Barley)(O:Finset I)(o:Edge (Site n))(r:ℕ):Vest n:=(((univ ×ˢ (spikes R b O r))).filter fun i:Seat n × I=> o.1∈metal R b i).map (spp b)
lemma ferris (R:Rep G n)(b:I↪Barley)(O:Finset I)(o:Edge (Site n))(r:ℕ): ∀ i,i∈zoneZ R b O o r ↔ i∈(univ ×ˢ O).map (spp b) ∧ o.1∈boothC R i ∧ ¬i.elim (fun i=> r < mote R i.2) (fun _=>True):=by
     intro i; refine ⟨?_,?_⟩
     · intro h; obtain ⟨j,H,rfl⟩:= mem_map.mp h; obtain ⟨he,hr⟩:= mem_filter.mp H; obtain ⟨hv,hz⟩:=mem_product.mp he; obtain ⟨hz,hx⟩:=mem_filter.mp hz; exact ⟨mem_map.mpr ⟨j,mem_product.mpr ⟨hv,hz⟩,rfl⟩,hr,not_lt.mpr hx⟩
     rintro ⟨h,hj,hh⟩; obtain ⟨j,H,rfl⟩:=mem_map.mp h; exact mem_map.mpr ⟨j,mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨(mem_product.mp H).2,le_of_not_gt hh⟩⟩,hj⟩,rfl⟩
abbrev StemCut(R:Rep G n)(m r:ℕ):Prop:= R.p.B*100+r≤R.p.B*m
def ovZone(R:Rep G n)(J: Vest n)(m r:ℕ)(o:Edge (Site n)):= (zestY R (stageZ R m J) o).filter (fun i=>¬ i.elim (fun i=>r < mote R i.2) (fun _=>True))
lemma prank (R:Rep G n)(o:Edge (Site n))(m r:ℕ)(A:Finset GreenA)(V L: Finset ℕ)(hh:StemCut R m r): ovZone R (shelves n A V L) m r o= zoneZ R pelletF A o r ∪ zoneZ R spurL V o r:=by
    ext i; rw [mem_union,ferris,ferris]; let T:= zestY R (stageZ R m (shelves n A V L)) o; constructor
    · intro hx; obtain ⟨ht,hp⟩:= mem_filter.mp hx; obtain ⟨hm,he⟩:= mem_filter.mp ht; obtain ⟨hq,hv⟩:= mem_filter.mp hm; rcases mem_union.mp hq with hk|hk
      · exact (mem_union.mp hk).imp (fun h=>⟨h,he,hp⟩) (fun h=>⟨h,he,hp⟩)
      obtain ⟨j,hj,rfl⟩:=mem_map.mp hk; exact False.elim (hp (show True from trivial))
    intro he; obtain ⟨h,hv,hx⟩:= (or_and_right (a:=_) (b:=_) (c:=_)).mpr he
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_union_left _ (mem_union.mpr h),?_⟩,hv⟩,hx⟩
    rcases i with i|i; exact Nat.le_of_mul_le_mul_left ((post_geo R _ _).trans ((Nat.add_le_add_left (Nat.le_of_not_gt hx) _).trans hh)) R.p.B_pos; exact False.elim (hx (show True from trivial))
lemma disburse (R:Rep G n)(o:Edge (Site n))(r:ℕ)(A:Finset GreenA)(V:Finset ℕ): Disjoint (zoneZ R pelletF A o r) (zoneZ R spurL V o r):=by
    refine Finset.disjoint_left.mpr fun i hi hj=> ?_; obtain ⟨x,hx,rfl⟩:=mem_map.mp hi; obtain ⟨y,hy,hh⟩:=mem_map.mp hj; have he:loopF y.2=legF x.2:=congr_arg Prod.snd (Sum.inl_injective (α:=Seat n × Barley) (β:=ℕ) hh); unfold legF loopF at he; cases h:x.2 <;> simp_all
lemma obelisk (R:Rep G n)(o:Edge (Site n))(r:ℕ)(b:I↪Barley)(A:Finset I)(P:Support n)(hP:o.1∈ P)(s:ℝ)(U:Config G n)(v:G.Color)(c:ℝ)(hv:∀ i: I, Shepherd.wake R (b i)=c)(hp:2≤ R.p.B) :
    let F:= -c • prun R b P (spikes R b A r); ∑ i∈zoneZ R b A o r,zest R o s i U v= F (Tint o v s U)-F U:=by
    let V:= Tint o v s U; let W:= @univ (Seat n) _ ×ˢ spikes R b A r (n:=n); let Q:= W.filter (fun i:Seat n × I=> o.1∈metal R b i); let G':= flocks R b P (spikes R b A r); have hQ:Q⊆G':=by
        intro j hj; obtain ⟨hj,hx⟩:=mem_filter.mp hj; exact mem_filter.mpr ⟨hj,Finset.not_disjoint_iff.mpr ⟨_,hP,hx⟩⟩
    have hV(i:Seat n × I): zest R o s (spp b i) U v= -c*(seatP R b i V-seatP R b i U):=by change Shepherd.wake R (b i.2) *_=_; rw[hv]; change c*(seatP R b i U-seatP R b i V)=_;ring
    intro F; change ∑ i∈Q.map (spp b),_= _; rw [sum_map]
    simp_rw[hV]; rw [sum_subset hQ]; swap
    · intro i hi h; have hh:o.1 ∉ metal R b i:=fun hv=> h (mem_filter.mpr ⟨(mem_filter.mp hi).1,hv⟩); have ht: Agrees (metal R b i) U V:=by unfold V Tint; rw[seatB]; exact modify_off _ _ _ _ _ hh
      rw [show seatP R b i V=seatP R b i U from (ferLocal R _ _ hp U V ht).symm,sub_self,mul_zero]
    rw[← Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]; unfold F prun; simp only[Pi.smul_apply,Finset.sum_apply];rfl
lemma office (R:Rep G n)(o:Edge (Site n))(m r r':ℕ) (P:Support n)(hP:o.1∈ P)(A:Finset GreenA)(V L:Finset ℕ)(H:StemCut R m r)(K:ℝ) (s:ℝ)(x:G.Color)(U:Config G n){σ X Λ δ w:ℝ}(hp:R.Lawful σ X Λ δ w)(ht:WilsonStartup.Decent R.clip R.p)(hB:2≤ R.p.B)(hv:64*K ≤ R.p.threshold)(he:G.chord (G.lieExp (s • x))≤ K)(hq:ringsZ R o m r')(hX:o.1∈ tower r')(hV:Healthy (R.p.threshold/16) (tower r') U):
    let I:=shelves n A V L; let W:=cabinet R m I; let F:= -R.beta • prun R legF P (spikes R legF A r) - prun R loopF P (spikes R loopF V r); let Z:= flavor R (stageZ R m I) r o; let Y:=Tint o x s U
    W Y-W U= F Y-F U+∑ i∈Z,zest R o s i U x :=by
    intro I W F Z Y; let E:= zestY R (stageZ R m I) o; let D:=ovZone R I m r o; rw[show _-_= _ from echo_feat R m r' o K s x U I hp ht hv he hq hX hV]; rw[show ∑ i∈ E,zest R o s i U x=(∑ i∈ Z,zest R o s i U x)+ ∑ i∈ D,zest R o s i U x from (sum_filter_add_sum_filter_not E _ _).symm,show D=_ from prank R o m r A V L H,sum_union (disburse R o r A V),obelisk R o r pelletF A P hP s U x R.beta (fun i=> by cases i <;> rfl) hB,obelisk R o r spurL V P hP s U x 1 (fun _=> rfl) hB]; unfold F; simp only [neg_one_smul,Pi.sub_apply, Pi.neg_apply]; unfold pelletF spurL; dsimp; abel
end YM.Trace.Wicket
