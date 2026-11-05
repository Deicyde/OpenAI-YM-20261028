import YM.TraceExtension.Shepherd.Naval
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side} (R:Rep G n)
local notation "W!"=> R.path
local notation "b!"=> R.p.threshold
local notation "M!"=> R.p.B
local notation "d!"=> R.p.supportExponent
local notation "Y!"=>Config G n
variable (x:V→Site n) (d:V→Step)(ν:G.El→ G.El)(o:V↪Site n) (P:V→ Support n)(J:V→ Config G n→ G.El →ℂ)
    {σ A v δ u:ℝ}(h:R.Lawful σ A v δ u)(H:Geo.Width R.p R.clip σ)(hv:WilsonStartup.Decent R.clip R.p)(he:4 ≤ R.p.supportExponent) (m:ℕ) {D:ℝ} (w:∀ i, ProofC R (x i) (J i) ν (P i) D)
abbrev docks (i:V):= EBook R (x i) m
def bluff (i:V):= P i∪(univ: Finset (docks R x m i)).biUnion Subtype.val
structure Palace (D:ℝ) : Prop where
   uses i : ProofC R (x i) (J i) ν (P i) D
   invest k j : ν (k*j)=k*ν j*k⁻¹
   phase : Measurable ν
   terse i : x i∈ P i
   seats i : o i∈P i
   inject : Injective (settles x d)
   festival : (Set.univ:Set V).PairwiseDisjoint (fun i=> inspected (bluff R x P m i))
local notation "φ"=>longC x d ν
variable {x d ν o P J} (HX : Palace R x d ν o P J m D)
include HX
lemma wall {i j:V}(he:i≠j): x j ∉ inspected (bluff R x P m i):=fun ht=> Finset.disjoint_left.mp (HX.festival (Set.mem_univ i) (Set.mem_univ j) he) ht (show x j ∈ inspected (bluff R x P m j) from Finset.mem_union_left _ (mem_union_left _ (HX.terse j)))
lemma ornate (S:Finset V)(v':Rain V G)(U:Config G n)(hg:∀ i∈S, spur (x i) (d i) (J i) ν U (v' i)≠0): flags b! (φ S v' U) = flags b! U:=by
   induction S using Finset.induction with
   | empty=> rw[singZ x d ν v' U HX.inject]
   | insert i s hi IH=>
        have hy:= IH fun i hi=> hg i (mem_insert_of_mem hi); have hp:spur (x i) (d i) (J i) ν (φ s v' U) (v' i)= spur (x i) (d i) (J i) ν U (v' i):= Eq.symm (siteP R _ _ _ _ (HX.uses i) _ _ _ (offZ x d ν s v' U HX.inject _ (fun j hj h'=> wall R _ HX (Ne.symm (ne_of_mem_of_not_mem hj hi)) (mem_union_left _ (mem_union_left _ h')))))
        rw [budge x d ν s v' U HX.inject i hi,← hy]; let f:= HX.uses i; exact (smallC _ _ _ R D (f.price (v' i)) f.less (φ s v' U) (f.charm _ _ (show spur _ _ _ _ _ _ ≠0 from hp.symm ▸ hg i (mem_insert_self ..)))).1.symm
omit HX
variable (hx:∀ i:V,x i∈P i) (ht:∀ i:V,o i∈P i)
abbrev Yarns (x:V→Site n)(m:ℕ):= Σ v:V,Finset (docks R x m v)
def hull : TourC R V (SheetL R m) (Yarns R x m) where
 seat:=o
 tie:=x
 cap:=P
 anchor:= ht
 centre:= hx
 trek:=longC x d ν
 guardP i U j:= spur (x i) (d i) (J i) ν U j≠0
 adjust z:=z ∘ x
 path:=Subtype.val
 long i:=stockC R i.val
 short:=field R m
 marks:=J
 high i:= rink R (x i) (d i) m (J i) ν
 fee i U v:= aura R (x i) (d i) m ν U (v i)
 who:= Sigma.fst
 paint i:= braid R (x i.1) (d i.1) m (J i.1) ν i.2
 size i:= widthP R (x i.1) m i.2 (P i.1)
 lease i:= mem_union_left _ (ht i.1)
include HX h hv he H
lemma extraCred (i:V): Envelope (uncurry (rink R (x i) (d i) m (J i) ν)) ∧ (∀ j:G.El, LocalOn (inspected (bluff R x P m i)) (fun U=> rink R (x i) (d i) m (J i) ν U j)):=by
   let s:=x i; let f:=d i; let J':=J i; have Hx:ProofC R s J' ν (P i) D:= HX.uses i
   let z:= rink R (x i) f m J' ν
   have hp:uncurry z=fun g:Config G n × G.El=> ∑ p,braid R s f m J' ν p g.1 g.2:=funext fun v=> (fills R s f h hv m _ ν Hx _ _).symm
   constructor
   · change Envelope (uncurry z); rw [hp]; exact envUsum univ (fun p=>uncurry (braid R s f m J' ν p)) (fun p _=> works R s f h H hv he m J' ν Hx p|>.1)
   intro j
   refine UsesFinal.allReads b! _ _ (fun U V hu he'=>?_); change rink R s f m J' ν U j = rink R s f m J' ν V j; rw [fills R s f h hv m J' ν Hx U j|>.symm,fills R s f h hv m J' ν Hx V j|>.symm]; refine sum_congr rfl fun p hp=> ?_
   have hh:= (works R s f h H hv he m J' ν Hx p).2.2 j; refine Work.H03.reads_larger ?_ hh _ _ hu he'
   refine union_subset Finset.subset_union_left ?_
   intro k hk; obtain ⟨a,ha,H⟩:=mem_biUnion.mp hk; exact mem_union_right _ (mem_biUnion.mpr ⟨a,mem_univ _,H⟩)
local notation "C!"=> hull R m HX.terse HX.seats (d:=d) (ν:=ν) (J:=J)
lemma visa (S:Finset V)(U:Config G n)(v:Rain V G)(hx:gazeA C! U v S): field R m (φ S v U)=field R m U+∑ i∈S,aura R (x i) (d i) m ν U (v i):=by
    induction S using Finset.induction with
    | empty => rw [singZ x d ν v U HX.inject]; simp
    | insert i s hi IH=>
       have hδ:= IH fun j hj=> hx j (mem_insert_of_mem hj)
       let Z:=φ s v U; let U':= stunt (x i) (d i) ν U (v i); let V':=φ (insert i s) v U; have hvq: flags b! V'=flags b! U:= ornate R m HX _ _ _ hx
       have HZ: flags b! Z=flags b! U:= ornate R m HX _ _ _ (fun j hj=>hx j (mem_insert_of_mem hj))
       have hx': flags b! U'=flags b! U:= actsD R _ (d i) h H hv he _ _ (HX.uses i) U _ (hx i (mem_insert_self ..))|>.1
       have ht:V'=stunt (x i) (d i) ν Z (v i):= budge x d ν s v U HX.inject i hi
       have hG(k:{p:Support n//coverNumber R.p.B p ≤  m}): stockC R k.val V'-stockC R k.val Z=stockC R k.val U'-stockC R k.val U:=by
          have he:= (stock_pay R h k.val hv).2.2
          by_cases hp: x i∈k.val; swap
          · skip
            have h1:= he U U' (modify_off _ _ (ν (v i)) _ _ hp) (congr_arg _ hx'.symm); have h2: stockC R k.val Z=stockC R k.val V':=he _ _ (ht.symm ▸ modify_off _ _ _ _ Z hp) (by rw [HZ,hvq]); rw [h2,h1,sub_self,sub_self]
          have hh: k.val⊆bluff R x P m i:= fun p hx=> Finset.mem_union_right _ (mem_biUnion.mpr ⟨⟨_,hp,k.property⟩,Finset.mem_univ _,hx⟩)
          have hU : Agrees k.val U Z:= offZ x d ν s v U HX.inject _ (fun j hj h'=> wall R _ HX (Ne.symm (ne_of_mem_of_not_mem hj hi)) (mem_union_left _ (hh h')))
          rw [he U Z hU (congr_arg _ HZ.symm), he U' V' (ht.symm ▸ modify_local _ _ _ _ hU) (by rw[hx',hvq])]
       have hp : field R m V'-field R m Z= aura R (x i) (d i) m ν U (v i):=by unfold aura field; rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub, ←sum_sub_distrib,←sum_sub_distrib]; exact sum_congr rfl (fun k _=> hG k)
       rw[Finset.sum_insert hi]; unfold Z V' at hp; rw[hδ] at hp; linarith only[hp]
lemma polo : AirC C! :=by
   refine ⟨fun i=>?_ ,fun i v U V hu he=>?_,fun i U v p=> ?_,fun S=> whirlM x d ν S HX.inject HX.phase,fun S v=> whirlK x d ν S v HX.inject, fun p U=> singZ x d ν p U HX.inject,fun S p U g=> whirlG x d ν S p U HX.inject g HX.invest,fun S U p h=> ornate R m HX S p U h, fun S p v h=>funext fun U=>readsZ x d ν S p U HX.inject v h, fun S p D U=>village x d ν S p U HX.inject D _ Finset.inter_subset_left (fun j h hx=>mem_inter.mpr ⟨h,mem_filter.mpr ⟨mem_univ j,hx⟩⟩),fun S p P U V h=> notes x d ν S p U HX.inject _ V h, fun i=> (stock_pay R h i.val hv).2.2,fun i=>floated R h H hv he i.val,fun i=> (stock_pay R h i.val hv).2.1,crewField R h H m,fun i=> (HX.uses i).env,fun i=>(extraCred R h H hv he m HX i).1,fun i=> ((works R _ _ h H hv he m _ _ (HX.uses i.1) i.2)).1,fun g U i=>(works R _ _ h H hv he m _ _ (HX.uses i.1) i.2).2.1 U g,fun i v=>(works R _ _ h H hv he m _ _ (HX.uses i.1) i.2).2.2 v,fun S p U i H=>?_,fun S p U i hi=> ?_,fun S U p hx=> visa R h H hv he m HX _ _ _ (fun k _=>hx k (mem_univ k)),fun i U p hv=>?_ ,fun i U p=>?_⟩
   · have hp: MeasurableSet {x:Y!×G.El| spur _ (d i) (J i) ν x.1 x.2=0}:= (ruleP R _ (d i) _ _ (HX.uses i)).meas measurableSet_eq; exact hp.compl
   · exact propext ( show ¬ spur _ (d i) (J i) ν U v=0 ↔ ¬ spur (x i) (d i) (J i) ν V v=0 from by rw[show spur (x i) (d i) (J i) ν U v=spur (x i) (d i) (J i) ν V v from siteP R _ _ _ _ (HX.uses i) _ _ _ hu])
   · change (spur (x v) (d v) (J v) ν (Lattice.gauge i U) (i (x v)*p) ≠ 0) ↔ spur _ (d v) _ _ U p ≠0; rw [diary R _ (d v) _ _ (HX.uses v)]
   · let Z:=φ (S.erase i) p U; have hu:Agrees (P i) U Z:= offZ x d ν _ _ _ HX.inject _ fun j hj hp=>wall R m HX (Ne.symm (mem_erase.mp hj).1) (mem_union_left _ (mem_union_left _ hp))
     have ht:φ S p U= stunt (x i) (d i) ν Z (p i):= by conv_lhs=>rw [← insert_erase H]; exact budge _ _ _ _ _ _ HX.inject _ (notMem_erase _ _)
     change rink R (x i) (d i) _ _ ν U _ = _
     unfold rink spur; change J i _ _*_=J i (φ S p U) _*_; rw [ht]; exact congr_arg₂ (·*·) ((HX.uses i).eye (p i) (stunt (x i) (d i) ν U (p i)) _ (modify_local _ _ _ _ hu)) rfl
   · exact Eq.symm ((extraCred R h H hv he m HX i).2 (p i) _ _ (offZ x d ν S p U HX.inject _ (fun j hj=> wall R m HX ((ne_of_mem_of_not_mem hj hi).symm))))
   · change _ * _≠0 at hv; exact left_ne_zero_of_mul hv
   let K:={j:Yarns R x m // j.1=i}; let f(a: Finset (docks R x m i)): K:=⟨⟨i,a⟩,rfl⟩
   have hp : Bijective f:=by
      refine ⟨fun a b ht=>?_, ?_⟩
      · have H:HEq a b:=(Sigma.mk.inj (show (f a).val = (f b).val from congr_arg Subtype.val ht)).2; exact eq_of_heq H
      rintro ⟨⟨v,q⟩,hv⟩; change v=i at hv; subst i; exact ⟨q,rfl⟩
   let e:= Equiv.ofBijective f hp; unfold cram; rw [tsum_fintype]; exact ((fills R _ _ h hv m _ _ (HX.uses i) U _).symm.trans (Fintype.sum_equiv e _ _ (fun i=>rfl)))
end YM.Trace.Shepherd
