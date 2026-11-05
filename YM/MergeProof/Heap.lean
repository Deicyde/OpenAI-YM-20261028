import YM.MergeProof.Buys
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge   Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories
variable [Fintype ι](q:ι→Hat B R)
local notation "u"=> legs q
set_option quotPrecheck false
abbrev hatKey (q:ι→Hat B R)(p:ι):= WKey (q p)
abbrev hatMode (q:ι→Hat B R)(p:ι):= (q p).s
-- singletons included but subsequently drop to retain literal Leaf.
def atKey (k:Wing): Finset ι:= Finset.univ.filter fun i=> WKey (q i)=k
def harvestKind (k:Wing)(p:Finset ι):Prop:= p.Nonempty ∧ p⊆ atKey q k ∧ Fits (hatMode q) p
abbrev Hay (k:Wing):= {p:Finset ι// harvestKind q k p}
omit [Fintype ι] in
lemma hats_ne (p:Finset ι) (ht:p.Nonempty) (he:Fits (hatMode q) p): (unionTag (hatMode q) p he).val.Nonempty:=by obtain ⟨i,hi⟩:=ht; exact (q i).shiny.mono (subset_biUnion_of_mem _ hi)
private lemma home (k:Wing)(p:Hay q k)(i:ι)(hi:i∈p.val): hatKey q i=k:=(mem_filter.mp (p.property.2.1 hi)).2

def rise (k:Wing)(p:Hay q k): Hat B R where
   M := { turn:= k
          ingredient:=fun U=>∏ i∈p.val,(q i).M.ingredient U
          weight:=∏ i∈p.val,(q i).M.weight
          borel:= Finset.measurable_fun_prod _ fun i _=> (q i).M.borel
          glows:=fun g U => prod_congr rfl fun i hi=> (q i).M.glows g U
          scopedR:= fun U V hx ht=> prod_congr rfl fun i hi=> (q i).M.scopedR U V ((show (q i).M.turn=k from home q k p i hi).symm ▸ hx) ((show (q i).M.turn=k from home q k p i hi).symm ▸ ht)
          earn:= fun U=> by rw [norm_prod]; exact prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(q i).M.earn _)
          blank:= by obtain ⟨i,hi⟩:=p.property.1; exact (home q k p i hi) ▸ (show _ from (q i).M.blank)
          grant:=fun U hu=>by obtain ⟨i,hi⟩:=p.property.1; exact (home q k p i hi) ▸ (show _ from (q i).M.grant U (fun h=> hu (prod_eq_zero hi h))) }
   s:= unionTag (hatMode q) p.val p.property.2.2
   charge:= ∏ i∈p.val,(q i).charge
   shiny := hats_ne q p.val p.property.1 p.property.2.2

lemma tolls (k:Wing)(p:Hay q k)(w : V→ℝ) : fare (rise q k p) w=∏ i∈p.val, fare (q i) w:=by
   unfold fare sumFee; change ((Poly.toll w (unionTag (hatMode q) p.val p.property.2.2))*‖∏ i∈p.val,(q i).charge‖)* _= _
   rw [toll_union,norm_prod,prod_mul_distrib,prod_mul_distrib];rfl
lemma flaunt (k:Wing)(p:Hay q k)(U : Config G f): amount (rise q k p) U = ∏ i∈p.val, amount (q i) U:=by
   rw [varnish]; let t:= p.val;simp_rw [varnish];
   rw [tagged_prod (hatMode q) p.val p.property.2.2]; unfold rise; dsimp only; rw [Complex.ofReal_prod,prod_mul_distrib]
-- carriers bound
lemma fills (k:Wing)(p:Hay q k)(o:V→Site f)(h:∀ i,(q i).s.val.image o ⊆ (q i).M.crest): (rise q k p).s.val.image o ⊆ (rise q k p).M.crest:=by
   intro j hj; obtain ⟨x,hx,ht⟩:=mem_image.mp hj; obtain ⟨i,hi,hI⟩:= mem_biUnion.mp hx; have hQ:= h i (show j∈_ from mem_image.mpr ⟨x,hI,ht⟩); change j∈ (hatKey q i).support R at hQ; rw [home q k p i hi] at hQ; exact hQ
lemma large (k:Wing)(p:Hay q k)(h:2 ≤ p.val.card): 2≤(rise q k p).s.val.card:= by
   obtain ⟨x,hx,y,hy,hn⟩:= Finset.one_lt_card.mp (show 1 < _ from h); obtain ⟨i,hi⟩:= (q x).shiny; obtain ⟨j,hj⟩ := (q y).shiny
   refine Finset.one_lt_card.mpr ⟨i,mem_biUnion.mpr ⟨x,hx,hi⟩,j,mem_biUnion.mpr ⟨y,hy,hj⟩,fun he=> Finset.disjoint_left.mp (p.property.2.2.1 hx hy hn) hi ?_⟩; subst i; exact hj
-- Tops: leaf + composites of true log
abbrev Rock (k:Wing):= {p:Hay q k//2 ≤ p.val.card}
abbrev Mound := ι ⊕ (Σ j:logDeck q, Rock q (.logKey j.val))
def heap : Mound q→ Hat B R:= Sum.elim q (fun i=> rise q (.logKey i.1.val) i.2.val)
lemma logs_kept : logDeck (heap q)= logDeck q:=by
   ext i; rw [cams,cams]; constructor
   · rintro ⟨b,hb⟩; cases b with
     | inl j=> exact ⟨j,hb⟩
     | inr j=> have hx : j.fst.val=i:= Wing.logKey.inj (show Wing.logKey _= .logKey _ from hb); exact hx ▸ (cams q _).1 j.fst.property
   rintro ⟨j,h⟩; exact ⟨.inl j,h⟩
lemma gases (k:ℕ)(U:Config G f): rush (heap q) (.gasKey k) U=rush q (.gasKey k) U:=by
   unfold rush; change (∑ i:Mound q,_)=_; unfold Mound; rw [Fintype.sum_sum_type,sum_eq_zero (s:=univ) (f:=fun i:Σ j:logDeck q, Rock q (.logKey j.val)=> if WKey (heap q (.inr i))= .gasKey k then _ else _) ?_,add_zero]; rfl
   exact fun i _=> if_neg (show ¬ Wing.logKey i.1.val=Wing.gasKey k by intro h; cases h)
end YM.MergeProof.Menu
