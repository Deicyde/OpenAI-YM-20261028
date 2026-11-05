import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Vegetal
/-!
# Pointwise reconstruction at the literal flags before feeding the K word

`Plate` as before; correspondence on every ticket in every Forest
Streak of the lantern, though mutually coupled at the inspection regions.
Parts API; no spurious multiplicities of cores arising at output-σ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Vale
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pot Marker
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x W : ℝ} {A : Stores S} {v : Dyed G S} {P : Teller G}

lemma births (p : Pilot G S x) (M : Plate v x W) (u : Support f):
    let D (s:Finset (Rung S x)):= if (s:Set (Rung S x)).PairwiseDisjoint (fun i=> acre (rips i)) ∧ s.image rips=owners p.key x ∧ s.biUnion markT=u then ∏ i∈s,atomP W v M (.inl i) p else 0
    ∑ s : Finset (Rung S x),D s= if (owners p.key x).biUnion (fun i=> hoes v i p)=u then ∏ i∈owners p.key x,autumn v W M i p else 0:= by
  intro D; let Y:= owners p.key x; let g(i:Core S x):= planting i (hoes v i p) inter_subset_left; let Q:=Y.image g
  have hv: Injective g:=fun i j h=>congr_arg rips h
  have hA : Q.image rips=Y:= by change Finset.image _ (Y.image g)=_; rw [image_image]; change Y.image id=Y; exact image_id
  have ht : (Q:Set (Rung S x)).PairwiseDisjoint (fun i=>acre (rips i)):= by
    intro i hi j hj h; obtain ⟨i,h1,rfl⟩:=mem_image.mp hi; obtain ⟨j,h2,rfl⟩:=mem_image.mp hj
    exact (((owner_eq ..).1 rfl).1 h1 h2) (fun e=>h (congr_arg g e))
  have hQ : Q.biUnion markT=Y.biUnion (fun i=>hoes v i p):= by ext i; simp only [Q,Finset.mem_biUnion,exists_mem_image]; rfl
  rw [Finset.sum_eq_single Q]
  · unfold D; split_ifs with he h h
    · rw [prod_image hv.injOn]; exact Finset.prod_congr rfl fun i _=> (show (checkIn v (g i) p)*_= _ from by rw [show checkIn v (g i) p=1 from if_pos rfl,one_mul]; rfl)
    · exact False.elim (h (hQ.symm.trans he.2.2))
    · exact False.elim (he ⟨ht,hA,hQ.trans h⟩)
    rfl
  · intro b _ h; unfold D; split
    next hz=>
      by_contra he
      apply h
      have ht (i) (hi:i∈b): i=g (rips i):= by
        have hp : checkIn v i p≠0:= left_ne_zero_of_mul (prod_ne_zero_iff.mp he i hi)
        have he:markT i=hoes v (rips i) p:= Classical.not_not.mp fun he=>hp (if_neg he)
        exact Subtype.ext (Prod.ext rfl he)
      ext i; rw [mem_image]; constructor
      · intro hi; exact ⟨rips i,(show b.image rips=Y from hz.2.1) ▸ mem_image_of_mem rips hi,(ht i hi).symm⟩
      rintro ⟨j,hj,rfl⟩
      obtain ⟨k,hk,rfl⟩:=mem_image.mp (show j∈b.image rips from hz.2.1.symm ▸ hj); exact ht k hk ▸ hk
    rfl
  simp

variable (H : Draft v P x W) (M : Plate v x W) (O : Orchard S)
local notation "Amt"=>amount H M O

def vine (Q : Finset (Herbs S x)) (p : Pilot G S x) (m : Support f) :=
    enlist Amt Q ∧ cardGoal Amt Q=flags v.bp.threshold p.view ∧ p.key=stapled x (glow Amt Q) p.view ∧ Q.biUnion loves=m

def crop (A : Stores S) (k : Streak O) (V : Config G c) (y : RoomView A x k.wood G) (u : Support f) (s : Finset (Sprigs H M O)) :=
  let Q:=sprouting H M O
  if (s:Set (Sprigs H M O)).PairwiseDisjoint (fun i=>(Q i).zone) ∧ s.biUnion (fun i=> (Q i).up)=u ∧
             s.biUnion (fun i=> (Q i).down)=flags v.bp.threshold V ∧ A=stapled x (s.sup (fun i=> (Q i).data)) V then ∏ i∈s,(Q i).weight A k V y else 0

private lemma enumerate {ι a:Type} [Fintype ι] [Fintype a] (F : Finset ι→Finset a) (T : Finset ι → Prop) [DecidablePred T] (V : Finset a → Prop) [DecidablePred V] (G : Finset a → ℝ) (g : Finset ι→ℂ) (h : Set.InjOn F {s| T s}) (hp : ∀ s,V s→ ∃ t,T t∧ F t=s) (ht : ∀ s,g s= if T s∧ V (F s) then ↑(G (F s)) else 0) : (∑ s,g s)=↑(∑ s∈ univ.filter V,G s):= by
  -- explicit with same Decides
  simp_rw [ht,← sum_filter,Complex.ofReal_sum]
  refine sum_bij (fun i _=> F i) ?_ ?_ ?_ (fun _ _=> rfl)
  · intro i hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2.2⟩
  · exact fun _ hi _ hj hv=> h ((mem_filter.mp hi).2.1) ((mem_filter.mp hj).2.1) hv
  intro i hi; obtain ⟨s,hs,rfl⟩:=hp i ((mem_filter.mp hi).2); exact ⟨_,mem_filter.mpr ⟨mem_univ _,hs,(mem_filter.mp hi).2⟩,rfl⟩
lemma cropping (A : Stores S) (k : Streak O) (V : Config G c) (y : RoomView A x k.wood G) (u : Support f):
    let p:Pilot G S x :=⟨A,k.wood,k.tag,V,y⟩
    (∑ s,crop H M O A k V y u s) = (↑(∑ s∈ univ.filter (fun s=>vine H M O s p u), ∏ i∈s,atomP W v M i p):ℂ):= by
  intro p; let f s:=draw Amt s; let g s:= ∏ i∈s,atomP W v M i p; let E s:=vine H M O s p u
  let T (s : Finset (Sprigs H M O)):= (s:Set (Club Amt)).PairwiseDisjoint (zone Amt)
  have hz (s : Finset (Sprigs H M O)): crop H M O A k V y u s= if T s∧E (f s) then ↑(g (f s)) else 0:= by
    unfold crop; dsimp only
    have hu :(f s).biUnion loves=s.biUnion (fun t : Sprigs H M O=>t.val.biUnion loves):=by
      unfold f Display.draw; rw [biUnion_biUnion]
    have hf : glow Amt (f s)=s.sup (fun i=> (sprouting H M O i).data):=by unfold glow f Display.draw; rw [sup_biUnion]; rfl
    have he:cardGoal Amt (f s)=s.biUnion (fun i=> (sprouting H M O i).down):= drawn_marks ..
    split
    next h=>
      rw [if_pos (show T s ∧ _ from ⟨h.1, Display.drew _ _ h.1,he.trans h.2.2.1, hf.symm ▸ h.2.2.2,hu.trans h.2.1⟩)]
      let u':=Display.autonomy Amt (show T s from h.1)
      unfold g f draw; rw [prod_biUnion u']
      simp_rw [contracts,Complex.ofReal_prod]; rfl
    next h=> exact Eq.symm (if_neg (fun ⟨hT,hF⟩=> h ⟨hT,hu.symm.trans hF.2.2.2,he.symm.trans hF.2.1,hf ▸ hF.2.2.1⟩))
  exact enumerate f T E g (crop H M O A k V y u) (fun i hi j hj h=> by
    let Z:= (recovered Amt (show T i from hi)).symm.trans ((congr_arg (Ac.Parts (zones Amt)) h).trans (recovered Amt (show T j from hj)))
    exact @Finset.image_injective _ _ (fun i j : Finset (Herbs S x) =>  i.decidableEq j) _ Subtype.val_injective i j Z) (fun i h=> luminous Amt i h.1) hz


lemma backyard (p : Pilot G S x) (A : Finset (Core S x)) (h : A=owners p.key x) (hp : 1 ≤ radiusB x):
    (∏ i∈ A,autumn v W M i p)* (∑ s : Finset (Fleck S⊕Glade c), ∏ i∈s,atomP W v M (Sum.inr i) p) = Real.exp ((∑ i∈A,M.base i p)+∑ j,M.aux j p)*∏ i,v.ask W p i:= by
  subst A
  let A:= owners p.key x; let t (i:Fleck S⊕Glade c):=atomP W v M (Sum.inr i) p
  have hV : (∑ s : Finset (Fleck S⊕Glade c), ∏ i∈s,t i)= ∏ i,(t i+1):= Eq.symm (by simpa only [prod_const_one,mul_one] using! Fintype.prod_add t (fun _=>1))
  let Y:= A.biUnion mined; let F:=v.ask W p
  have ht : (∏ i∈Y,F i)*(∏ i:Fleck S,(v.sock W i p+1))=∏ i,F i:= by
    have he(i): v.sock W i p + 1 = if i ∈ Yᶜ then F i else 1:= by simp only [Y,A,deposits,mem_compl,mem_filter,mem_univ,true_and, not_not,Dyed.sock]; split_ifs; exact sub_add_cancel ..; rw [zero_add]
    simp_rw [he, ← Finset.prod_filter]; rw [show (univ.filter fun i => i∈Yᶜ)=Yᶜ by ext; simp]
    exact prod_mul_prod_compl ..
  have he : (∏ i,(atomP W v M (Sum.inr (.inr i)) p+1))= Real.exp (∑ i,M.aux i p):= by rw [Real.exp_sum]; exact Finset.prod_congr rfl fun i _=> sub_add_cancel ..
  change (∏ i∈A,_)*(∑ s:Finset (Fleck S⊕Glade c),∏ i∈s,t i)=_
  rw [hV,Fintype.prod_sum_type]; unfold t
  rw [he]; simp only [Real.exp_add,autumn,prod_mul_distrib]
  rw [← Real.exp_sum, ← Finset.prod_biUnion (disjoint_carts p.key x hp)]; change (_* (∏ i∈Y,F i))*((∏ i,_)*_)=_
  change (Real.exp (∑ i∈ A,_)* _)*((∏ i,(v.sock W i p+1))* _)= (Real.exp (∑ i∈A,_)*_)*∏ i,F i
  rw [← ht]; ring

lemma rect (hp : v.bp.threshold=temp x) (hw : 0<W) (ht : 0<fiery G x S.patch.L) (hV : fiery G x S.patch.L /2≤ v.source.p.threshold)
    (p : Pilot G S x) (u : Support f) (h : Matched p):
    (∑ s : Finset (Herbs S x),if vine H M O s p u then ∏ i∈s,atomP W v M i p else 0) = if flags v.source.p.threshold (v.top p)=u then Real.exp (v.spoolLift p)*∏ i,v.ask W p i else 0:=by
  let a:=owners p.key x
  let U:= a.biUnion fun i=> hoes v i p
  let t:= flags v.source.p.threshold (v.top p)
  let C (s):=vine H M O s p u
  let g (s:Finset (Fleck S⊕Glade c)):= ∏ i∈s,atomP W v M (Sum.inr i) p
  let e : Finset (Rung S x) × Finset (Fleck S⊕Glade c) ≃ Finset (Herbs S x):= Finset.sumEquiv.symm.toEquiv
  let D : ℝ := if U=u then ∏ i∈a,autumn v W M i p else 0
  have hv (r : Finset (Fleck S⊕Glade c)):
      (∑ s : Finset (Rung S x),if C (e (s,r)) then ∏ i∈e (s,r),atomP W v M i p else 0)=D*g r := by
    unfold D U; rw [← births p M]
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=>?_
    split
    next H' =>
      rw [if_pos ((membership H M O hp u p h i r).1 H')]; exact prod_disjSum ..
    next H'=> rw [if_neg (mt ((membership H M O hp u p h i r).2) H'), zero_mul]
  rw [← Equiv.sum_comp e (fun s=> if C s then _ else 0),Fintype.sum_prod_type,sum_comm]; simp_rw [hv, ← Finset.mul_sum]
  have hm : (∏ i∈a,autumn v W M i p)*(∑ i,g i)=_:= backyard M p a rfl (by have :=H.enrolled.produced.scale; omega)
  by_cases hA : v.Playing W p
  · have hz:U=t:=by
      refine Finset.Subset.antisymm ?_ ?_
      · intro i hi; obtain ⟨u,hu,hp⟩:= mem_biUnion.mp hi; exact (mem_inter.mp hp).2
      intro i hi; obtain ⟨u,hu,hp⟩:=mem_biUnion.mp (playsInto v W hw ht hV h hA hi); exact mem_biUnion.mpr ⟨u,hu,mem_inter.mpr ⟨hp,hi⟩⟩
    change D*(∑ i,g i)= if t=u then _ else _; unfold D; rw [hz]; split; next hv=> rw [M.pitch p h hA]; exact hm
    next h=> exact zero_mul _
  have hV: (∏ i,v.ask W p i)=0:= Classical.not_not.mp hA
  rw [hV,mul_zero,ite_self]; dsimp only [D]; split
  next => exact hm.trans (by rw [hV,mul_zero])
  exact zero_mul _

theorem land {a C η b : ℝ} (hp : v.bp.threshold=temp x) (hw : 0<W) (ht : 0<fiery G x S.patch.L) (hV : fiery G x S.patch.L /2≤ v.source.p.threshold) (he : Physical.Certified S v.things x a C η b) (hr : v.things.up=v.source.path) (hc : v.things.high=v.source.clip) (hJ : LocalRatio v.ratio) (hb : 0<v.source.beta) :
    let Q : Lantern G S:=⟨v.chi,v.arc,H.pos,H.radius,O⟩
    BodyGrant v.things v.source Q (v.chi.profiles G S x W hw ht) v.ratio v.bp.threshold (sprouting H M O) (fun V=> (↑(v.loading x V):ℂ)):= by
  intro Q V A hz k z u
  let p:Pilot G S x:= ⟨A,k.wood,k.tag,V,z⟩
  let F:= v.source; let β:=F.beta; let T:=v.things; let b':= v.top p; let L:= Q.park
  let I:=v.chi.profiles G S x W hw ht
  change (if flags _ _=u then spooled T Q v.ratio I β _ _ k V z else 0)=↑(v.loading x V)*∑ s,crop H M O A k V z u s
  rw [cropping]; -- y
  have he:= v.cardinal_spin H.enrolled.funded he hr hc hJ hb hp p hz
  have hm:v.freight p= _ := he.2
  have hy:= rect H M O hp hw ht hV p u hz
  -- spool algebra
  split
  next hw' =>
    rw [← sum_filter, if_pos (show flags _ b'=u from hw')] at hy
    rw [hy, ← Complex.ofReal_mul]
    let h0:= v.tapeAt p
    have hh : spooled T Q v.ratio I β (fun U=>(↑(Real.exp (F.exponent U)):ℂ)) A k V z=↑(v.freight p* ∏ i,v.ask W p i):= by
      rw [← v.pursues W p hz]; let a:= v.tapeAt p; let D:=reserve v.chi v.ratio v.arc a; let d:=doors v.chi v.arc a; let m:ℝ:=Fintype.card S.Choices
      let C:= fog A k.wood T x V k.tag; let u:=v.ratio.scale ^ Fintype.card (Active A x k.wood)*chartCost C (coupling β)
      let E:=Real.exp (Gaussian.force C z.2/2); let g:=Real.exp (F.exponent b'); let j:=I.bill A k.tag b' V; let i:=S.likelihood b' k.tag; let n:= S.noise β (S.prediction b' k.tag) V
      unfold spooled regularized attending Dyed.freight
      dsimp only [p,Q]; simp_rw [← Q_endpoint,← mean_endpoint]
      -- U and coordinates; use exact equality of tapes
      have hu : a=Next.SectorChange.tape (Local.portrait T A k.wood k.tag x V .endpoint v.chi v.arc z.1+coupling β • z.2):= by unfold a p Dyed.tapeAt displaced; simp only [mean_endpoint]; rfl
      have hp : k.wood.drape (returned A k.wood V z.1 (displaced (meanLog A k.wood T x V k.tag v.chi v.arc z.1) (coupling β) z.2))=b':= by rw [mean_endpoint]; rfl
      rw [hp]; change m • u • E • (D*d) • (j*i) • n • (↑g:ℂ)=↑(u*E*D*n*g*(j*m*i*d))
      simp only [Complex.real_smul,Complex.ofReal_mul]; ring
    rw [show spooled T Q v.ratio I β _ _ k V z= _ from hh,hm,mul_assoc]
  next hf => rw [← sum_filter, if_neg (show flags _ b'≠u from hf)] at hy; rw [hy, Complex.ofReal_zero,mul_zero]
end YM.PhysicalNext.InteractingRank.Pump.Vale
