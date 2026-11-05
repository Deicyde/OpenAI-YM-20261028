import YM.MergeProof.Dock
import YM.MergeProof.North.Gild
import YM.MergeProof.North.Shan

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}{A:Rep G c}
variable (v:V)(P:V→Motion)(E:V→Site f)(B:V→Equiv.Perm V)(π:∀ i,(R).activities.Moves (P i).1 (E i))
local notation "X"=> Aged V
def Horn (F:Support f→ Config G f→Poly (X))(K:Box f→ Config G f→ Poly (X)):Prop:= ∀ i,i≠v→ B i v=i∧ ∀ U,(∀ j,Harm v (B i) (P i) (F j (pull (P i).1 (E i) U)) (F (sky (P i) (E i) j) U))∧∀ j,Harm v (B i) (P i) (K j (pull (P i).1 (E i) U)) (K (puff (P i) (E i) j) U)
def Cohere (q:ι→Hat (X) R): Prop:=∀ i,i≠v→∃ b, Kin q v i (B i) (P i) (E i) (π i) b
variable {v P E B π}
lemma Cohere.sum (p:ι→Hat (X) R)(q:J→Hat (X) R)(h:Cohere v P E B π p)(hp:Cohere v P E B π q): Cohere v P E B π (Sum.elim p q):=by
    intro i hi; obtain ⟨a,ha⟩:=h i hi; obtain ⟨b,hb⟩:=hp i hi; refine ⟨Equiv.sumCongr a b,ha.here,fun j=>?_,fun j=>?_⟩
    · cases j; exact ha.cares _;exact hb.cares _
    cases j;exact ha.plot _;exact hb.plot _
lemma Cohere.cling [Fintype ι] (q:ι→ Hat X R)(h:Cohere v P E B π q): Cohere v P E B π (heap q):= fun i hi=> (h i hi).elim (fun _ h=> h.piled)
variable {F:Support f→ Config G f→Poly (Aged V)}{K:Box f→ Config G f→ Poly (Aged V)}{o:Name V→ Site f}{d t:ℝ}{w:Name V→ℝ}
lemma dryUp (h:Carton o F K R.p.threshold)(hT:Horn v P E B F K)(hF:Towed w id F R.p.B d t)(hK:Towed w Prod.fst K R.p.B d t)(hw:∀ i,0<w i)(hh:Arsenal R)(Pib:∀ i,(R).activities.Moves (P i).1 (E i))(hv:∀ u:V,u≠v→∀ i:Bool,w (u,i)=w (v,i)):
   ∃ (I:Type) (_:Fintype I) (q:I→Hat (X) R), Cohere v P E B Pib q ∧ (∀ i,2 ≤ (q i).s.val.card) ∧ Offer o q w R.p.B d (4*t) ∧ (∀ U,∑ i,odour (q i) U=∑ i,F i U) ∧ ∀ i U,∑ j,fragrance (q j) U i= K i U:=by
    let T:=fun (_:Support f)(a:Wing)=> ∃ i,a=.logKey i; let Z:=fun (i:Box f)(a:Wing)=>∃ j,a= .gasKey j ∧ barcode R.activities j=i
    have hx (i:Viv F) :∃ M:Bool→Hat X R,Baker F w T id i M:= by
        let j:= i.val.1; let U:= i.property.choose; have hz: F j U≠0:= fun hh=> i.property.choose_spec (hh ▸ rfl); let p:= i.val.2
        have h1: 2 ≤ p.val.card:= (h.exp j).2 U p i.property.choose_spec; have hq:j.Nonempty:= ((Finset.card_pos.mp (by omega : 0 < p.val.card)).image o).mono ((h.exp j).1.toBorne.place _ _ i.property.choose_spec)
        obtain ⟨a,hv,hr⟩:=hh.dry j hq; exact certifies hw T (fun i=>(h.exp i).1.toBorne) (fun i=>(h.exp i).2) hF i ⟨Wing.logKey a,hr,hv,⟨a,rfl⟩,fun x hp=> by change Healthy R.p.threshold _ x; rw [hv]; exact (h.exp _).1.permits x hp⟩
    have hs (i:Viv K):∃ M:Bool→Hat X R,Baker K w Z Prod.fst i M:=by
        let j:=i.val.1; have ht: K j i.property.choose ≠ 0:= by intro h; exact i.property.choose_spec (by rw [show K _ _= _ from h];rfl)
        obtain ⟨a,hv,hx⟩:= hh.wet j ((h.flag _).1.permits _ ht|>.2)
        exact certifies hw Z (fun i=>(h.flag i).1.toBorne) (fun i=>(h.flag i).2) hK i ⟨Wing.gasKey a,trivial,(Prod.mk.inj hv).1,⟨a,rfl,hv⟩,fun x hh=> hx x (((h.flag _).1.permits _ hh).1)⟩
    have he(u)(hu:u≠v):= (hT u hu).1
    obtain ⟨f0,hf,hB⟩:= joined (fun i=>sky (P i) (E i)) B P E T id Pib he (fun v hv i U=> (hT v hv).2 U|>.1 i) hv (fun i h _=>rfl) (fun i hi j p ⟨v,hv⟩=> by rw [hv]; exact ⟨_,rfl⟩) hx
    obtain ⟨g,hg,hy⟩:=joined (fun i=>puff (P i) (E i)) B P E Z Prod.fst Pib he (fun v hv i U=> (hT v hv).2 U|>.2 i) hv (fun i h _=>rfl) (fun i hi j p ⟨v,hv,hu⟩=> by rw [hv]; exact ⟨(Pib i).kp v,rfl, (location (P i) _ (Pib i) v).trans (congr_arg _ hu)⟩) hs
    obtain ⟨hF,hv⟩:= ranks hw T (fun i=>(h.exp i).1.toBorne) (fun i=>(h.exp i).2) hF f0 hf
    obtain ⟨hG,hW⟩:= ranks hw Z (fun i=>(h.flag i).1.toBorne) (fun i=>(h.flag i).2) hK g hg
    have ht U i: odour (f0 i) U=amount (f0 i) U ∧ ∀ j,fragrance (f0 i) U j=0 :=by
       obtain ⟨l,hl⟩:=show ∃ l,(f0 i).M.turn= .logKey l from ((hf i.1).head i.2).2.2
       unfold odour prose; rw [hl,varnish]; exact ⟨rfl,fun j=>by simp [fragrance,entry,hl]⟩
    have hr U (i:Viv K ×Bool): odour (g i) U=0∧∀ j,fragrance (g i) U j=if i.1.val.1=j then amount (g i) U else 0:=by
       obtain ⟨l,hl,hb⟩:=show ∃ l,(g i).M.turn= .gasKey l ∧ _ from ((hg i.1).head i.2).2.2
       constructor
       · simp [odour,prose,hl]
       intro j; unfold fragrance entry; rw [hl,varnish]; dsimp only; rw [hb]; split_ifs; rfl; simp
    refine ⟨_,inferInstance,Sum.elim f0 g,Cohere.sum f0 g hB hy,fun i=>?_,?_,fun U=>?_,fun i U=>?_⟩
    · cases i;exact hF _; exact hG _
    · rw [show 4*t=2*t+2*t by ring]; exact hv.cross hW
    · simp_rw [Fintype.sum_sum_type,Sum.elim_inr,Sum.elim_inl,show ∀ i,odour (g i) U=0 from fun i=> (hr U i).1,sum_const_zero,add_zero,show ∀ i,odour (f0 i) U=amount (f0 i) U from fun i=>(ht U i).1,← yielded T f0 hf]; rw [sum_comm (s:=@Finset.univ (Support f) _) ]; symm; apply sum_congr rfl; intro j hj; rw [sum_eq_single j.1.val.1]
      · exact if_pos rfl
      · intro i _ hi; exact if_neg hi.symm
      simp
    simp_rw [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,show ∀ j,fragrance (f0 j) U i=0 from (fun j=> (ht U j).2 i),sum_const_zero, zero_add, ← yielded Z g hg _ U]; exact sum_congr rfl fun j _=> by rw [(hr U j).2 i]; congr
end YM.MergeProof.Ribbons
