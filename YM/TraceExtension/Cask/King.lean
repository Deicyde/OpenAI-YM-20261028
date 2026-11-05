import YM.TraceExtension.Cask.Choral
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Extra.Trajectories Function
open scoped Classical
variable {L K J V:Type*}[DecidableEq L][DecidableEq K][DecidableEq J][DecidableEq V]{n:Side}[Fintype V]
variable (P:Staff V (Grain L K J) n) (x:J→V)(slotp:K→Box n)
variable [Fintype J][Fintype K][Fintype L]
lemma load (w:J→V)(F:Finset V→Prop) (g:J→ℂ): (∑ b: Finset V, if F b then ∏ i∈b,cram w g i else 0)=∑ s:Finset J, if Packets.selected w F s then ∏ i∈s,g i else 0:=by
    let W:= Twin V; let Q:= Poly.bead W
    have he(i): ∑' j:{x// w x=i}, Q (g j.val)= Q (cram w g i):= by simp only[tsum_fintype,cram]; rw [← map_sum]
    have hx:= (Packets.repack w F (Q ∘ g) Summable.of_finite Summable.of_finite).tsum_eq
    have hp : ∑ b:Finset V, Q (if F b then ∏ i∈b,cram w g i else 0)= ∑ s:Finset J, Q (if Packets.selected w F s then ∏ i∈s,g i else 0):=by
       change _= _; simp only[tsum_fintype,Packets.value,comp_apply] at hx; have hm(i):∑ j:{x// w x=i}, Q (g j.val)= Q (cram w g i):=by rw[← he i,tsum_fintype]
       simp_rw [hm] at hx; simp_rw [apply_ite Q,map_prod,map_zero]; exact hx
    have hi:Function.Injective Q:=fun u v h=> show u=v from by simpa [Q,Poly.bead] using congr_arg (fun f:Poly W=>f.part W.quiet) h
    apply hi; rw [map_sum,map_sum]; exact hp
variable (T:Support n)
def hushK (T:Support n)(p:Box n→ℂ):= ∑ s:Finset (Box n), if Pattern T s then ∏ i∈s,p i else 0
def stairC (P:Staff V J n) (s:Finset V)(q:J)(f:J→ℂ):= if P.cast q ⊆ s then f q else 0
variable (f:Grain L K J→ℂ)
def clothW := ∏ i:V,cram x (f ∘ Sum.inl) i
def trump (s: Finset V): ℂ:= (∏ i:L, (1+stairC P s (.inr (.inl i)) f))* hushK T (cram slotp (fun i:K=> stairC P s (.inr (.inr i)) f))
def hoard (s : Finset V)(p:Finset (Grain L K J)):ℂ:= if joinP P p⊆ s then if Packets.selected slotp (Pattern T) p.toRight.toRight ∧ Packets.selected x (·=univ) p.toLeft then ∏ i∈p,f i else 0 else 0
-- θ polynomial. Z name. signs external
lemma tidings (S:Finset V): clothW x f*trump P slotp T f S=∑ p:Finset (Grain L K J),hoard P x slotp T f S p:=by
    have hx: clothW x f =∑ p:Finset J,if Packets.selected x (·=(univ:Finset V)) p then ∏ i∈p,f (.inl i) else 0:=by rw [← load (g:=fun i=>f (Sum.inl i))]; rw [sum_eq_single (univ:Finset V),if_pos rfl];rfl; intro i _ hi; exact if_neg hi; simp
    unfold trump hushK; rw [prod_one_add,powerset_univ,load, hx]
    let e:(Finset (Grain L K J)) ≃ (Finset J× Finset (L ⊕ K)):= Finset.sumEquiv.toEquiv
    let m:(Finset (L⊕ K))≃(Finset L × Finset K):= Finset.sumEquiv.toEquiv
    nth_rw 1 [← e.symm.sum_comp (hoard P x slotp T f S)]; rw [Fintype.sum_prod_type,sum_mul]; refine sum_congr rfl fun p _=> ?_
    let g := stairC P S; rw [← m.symm.sum_comp (fun i=> hoard P x slotp T f S (e.symm (p,i))), Fintype.sum_prod_type,sum_mul,mul_sum]; refine sum_congr rfl fun i _=> ?_; rw [mul_sum,mul_sum]; refine sum_congr rfl fun a _=> ?_
    let c:= m.symm (i,a); let t:=e.symm (p,c); have h₁:t.toLeft=p:= congr_arg Prod.fst (e.apply_symm_apply _); have h₂:t.toRight=c:=congr_arg Prod.snd (e.apply_symm_apply _); have h₃:c.toLeft=i:=congr_arg Prod.fst (m.apply_symm_apply _); have h₄:c.toRight=a:=congr_arg Prod.snd (m.apply_symm_apply _)
    have ht: ∏ u∈t,f u=(∏ j∈p,f (.inl j))*((∏ j∈i,f (.inr (.inl j)))*(∏ j∈a,f (.inr (.inr j)))):=by rw [prod_sum_eq_prod_toLeft_mul_prod_toRight,h₂,h₁,prod_sum_eq_prod_toLeft_mul_prod_toRight (s:=c),h₃,h₄]
    have hp : (∏ j∈i,stairC P S (.inr (.inl j)) f)*(∏ j∈a,stairC P S (.inr (.inr j)) f)=if joinP P t ⊆ S then (∏ j∈i,f (.inr (.inl j)))*(∏ j∈a,f (.inr (.inr j))) else 0:=by
       split
       next h=>
          have hp (j : L⊕ K)(hj:j∈ c): stairC P S (.inr j) f=f (.inr j):= if_pos ((Finset.subset_biUnion_of_mem (fun i:L⊕K=>P.cast (.inr i)) (h₂.symm ▸ hj)).trans h)
          exact congr_arg₂ _ (prod_congr rfl (fun j hj=> hp (.inl j) (mem_toLeft.mp (h₃.symm ▸ hj)))) (prod_congr rfl (fun j hj=> hp (.inr j) (mem_toRight.mp (h₄.symm ▸ hj))))
       next h=>
          obtain ⟨j,hj,hs⟩:= Finset.not_subset.mp h; obtain ⟨v,hv,hr⟩:=mem_biUnion.mp hj; have hu: stairC P S (.inr v) f=0:=if_neg (fun hj=> hs (hj hr)); rw [h₂] at hv; cases v with
          | inl v=> rw [prod_eq_zero (show v∈i from h₃ ▸ mem_toLeft.mpr hv) hu,zero_mul]
          | inr v=> rw [prod_eq_zero (show v∈a from h₄ ▸ mem_toRight.mpr hv) hu,mul_zero]
    have hy: e.symm (p,m.symm (i,a))=t:=rfl
    rw [hy]; unfold hoard; rw [ht,h₁,h₂,h₄]; split_ifs at * <;> simp only [hp,zero_mul,mul_zero] <;> tauto
lemma teaL : clothW x f*∑ i: Finset V,(-1:ℂ)^i.card*trump P slotp T f i= (-1:ℂ)^Fintype.card V * ∑ t:Finset (Grain L K J), if fetchP P x slotp T t then ∏ i∈t,f i else 0:=by
    let z:=@univ V _; have hp: clothW x f*∑ i: Finset V,(-1:ℂ)^i.card*trump P slotp T f i = ∑ i∈z.powerset,(-1:ℂ)^i.card*(∑ t:Finset (Grain L K J), hoard P x slotp T f i t):=by
       rw [mul_sum,show z.powerset=univ from powerset_univ]; refine sum_congr rfl fun i _=> (mul_left_comm ..).trans ?_; rw [tidings]
    rw [hp,windF (V:=V) (S:=z) (F:=fun i:Finset V=>∑ t:Finset (Grain L K J),hoard P x slotp T f i t),powder_sum (F:=fun t i=> hoard P x slotp T f i t),show z.card=Fintype.card V from card_univ]; refine congr_arg₂ (·*·) rfl (sum_congr rfl (fun t _=> ?_))
    unfold hoard fetchP; rw [powder_mono]; split_ifs with h h' h'' h'' <;> first | rfl | tauto
variable (H:Roles P x slotp)
include H
lemma codeC (h:∀ i, f i≠0→ P.pole i ∩ T=P.flag i): (∑ p :Finset (Grain L K J), (swarm P (fun s=>(-1:ℂ)^(crew P s).card*∏ i∈s,f i) T p).part (Stock.final (Duel V)))=clothW x f*∑ i:Finset V,(-1:ℂ)^i.card*trump P slotp T f i:=by
   rw [teaL,mul_sum]; refine sum_congr rfl (fun p _=>?_)
   have hx: Stock.final (Duel V)=spanZ (crew P p)↔crew P p=univ:=by
       constructor
       · intro hp; exact eq_univ_of_forall (fun i=> (mem_product.mp (show (i,true)∈(spanZ (crew P p)).val from hp ▸mem_univ _)).1)
       intro hp; rw [hp]; exact Subtype.ext (show _ from (show (@univ (Duel V) _)=_ from univ_product_univ.symm))
   unfold swarm; rw [fetch_eq P x slotp H]; by_cases ht : Woven P p∧crew P p=univ∧gem P p=T
   · rw [if_pos ht]; split
     · rw [shipP,Poly.part_send,if_pos (hx.2 ht.2.1)]; simp only [ht.2.1,card_univ]
     next H'=> have hv:(∏ i∈p,f i)=0:= Classical.byContradiction fun hb=> H' ⟨ht.1,ht.2.2,fun j hj=> h j (fun hy=> hb (prod_eq_zero hj hy))⟩
               rw [hv,mul_zero];rfl
   rw [if_neg ht,mul_zero]; split
   next he=> rw [shipP,Poly.part_send,if_neg (fun hp=> ht ⟨he.formed,hx.mp hp,he.complete⟩)]
   rfl
end YM.Trace.Cask
