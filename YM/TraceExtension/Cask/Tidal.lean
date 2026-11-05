import YM.TraceExtension.Cask.Tagged
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker Extra.Trajectories Function
open scoped Classical
variable {I V:Type*}[DecidableEq I][DecidableEq V]{n:Side}[Fintype V]
variable (P:Staff V I n)
lemma spawn (s:Finset (Finset I)){F:Finset I→Prop}(h:∀ i∈s,F i): ∃ v:Finset {i// F i},beadsP v=s:=by
  refine ⟨s.subtype F,?_⟩; ext i; constructor
  · intro he; obtain ⟨i,hi,rfl⟩:= mem_image.mp he; exact mem_subtype.mp hi
  intro hi; exact mem_image.mpr ⟨⟨i,h i hi⟩,mem_subtype.mpr hi,rfl⟩
def swarm (F: Finset I→ℂ)(T:Support n)(v:Finset I):= if Basic P T v then shipP (crew P v) (F v) else 0
variable {P} {s:Finset I} {T:Support n} {i:Finset (Stiff P)} {b: Finset (Arch P)} {L: Finset I→ℂ}
lemma brood (h:Haven P T (beadsP i) (beadsP b))(h':L (grab i b)=∏ p∈dispel i b,L p) (hp:∀ q, L q≠0→∀ j∈q,P.pole j∩T=P.flag j): booth P L T i b=swarm P L T (grab i b):=by
   rw [booth_shares h,← h']; unfold swarm; by_cases he: L (grab i b)=0
   · rw [he,shipP,Poly.send_zero]; split <;> simp[shipP]
   rw [if_pos (h.compact (hp _ he))]
lemma cubed (hp:∀ q, L q≠0→∀ j∈q,P.pole j∩T=P.flag j)
   (hf:∀ (a:Finset (Stiff P))(b:Finset (Arch P)), Haven P T (beadsP a) (beadsP b)→L (grab a b)=∏ p∈dispel a b,L p):
   ∑' t:Finset (Stiff P)× Finset (Arch P), booth P L T t.1 t.2= ∑' t:Finset I, swarm P L T t:=by
   let Y := fun p:Finset (Stiff P)× Finset (Arch P)=> booth P L T p.1 p.2; let B:=swarm P L T; let R := Function.support Y; let E:=Function.support B
   have h(a:R): Haven P T (beadsP a.val.1) (beadsP a.val.2):= booth_up a.property
   have hz(a:R): Y a.val=B (grab a.val.1 a.val.2):= brood (h a) (hf _ _ (h a)) hp
   let f(a:R):E:= ⟨grab a.val.1 a.val.2, (show B _ ≠0 from fun he=>a.property ((hz a).trans he))⟩
   have hX : Bijective f:=by
      refine ⟨fun i j he=>?_,fun i=>?_⟩
      · have hx: grab i.val.1 i.val.2= grab j.val.1 j.val.2:= congr_arg Subtype.val he; have ht:=h i|>.recover; have hu:= h j|>.recover
        exact Subtype.ext (Prod.ext (Finset.image_injective Subtype.val_injective (ht.1.symm.trans ((congr_arg (flot P T) hx).trans hu.1))) (Finset.image_injective Subtype.val_injective (ht.2.symm.trans ((congr_arg (base P T) hx).trans hu.2))))
      have he:swarm P L T i.val≠0:= i.property; have hv:Basic P T i.val:= of_not_not fun hh=> he (if_neg hh)
      have hx:= hv.splits
      obtain ⟨u,hu⟩:=spawn (F:=Ice P) _ (fun t hT=>(hx.ice t hT).1); obtain ⟨y,hy⟩:= spawn (F:=Boat P) _ (fun t hT=>(hx.boat t hT).1)
      rw [← hu,←hy] at hx; have hs: grab u y= i.val:=by rw [grab,hu,hy,bulk_id]
      have H : Y (u,y)=B i.val:= (brood hx (hf _ _ hx) hp).trans (congr_arg B hs)
      exact ⟨⟨(u,y),fun he' => i.property (H.symm.trans he')⟩,Subtype.ext hs⟩
   let e:=Equiv.ofBijective f hX
   rw [← tsum_subtype_eq_of_support_subset (s:=R) (f:=Y) Set.Subset.rfl, ← tsum_subtype_eq_of_support_subset (s:=E) (f:=B) Set.Subset.rfl,← e.tsum_eq]; exact tsum_congr fun i=>hz i

variable (P T L)[Fintype I]
def shell (p:Support n):Poly (Twin V):= cram (f:=fun i:Stiff P=>shipP (crew P i.val) (blue P L T i.val)) (hill P ∘ Subtype.val) p
def cargo (p:Box n):Poly (Twin V):= cram (f:=fun i:Arch P=>shipP (crew P i.val) (red P L T i.val)) (Pier P) p
lemma emerge (hp:∀ q, L q≠0→∀ j∈q,P.pole j∩T=P.flag j)
   (hf:∀ (a:Finset (Stiff P))(b:Finset (Arch P)), Haven P T (beadsP a) (beadsP b)→L (grab a b)=∏ p∈dispel a b,L p):
   Poly.pass (∑ i:Support n, shell P T L i) * Accent.field (cargo P T L) T= ∑ t, swarm P L T t:=by
   let H:=fun i:Stiff P=> blue P L T i.val; let K:=fun i:Arch P=>red P L T i.val
   let b:= fun i : Stiff P=> spanZ (crew P i.val); let f:=fun i:Stiff P=> Poly.send (b i) (H i)
   have he:∑ i:Support n,shell P T L i=∑ i,f i:=by
      have hp:= Accent.border (hill P ∘ Subtype.val) (p:=f) Summable.of_finite |>.tsum_eq; simp only[tsum_fintype] at hp; simp only [shell,cram,tsum_fintype]; exact hp
   have hg(i:Stiff P): (b i).val.Nonempty:= Finset.Nonempty.product (Ice.rises P i.property) univ_nonempty
   calc
    _ = (∑ s:Finset (Stiff P), ∏ i∈s,f i)* ∑ s:Finset (Arch P), Packets.value (Pier P) (Pattern T) (fun i=>shipP (crew P i.val) (K i)) s:= by
       rw [he,show (∑ i,f i) =_ from rfl, show Poly.pass (∑ i,f i)=_ from pass_sum univ b (fun i _=>hg i) H,prod_one_add]; unfold cargo; rw[field_eq (Pier P) T _ Summable.of_finite Summable.of_finite,tsum_fintype,Finset.powerset_univ]
    _ = _ := by
       have hx := cubed hp hf; simp only [tsum_fintype] at hx; rw [← hx,Fintype.sum_prod_type,sum_mul]; simp_rw [mul_sum]; rfl
end YM.Trace.Cask
