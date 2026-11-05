import YM.MultipleContact.Multi.Script
import YM.Ward.Sum
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Multilinear.Basis
/-! Placement syntax: evaluate only on separated profiles, carry support through finite signed sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Script
open Set Function Filter Table Extraction Spec Ward MeasureTheory
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
variable {G:Gauge}{L:Register G}(S:Table L)
variable {α ι A:Type*}[Fintype ι]
variable {d:ι→ℕ}{v:∀i,S.Field (d i)}
set_option maxHeartbeats 1600000
theorem letters_eq (x:ι→A): letters x= Finset.univ.val.map x:=by
      exact Eq.symm (by rw [← Finset.sum_multiset_singleton]; change mapAdd x _=_; rw [_root_.map_sum]; exact Finset.sum_congr rfl (fun i _=>rfl))
lemma clear_iff (x:ι→Alpha S):(letters x|>.map Prod.snd).Nodup ↔ clear S x:=by
  rw [letters_eq, Multiset.map_map]
  have ht := Multiset.nodup_map_iff_inj_on (f:=Prod.snd∘x) (s:=Finset.univ.val) (d:=Finset.univ.nodup)
  simp at ht
  exact ht

def names (x:Multiset (Alpha S)) : Set E4:= {a|a∈x.map Prod.snd}
lemma names_iff (x:Multiset (Alpha S)){p:E4}: p∈names S x ↔ ∃ q:S.Tag,(q,p)∈x:=by
    simp [names]
def accessible (K:Set E4)(m:Multiset (Alpha S)):=(m.map Prod.snd).Nodup ∧ names S m ⊆ K
def Secure (K:Set E4) (x:Grammar (Alpha S)):Prop:=∀m∈x.coeff.support, accessible S K m
lemma secure_spell {K:Set E4}{v:ι→Alpha S}(hv:Set.range (fun i=>(v i).2) ⊆ K)(hq:clear S v):Secure S K (spell v):=by
    intro m hm; rw [spell_eq] at hm
    have ht:AddMonoidAlgebra.single (letters v) (1:ℂ)=(AddMonoidAlgebra.single (letters v) (1:ℂ)):=rfl  
    simp only [AddMonoidAlgebra.coeff_single,Finsupp.support_single_ne_zero _ one_ne_zero,Finset.mem_singleton] at hm
    rw [hm]; refine ⟨(clear_iff ..).mpr hq,fun p hp=>?_⟩
    obtain ⟨q,hq'⟩:= (names_iff ..).mp hp; obtain ⟨i,hi⟩:=(letters_image v).mp hq'
    exact hv ⟨i,congr_arg Prod.snd hi⟩
variable {p q:Grammar (Alpha S)} {K T:Set E4}
lemma Secure.weak (h:K⊆T)(hp:Secure S K p):Secure S T p:=fun i hi=>⟨(hp i hi).1,Subset.trans (hp i hi).2 h⟩
lemma secure_one : Secure S K 1:=by intro m hm; rw [AddMonoidAlgebra.one_def] at hm; simp only [AddMonoidAlgebra.coeff_single,Finsupp.support_single_ne_zero _ one_ne_zero,Finset.mem_singleton] at hm; rcases hm with rfl; simp [accessible,names]
lemma secure_zero : Secure S K 0:=fun m h=>False.elim (by simpa using h)
lemma Secure.add (h:Secure S K p)(h':Secure S K q):Secure S K (p+q):=by intro m hm; obtain h|h := Finset.mem_union.mp (Finsupp.support_add (show m∈(p.coeff+q.coeff).support from hm)); exacts [‹Secure S K p› _ h,h' _ h] -- shadow
lemma Secure.scalar (h:Secure S K p)(c:ℂ):Secure S K (c • p):=by intro m hm; exact h _ (Finsupp.support_smul (show m∈ (c • (p.coeff)).support from hm))
lemma Secure.diff (h:Secure S K p)(h':Secure S K q):Secure S K (p-q):=(show p+(-1:ℂ)•q=p-q by rw [neg_one_smul]; simp only [sub_eq_add_neg]) ▸ Secure.add S h (Secure.scalar S h' _)
lemma Secure.join (h:Secure S K p) (h':Secure S T q)(hf:Disjoint K T):Secure S (K∪T) (p*q):=by
    intro m hm; obtain ⟨k,hk,l,hl,rfl⟩:=Finset.mem_image₂.mp (AddMonoidAlgebra.support_coeff_mul_subset p q hm) -- implicit pointwise
    obtain ⟨he,hh⟩:=h k hk; obtain ⟨he',hh'⟩:=h' l hl
    refine ⟨?_ ,?_⟩
    · rw [Multiset.map_add,Multiset.nodup_add]; exact ⟨he,he',Multiset.disjoint_left.mpr (fun {r} hr hr'=> Set.disjoint_left.mp hf (hh hr) (hh' hr'))⟩
    intro r hr; obtain hw|hw:=Multiset.mem_add.mp (show r∈(k.map Prod.snd)+(l.map Prod.snd) by rw [← Multiset.map_add]; exact hr)
    · exact Or.inl (hh hw)
    exact Or.inr (hh' hw)
lemma secure_product {α:Type*}{Q:Finset α}{P:α→Set E4}{x:α→Grammar _}(hP:∀i∈Q,Secure S (P i) (x i))(hd:(↑Q:Set α).Pairwise (fun i j=>Disjoint (P i) (P j))):
    Secure S (⋃ i∈Q,P i) (Q.prod x):=by
    classical
    induction Q using Finset.induction with
    | empty=> rw [Finset.prod_empty]; exact secure_one S
    | @insert i q hi ih =>
      rw [Finset.prod_insert hi]; apply Secure.weak S ?_ (Secure.join S (hP i (Finset.mem_insert_self ..)) (ih (fun _ h=>hP _ (Finset.mem_insert_of_mem h)) (hd.mono (by simp))) ?_)
      · intro r hr; obtain he|he:=hr
        · exact Set.mem_iUnion₂.mpr ⟨_,Finset.mem_insert_self ..,he⟩
        obtain ⟨j,hj,hh⟩:=Set.mem_iUnion₂.mp he; exact Set.mem_iUnion₂.mpr ⟨j,Finset.mem_insert_of_mem hj,hh⟩
      rw [Set.disjoint_left]; intro r hr hs; obtain ⟨j,hj,he⟩:=Set.mem_iUnion₂.mp hs
      exact (Set.disjoint_left.mp (hd (Finset.mem_insert_self i q) (Finset.mem_insert_of_mem hj) (by aesop))) hr he

lemma secure_frame {n:ℕ}(x:Fin n→Alpha S)(h:accessible S K (letters x)): clear S x∧∀i, (x i).2∈K:=⟨(clear_iff ..).mp h.1,fun i=>h.2 (by rw [names_iff]; exact ⟨_,(letters_image x).mpr ⟨i,Prod.eta ..⟩⟩)⟩
lemma secure_selected {x:Multiset (Alpha S)}(h:accessible S K x): clear S (pickFrame S x)∧∀i, (pickFrame S x i).2∈K:=secure_frame S (pickFrame S x) ((letters_frame x).choose_spec ▸ h)

theorem basis_express [DecidableEq ι] {𝕜:Type*} [Field 𝕜] {V:ι→Type*}[∀i,AddCommGroup (V i)][∀i,Module 𝕜 (V i)] {F':Type*}[AddCommGroup F'][Module 𝕜 F'](f:MultilinearMap 𝕜 V F')
       {κ:ι→Type*}[∀i,Fintype (κ i)](d:∀i,Module.Basis (κ i) 𝕜 (V i))(w:∀i,V i): f w= ∑ j:(Π i,κ i), (∏ i,(d i).repr (w i) (j i)) • f (fun i=>d i (j i)):=by
      have he : w=(fun i=> ∑ q:κ i, (d i).repr (w i) q • (d i q)):=by funext i; exact (d i).sum_repr (w i)|>.symm
      conv_lhs => rw [he]
      rw [f.map_sum_finset]; simp_rw [f.map_smul_univ]; apply Finset.sum_congr (by ext k; simp [Fintype.mem_piFinset]); simp

lemma sum_terms (a:Grammar A):a=∑ m∈a.coeff.support, (a.coeff m) • spell ((letters_frame m).choose):=by
    trans a.coeff.sum AddMonoidAlgebra.single
    · exact a.sum_coeff_single.symm
    change _=a.coeff.sum (fun m c=>c • (spell _))
    apply Finsupp.sum_congr (g1:=AddMonoidAlgebra.single) (g2:=fun m c=>c • (spell _))
    intro m c
    change AddMonoidAlgebra.single m _ = _ • spell _
    rw [spell_eq,← (letters_frame m).choose_spec, AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]
lemma spell_sum {n m:ℕ}(x:Fin n→A)(y:Fin m→A):spell (Fin.append x y) = spell x * spell y:=by unfold spell;rw [Fin.prod_univ_add]; simp
lemma eval_cont (hs:S.Hierarchy){α:Type*}[TopologicalSpace α]{n:ℕ}{z:α→ Fin n→ E4}{a:α}(hz:ContinuousAt z a)(hc:Injective (z a)){d:Fin n→ℕ}{v:∀i,α→ S.Field (d i)}
     (hv:∀i,ContinuousAt (v i) a):ContinuousAt (fun r=>S.useAt S (points (z r)) (fun i=>(⟨d i,v i r⟩:S.Tag))) a:=by
     classical
     let z'(r:α):=points (z r)
     have hz' :=(PiLp.continuous_toLp 2 _).continuousAt (x:=z a) |>.comp (f:=z) hz
     have hq:z' a∈conf n:=hc
     let κ(i:Fin n):= Fin (Module.finrank ℂ (S.Field (d i))); let f (i:Fin n) : Module.Basis (κ i) ℂ (S.Field (d i)):=Module.finBasis ..
     have heq(b):S.useAt S (z' b) (fun i=>(⟨d i,v i b⟩:S.Tag))=∑ j:(Π i,κ i),(∏ i,(f i).repr (v i b) (j i)) • S.useAt S (z' b) (fun i=>⟨_,f i (j i)⟩):=basis_express (S.classMoment S d (z' b)) f _
     change ContinuousAt (fun b=>S.useAt S (z' b) _) a
     simp_rw [heq]; apply tendsto_finsetSum; intro j hj; exact ContinuousAt.smul (tendsto_finsetProd _ fun i _=> by have hC:= ((f i).coord (j i)).continuous_of_finiteDimensional; exact hC.continuousAt.comp (hv i)) ((S.class_smooth S hs.smooth _ _ hq).continuousWithinAt.continuousAt ((conf_open _).mem_nhds hq) |>.comp hz')
theorem placed_continuous (H:S.Hierarchy){α:Type*}[TopologicalSpace α] (x:ι→α→ E4) {a:α}(hx:∀i,ContinuousAt (x i) a){d:ι→ℕ}{v:∀i,α→ S.Field (d i)} (hV:∀i,ContinuousAt (v i) a) (hinj:Injective (x · a)):
   ContinuousAt (fun a=>evaluation S (spell (fun i:ι=>((⟨_,v i a⟩:S.Tag),x i a)))) a:=by
       classical
       let e:= (Fintype.equivFin ι).symm; simp_rw [eval_frame S H.laws.toSymmetric e,read_points]
       let q := fun a:α=>points (fun i=>x (e i) a); let z:= fun a=> ((fun i=> ((⟨_,v i a⟩:S.Tag),x i a)) ∘ e)
       change ContinuousAt (fun b=>Truncated S (q b) (fun i=>(z b i).1)) a
       have hp:= continuousAt_pi.mpr fun i=> hx (e i)
       have h'0 := (PiLp.continuous_toLp (2:NNReal) _).continuousAt.comp hp
       have hq': q a∈conf _:= hinj.comp e.injective
       have hq:= h'0.eventually (show _ from (conf_open _).mem_nhds hq')
       suffices he:ContinuousAt (fun b=> S.useAt S (q b) (fun i:Fin (Fintype.card ι)=>(z b i).1)) a from he.congr ((by filter_upwards [hq] with b hb; change _ = Truncated S _ _; unfold Truncated; rw [if_pos (show q b ∈ conf _ from hb)]) : (fun b=>S.useAt S (q b) (fun i=>(z b i).1)) =ᶠ[𝓝 a] (fun b=>Truncated S (q b) (fun i=>(z b i).1)))
       exact eval_cont S H (z:=fun a i=>x (e i) a) hp hq' fun i=>hV (e i)
end YM.MultipleContact.Script
