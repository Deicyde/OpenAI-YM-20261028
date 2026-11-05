import YM.RG08.Nacre.Archer
import YM.RG08.Rate.Shadows

/-!
# Bills for strict steps. Street can use on a time array, any one eligible Ω. Budget method
 for paying geometry assumptions at each parallel demand: deliver all post step costs under
 Good once publicly, and use this algebra consumer. Width constraints v supplied separately
 PER step. δ one common for list of *prior* difficulties on this whole domain, need not ≤1.
-/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Steam Isles Gauge Rate Stair
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type} {I J : O→Type}{n : ℕ}

structure Exchange (O:Type) where
 Good : (O→ℝ)→ Prop -- includes nn at each. can encode near & age cap etc, uniform constants
 cheap : (O→ℝ)→ Prop -- ephemeral (cutoff). Nonneg also; mixed.
 zero : cheap (fun _=>0)
 steady r (hr:0≤r) : Good (fun _=>r)
 hear p q : Good p → Good q → Good fun i=>p i+q i
 moreover p q : Good p→Good q→Good fun i=>p i*q i
 lasts p q : cheap p→cheap q→cheap fun i=>p i+q i
 awe p q : Good p→cheap q→cheap fun i=>p i*q i
 safe p : Good p→∀ i,0≤p i
 hale p q : Good p→ (∀ x,0≤ q x)→ (∀ x,q x ≤ p x)→ Good q
 nope p:cheap p→Good p
 hat p q:cheap p→(∀ x,0≤ q x)→ (∀ x,q x ≤ p x)→cheap q

variable (D:Exchange O)

lemma tiny {p:O→ℝ}(h:D.cheap p)(x:O):0≤p x:=D.safe _ (D.nope _ h) _
lemma stairs {p:O→ℝ}(h:D.Good p)(n:ℕ):D.Good fun x=> p x ^ n:=by
 induction n with
 | zero=>simpa using D.steady 1 zero_le_one
 | succ n hi=> simp_rw [pow_succ];exact D.moreover _ _ hi h
lemma steadyPay {p:ℝ→ℝ}(h:Wage p){w:O→ℝ}(he:D.Good w)(ht:∀ x, 1≤w x):D.Good fun x=>p (w x):=by
 obtain ⟨a,n,ha,H⟩:=h
 exact D.hale _ _ (D.moreover _ _ (D.steady _ ha) (stairs D he n)) (fun i=> (H _ (ht i)).1) (fun i=> (H _ (ht i)).2)

lemma crowd {K:Type}(s:Finset K)(p:K→O→ℝ)(h:∀ i∈s,D.Good (p i)):D.Good fun j=>∑ i∈s,p i j:=by
 induction s using Finset.induction_on with
 | empty=>simp only [Finset.sum_empty];exact D.steady 0 le_rfl
 | insert a s ha ih=>simpa only [Finset.sum_insert ha] using D.hear _ _ (h a (Finset.mem_insert_self ..)) (ih (fun z hz=>h z (Finset.mem_insert_of_mem hz)))
lemma shells {K:Type}(s:Finset K)(p:K→O→ℝ)(h:∀ i∈s,D.cheap (p i)):D.cheap fun j=>∑ i∈s,p i j:=by
 induction s using Finset.induction_on with
 | empty=>simpa only [Finset.sum_empty] using D.zero
 | insert a s ha ih=>simpa only [Finset.sum_insert ha] using D.lasts _ _ (h a (Finset.mem_insert_self ..)) (ih (fun z hz=>h z (Finset.mem_insert_of_mem hz)))

variable (w d:O→ℝ)(A B:∀ x:O,Flake n (Market (I x)))
/-- P common. d doesn't have to be cheap until declared. -/
def Lance := ∃ p,D.Good p ∧ ∀ x, Cot (n:=n) (carpet _) (w x) (d x) (p x) (A x) (B x)
/-- upper side available (for repeated component comparison forcing). -/
def Bound := ∃ p,D.Good p ∧ ∀ x,Held (carpet _) (w x) (p x) (A x)
/-- lower side cutoff stability in SAME orientation. -/
def Change := ∃ p,D.cheap p ∧ ∀ x,Held (carpet _) (w x) (p x) (A x-B x)
variable {D A B} {F G:∀ x:O,Flake n (Market (I x))} {w d}
lemma joined {p:O→ℝ}(h:D.Good p)(hp:∀ x,Held (carpet _) (w x) (p x) (A x)) : Lance D w (fun _=>0) A (A:∀ x:O,Flake n (Market (I x))):= ⟨_,h,fun x=>⟨D.safe _ h _,hp x,hp x,by rw [sub_self];exact zero_held⟩⟩
lemma zero (D:Exchange O)(w d:O→ℝ): Lance D w d (fun x=> (0: Flake n (Market (I x)))) (fun x=> (0: Flake n (Market (I x)))):= ⟨_, D.steady _ le_rfl,fun _=> Cot.zero 0 le_rfl⟩
lemma Lance.add (h:Lance D w d F G)(hk:Lance D w d A B)(hd:∀ i,0≤ d i): Lance D w d (fun i=>F i+A i) (fun i=>G i+B i):=by
 obtain ⟨a,ha,h⟩:=h;obtain ⟨b,hb,hT⟩:=hk;exact ⟨_,D.hear _ _ ha hb,fun i=>(h i).add (hT i) (hd i)⟩
lemma Lance.opposite (h:Lance D w d F G): Lance D w d (fun i=> -F i) (fun i=> -G i):=by
 obtain ⟨a,ha,h⟩:=h;refine ⟨_,ha,fun i=>?_⟩;convert (h i).smul (-1) using 1 <;> simp
lemma Lance.sub (h:Lance D w d F G)(hk:Lance D w d A B)(hd:∀ i,0≤d i): Lance D w d (fun i=>F i-A i) (fun i=>G i-B i):=by simp_rw [sub_eq_add_neg];exact h.add hk.opposite hd
lemma Lance.series {K:Type}(s:Finset K)(F G:K→ (x:O)→Flake n (Market (I x)))(h:∀ i∈s,Lance D w d (F i) (G i))(hd:∀ i,0 ≤ d i): Lance D w d (fun i=>∑ j∈s,F j i) (fun i=>∑ j∈s,G j i):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty];exact Ducat.zero D w d
 | insert a s ha ih=>simpa only [Finset.sum_insert ha] using ((h a (Finset.mem_insert_self ..)).add (ih (fun i hi=>h _ (Finset.mem_insert_of_mem hi))) hd)
lemma Bound.join (h:Bound D w F): Lance D w d F F:=by obtain ⟨u,hu,h⟩:=h;refine ⟨_,hu,fun i=> ⟨D.safe _ hu _,h i,h i,?_⟩⟩;rw [sub_self];exact zero_held
lemma Lance.fore (h:Lance D w d F G):Bound D w F:=by obtain ⟨p,hq,hy⟩:=h;exact ⟨_,hq,fun i=>(hy i).near⟩
lemma Lance.until (h:Lance D w d F G):Bound D w G:=by obtain ⟨p,hq,hy⟩:=h;exact ⟨_,hq,fun i=>(hy i).far⟩
lemma Lance.berry (h:Lance D w d F G)(hd:D.cheap d):Change D w F G:=by obtain ⟨p,hq,h⟩:=h;exact ⟨_,D.awe _ _ hq hd,fun i=>(h i).compare⟩
lemma Lance.vow (h:Lance D w d F G){s t:O→ℝ}(he:∀ i,d i ≤ s i)(hs:∀ i,t i ≤ w i):Lance D t s F G:=by
 obtain ⟨p,hq,hy⟩:=h;exact ⟨_,hq,fun i=>⟨(hy i).gain,(hy i).near.mono (hs i) le_rfl (fun _=>le_rfl),(hy i).far.mono (hs i) le_rfl (fun _=>le_rfl),(hy i).compare.mono (hs i) (mul_le_mul_of_nonneg_left (he i) (D.safe _ hq _)) (fun _=>le_rfl)⟩⟩
lemma grazing (h:Bound D w F)(ht:Bound D w G)(hZ:Change D w F G):∃ d,D.cheap d ∧ Lance D w d F G:=by
 obtain ⟨a,ha,hA⟩:=h;obtain ⟨b,hb,hB⟩:=ht;obtain ⟨d,hd,H⟩:=hZ
 refine ⟨_,hd,_,D.hear _ _ (D.steady _ zero_le_one) (D.hear _ _ ha hb),fun x=>?_⟩
 have hx:=D.safe _ ha x;have hv:=D.safe _ hb x;have hg:=tiny D hd x
 exact ⟨show 0≤ 1+(a x+b x) by positivity,(hA x).mono le_rfl (by linarith) (fun _=>le_rfl),(hB x).mono le_rfl (by linarith) (fun _=>le_rfl),(H x).mono le_rfl (le_mul_of_one_le_left hg (by linarith)) (fun _=>le_rfl)⟩

-- collect δ's across finitely many promises of possibly different arities etc.
lemma gathering {K:Type}(s:Finset K)(P:K→(O→ℝ)→Prop)(hD:∀ i∈s,∃ d,D.cheap d∧ P i d)(hM:∀ i∈s,∀ a b:O→ℝ,(∀ x,a x≤ b x)→ P i a → P i b):∃ d,D.cheap d∧ ∀ i∈s,P i d:=by
 induction s using Finset.induction_on with
 | empty=>refine ⟨_,D.zero,by simp⟩
 | insert k s hk ih=>
   obtain ⟨p,hp,H⟩:=hD k (Finset.mem_insert_self ..)
   obtain ⟨q,hq,HQ⟩:=ih (fun i hi=>hD _ (Finset.mem_insert_of_mem hi)) (fun i hi=>hM i (Finset.mem_insert_of_mem hi))
   refine ⟨_,D.lasts p q hp hq,fun i hi=>?_⟩
   have hj:=hM i hi
   rcases Finset.mem_insert.mp hi with rfl|hi
   · exact hj _ _ (fun x=>le_add_of_nonneg_right (tiny D hq x)) H
   exact hj _ _ (fun x=>le_add_of_nonneg_left (tiny D hp x)) (HQ i hi)
end YM.RG08.Ducat
