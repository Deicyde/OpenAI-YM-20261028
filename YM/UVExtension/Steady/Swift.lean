import YM.UVExtension.Steady.Platoon
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Fixed level tight ledger, not root-specific or exponent dependent.
Gates here require both Tail tight and regular valuation bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Push.AbsoluteSums Finset
open scoped BigOperators Topology ContDiff Classical
variable {ι κ π : Type*}{v:Filter ι}
structure Swift (v:Filter ι)(a:ι→κ→ℝ): Prop where
  books : ∃ r:ℝ,∀ᶠ n in v, SumBudget (a n) r
  drops (ε:ℝ)(he:0<ε): ∃ s:Finset κ,∀ᶠ n in v, SumBudget (fun i=> if i∈s then 0 else a n i) ε
namespace Swift
variable {a b:ι→κ→ℝ} {c c':ι→π→ℝ}
lemma tills (p:Swift v a):∃ r>0, ∀ᶠ n in v, SumBudget (a n) r:=by
   obtain ⟨r,h⟩:=p.books; exact ⟨max r 1,zero_lt_one.trans_le (le_max_right ..), h.mono fun i hi=> budget_loosen hi (le_max_left ..)⟩
lemma le (p:Swift v a)(h:∀ᶠ n in v,∀ i,0≤ b n i∧ b n i≤a n i): Swift v b:=by
  constructor
  · obtain ⟨r,hr⟩:=p.books; exact ⟨r,(h.and hr).mono fun n ⟨hx,h⟩=> budget_mono h (fun i=>(hx i).1) (fun i=>(hx i).2)⟩
  intro ε he; obtain ⟨s,hs⟩:= p.drops _ he; refine ⟨s,(hs.and h).mono fun n ⟨hs,h⟩=> budget_mono hs (fun i=>?_) (fun i=>?_)⟩
  · split; rfl; exact (h _).1
  split; rfl; exact (h _).2
lemma eq (p:Swift v a)(he:∀ᶠ n in v,a n=b n):Swift v b:= by
   obtain ⟨r,hr⟩:=p.books; apply p.le; filter_upwards [he,hr] with n h hh i; rw [← h]; exact ⟨hh.1 _,le_rfl⟩
lemma exhaust (p:Swift v a)(ε:ℝ)(he:0<ε)(s:ι→Finset κ)(h:∀ i,∀ᶠ k in v,i∈s k): ∀ᶠ n in v, SumBudget (fun i=> if i∈s n then 0 else a n i) ε :=by
   obtain ⟨r,hr⟩:= p.drops ε he
   have hx: ∀ᶠ n in v, r⊆s n:= (eventually_all_finset r).mpr (fun i (_:i∈r)=> h i)
   filter_upwards [hr,hx] with i hi ht; refine budget_mono hi (fun j=>?_) (fun j=>?_)
   · split; exact le_rfl
     next h=> simpa only [if_neg (mt (@ht j) h)] using hi.1 j
   by_cases h:j∈s i
   · rw [if_pos h]; exact hi.1 _
   rw [if_neg h,if_neg (mt (@ht j) h)]
lemma plus (p:Swift v a)(q:Swift v b): Swift v (fun n i=> a n i+b n i):=by
   obtain ⟨r,hr⟩:= p.books; obtain ⟨t,ht⟩:= q.books; constructor
   · exact ⟨_,(hr.and ht).mono fun n hn=> budget_plus hn.1 hn.2⟩
   intro ε he; obtain ⟨s,hs⟩:= p.drops _ (half_pos he); obtain ⟨u,hu⟩:= q.drops _ (half_pos he)
   refine ⟨s∪u,(hs.and hu).mono fun n ⟨hp,hu⟩=> budget_loosen (budget_mono (budget_plus hp hu) (fun i=>?_) (fun i=>?_)) (by linarith)⟩
   · split; rfl
     next hv=> obtain ⟨hx,h⟩:= not_or.mp (mt mem_union.mpr hv); simpa only [if_neg hx,if_neg h] using (budget_plus hp hu).1 i
   split; exact (budget_plus hp hu).1 i
   next hv=> obtain ⟨hx,h⟩:= not_or.mp (mt mem_union.mpr hv); simp only [if_neg hx,if_neg h,le_rfl]
lemma nil (a:κ→ℝ){u:ℝ}(h:SumBudget a u): Swift v (fun _=> a):=by
   refine ⟨⟨_,Eventually.of_forall fun _=> h⟩,fun ε he=>?_⟩
   have hh := h.2.1.hasSum
   obtain ⟨s,hs⟩:= (hh.eventually (Metric.ball_mem_nhds _ (half_pos he))).exists
   refine ⟨s,Eventually.of_forall fun n=>?_⟩; have hp := Metric.mem_ball.mp hs
   let f i:= if i∈s then 0 else a i; have hz : SumBudget f u:=budget_mono h (fun i=>by unfold f; split; rfl; exact h.1 _) (fun i=>by unfold f; split; exact h.1 _; rfl)
   refine ⟨hz.1,hz.2.1,?_⟩
   have hh := Summable.sum_add_tsum_subtype_compl h.2.1 s -- inspect
   have ha : ∑' i,f i=∑' i:(↥ ((s:Set κ)ᶜ)), a i:=by
     rw [_root_.tsum_subtype]; refine tsum_congr fun j=> ?_
     unfold f; split; next h=> exact (Set.indicator_of_notMem (show ¬j∈ _ from (by simpa using h)) _).symm
     next h=> exact (Set.indicator_of_mem h a).symm
   rw [show (fun i=>ite _ 0 _)= f from rfl, ha]; change (∑ i∈s,a i)+ (∑' i:(↥ ((s:Set κ)ᶜ)), a i)=_ at hh
   change dist (∑ i∈s,a i) (∑' i,a i)<ε/2 at hp; rw [Real.dist_eq] at hp; linarith only [hh,abs_lt.mp hp|>.1,he]
lemma scales (p:Swift v a) (r:ℝ)(hr:0≤r):Swift v (fun n i=> r*a n i):=by
   obtain ⟨s,hs⟩:= p.books; refine ⟨⟨_,hs.mono (fun n hn=> budget_scale hr hn)⟩,fun ε he=>?_⟩
   obtain ⟨t,ht⟩:= p.drops (ε/(1+r)) (div_pos he (by positivity)); have h: r*(ε/(1+r)) ≤ ε:= by apply (mul_le_mul_of_nonneg_right (by linarith : r≤1+r) (by positivity : 0≤ε/(1+r))).trans_eq; field_simp
   refine ⟨t,ht.mono fun n hn=>?_⟩; simpa only [mul_ite,mul_zero] using budget_loosen (budget_scale hr hn) h
lemma letters (p:Swift v a) (e:π→ κ)(he:Injective e): Swift v (fun n i=> a n (e i)):=by
  obtain ⟨r,hr⟩:=p.books; refine ⟨⟨r,hr.mono fun n h=>budget_pull _ he h⟩,fun ε h=>?_⟩
  obtain ⟨t,ht⟩:= p.drops ε h; refine ⟨(t.finite_toSet.preimage he.injOn).toFinset, ht.mono fun n hn=>?_⟩; simp only [Set.Finite.mem_toFinset,Set.mem_preimage,Finset.mem_coe]; exact_mod_cast budget_pull _ he hn
lemma mixes (p:Swift v a)(q:Swift v c):Swift v (fun n (i:κ×π)=> a n i.1*c n i.2):=by
   obtain ⟨r,hr,hK⟩:=p.tills; obtain ⟨t,ht,hT⟩:=q.tills
   refine ⟨⟨_,(hK.and hT).mono (fun n hn=> budget_prod hn.1 hn.2)⟩,fun ε he=>?_⟩
   obtain ⟨s,hs⟩:= p.drops (ε/(r+t)) (by positivity); obtain ⟨u,hu⟩:= q.drops (ε/(r+t)) (by positivity)
   refine ⟨s×ˢu,?_⟩; filter_upwards [hs,hu,hK,hT] with n hv hx hy hg
   refine budget_loosen (budget_mono (budget_plus (budget_prod hy hx) (budget_prod hv hg)) ?_ ?_) ?_
   · rintro ⟨b,c⟩; split; exact le_rfl; exact mul_nonneg (hy.1 _) (hg.1 _)
   · rintro ⟨b,c⟩; split
     · exact (budget_plus (budget_prod hy hx) (budget_prod hv hg)).1 _
     next h=> rcases not_and_or.mp (mt mem_product.mpr h) with h|h
              · apply (le_add_of_nonneg_left ((budget_prod hy hx).1 _)).trans' ; rw [if_neg h]
              apply (le_add_of_nonneg_right ((budget_prod hv hg).1 _)).trans'; rw [if_neg h]
   have h : r+t>0:=add_pos hr ht; apply le_of_eq; field_simp
lemma unionK {f:κ→ℝ} {g:π→ℝ}{u w:ℝ}(h: SumBudget f u) (k:SumBudget g w) : SumBudget (Sum.elim f g) (u+w):=by
     refine budget_of_sum (fun i=> match i with| Sum.inl z=> h.1 _| .inr z=> k.1 _) (fun s=>?_)
     calc
        _ = (∑ i∈s.toLeft,f i)+(∑ i∈s.toRight,g i):= by rw [← Finset.toLeft_disjSum_toRight (u:=s),sum_disjSum]; simp
        _ ≤ _:=add_le_add (budget_sum h _) (budget_sum k _)
lemma onion (p:Swift v a)(q:Swift v c): Swift v (fun n=> Sum.elim (a n) (c n)):=by
  obtain ⟨r,hr⟩:=p.books; obtain ⟨s,hs⟩:= q.books; refine ⟨⟨r+s,(hr.and hs).mono fun i hi=> unionK hi.1 hi.2⟩,fun ε he=>?_⟩
  obtain ⟨z,hz⟩:=p.drops (ε/2) (half_pos he); obtain ⟨Z,hZ⟩:= q.drops (ε/2) (half_pos he);
  refine ⟨z.disjSum Z,(hz.and hZ).mono fun i hi=>?_⟩; convert budget_loosen (unionK hi.1 hi.2) (le_of_eq (add_halves ε)) using 1; ext b; cases b <;> simp
lemma shutter (p:Swift v a) (r : ι→ κ→ Prop): Swift v (fun n i=> if r n i then a n i else 0):=by
   obtain ⟨s,hs⟩:=p.books; apply p.le; filter_upwards [hs] with n h i; split <;> first| exact ⟨h.1 _,le_rfl⟩| exact ⟨le_rfl,h.1 _⟩
lemma under_limit [Fintype κ](p:∃ t,∀ᶠ n in v, SumBudget (a n) t): Swift v a:=by exact ⟨p,fun ε he=>⟨Finset.univ,by simp [SumBudget,he.le]⟩⟩
lemma sight [Finite κ](hp:∀ i,∃ r,∀ᶠ n in v, 0≤ a n i ∧ a n i≤r): Swift v a:=by
   letI:=Fintype.ofFinite κ; choose r hr using hp; exact under_limit ⟨∑ i,r i,(eventually_all.mpr hr).mono fun n h=> budget_finite (fun i=>(h i).1) (sum_le_sum fun i _=> (h i).2)⟩
lemma absorbs (p:∃ r:ℝ,∀ᶠ n in v, SumBudget (a n) r)(q:∀ ε:ℝ,0<ε→ ∃ f g:ι→κ→ℝ,Swift v f∧ (∀ᶠ n in v, SumBudget (g n) ε) ∧ ∀ᶠ n in v,∀ i,a n i≤f n i+g n i): Swift v a:=by
   refine ⟨p,fun ε he=>?_⟩; obtain ⟨r,hr⟩:=p; obtain ⟨f,g,h,hf,hg⟩:= q _ (half_pos he); obtain ⟨s,hs⟩:= h.drops (ε/2) (half_pos he); refine ⟨s,?_⟩
   filter_upwards [hr,hf,hg,hs] with n hr hv hp hq; refine budget_loosen (budget_mono (budget_plus hq hv) ?_ ?_) (by linarith)
   · intro i; split; rfl; exact hr.1 _
   intro i; split; exact (by rw [zero_add]; exact hv.1 _); exact hp _
end Swift
end YM.UVExtension.Steady
