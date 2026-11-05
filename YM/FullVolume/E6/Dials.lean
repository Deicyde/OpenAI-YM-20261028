import YM.FullVolume.E6.Sparse
import YM.Push.ABSOLUTE_SUMS.Copies
/-! more stable ledger.Branches. Finite period only.-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Neptune.Sparse
open Function Filter Lattice RG Push Push.AbsoluteSums Multiple Finset
open scoped Topology Classical BigOperators
variable {ι κ:Type}{f:ℕ→ι→ℝ}{g:ℕ→κ→ℝ}
lemma constant {f:ι→ℝ}(h:Summable f)(he:∀ i,0 ≤ f i): Sparse fun _=> f:=by
    refine ⟨⟨_,fun n=>⟨he,h,le_rfl⟩⟩,fun v hv=>?_⟩
    obtain ⟨s,hs⟩:= (h.hasSum.eventually (lt_mem_nhds (sub_lt_self _ hv))).exists
    exact ⟨s,fun n u hu=> by have h':∑ i∈s,f i+∑ i∈u,f i ≤ ∑' i,f i:= by rw [← sum_union hu]; exact h.sum_le_tsum _ fun i _=> he i
                             linarith⟩
lemma pairs (h:Sparse f)(he: Sparse g): Sparse (fun n (u:ι×κ)=>f n u.1 * g n u.2):=by
    obtain ⟨A,hA⟩:= h.bound; obtain ⟨B,hB⟩:= he.bound; have hh :0≤A:=budget_nonneg (hA 0); have hp:0 ≤B:=budget_nonneg (hB 0)
    let F n (u:ι×κ):= f n u.1 * g n u.2; have hx n u:0 ≤ F n u:= mul_nonneg (h.value ..) (he.value ..)
    refine ⟨⟨_,fun i=> budget_prod (hA i) (hB i)⟩, fun v hv=>?_⟩
    let t:= v/(1+(A+B)); have ht:0<t:= div_pos hv (by positivity); obtain ⟨S,hS⟩:= h.stalls t ht; obtain ⟨P,hP⟩:= he.stalls t ht
    refine ⟨S×ˢP,fun i T hu=>?_⟩
    let s:= T.filter fun x=> x.1∈S; let p:=T.filter fun x=> ¬ x.1∈S
    have hg (Y:Finset (ι×κ)):∑ i'∈Y, F i i' ≤ (∑ a∈Y.image Prod.fst,f i a) *(∑ a∈Y.image Prod.snd,g i a):=by
       rw [sum_mul_sum];rw [← sum_product']; exact sum_le_sum_of_subset_of_nonneg (fun x hx=> mem_product.mpr ⟨mem_image_of_mem _ hx,mem_image_of_mem _ hx⟩) (fun x _ _=> hx i x)
    have hk j T(hj:∀ k∈(T:Finset κ),k∉P): ∑ x∈T,g j x≤ t:= hP _ _ (Finset.disjoint_left.mpr fun k hk hx=> hj _ hx hk)
    have hy : Disjoint S (p.image Prod.fst):=by
       refine disjoint_left.mpr fun x hx hz=> ?_; obtain ⟨k,hk,rfl⟩:= mem_image.mp hz; exact (mem_filter.mp hk).2 hx
    have hL y (hf:y∈ s.image Prod.snd):y∉P:=by
       obtain ⟨k,hk,rfl⟩:=mem_image.mp hf; exact fun i=> disjoint_left.mp hu (mem_product.mpr ⟨(mem_filter.mp hk).2,i⟩) (mem_filter.mp hk).1
    change ∑ x∈T,F i x≤_; rw [← Finset.sum_filter_add_sum_filter_not _ (fun x:ι×κ=> x.1∈S)]; refine (add_le_add ((hg s).trans (mul_le_mul (budget_sum (hA i) _) (hk _ _ hL) (sum_nonneg fun i _=>he.value ..) hh)) ((hg p).trans (mul_le_mul (hS i _ hy) (budget_sum (hB i) _) (sum_nonneg fun i _=>he.value ..) ht.le))).trans ?_
    have h' : t*(1+(A+B))=v:= div_mul_cancel₀ _ (by positivity); nlinarith only [ht,h']
lemma courtyard (h:Sparse f) :Sparse (fun n r=>manyW (f n) r):=by
    obtain ⟨C,hC⟩:= h.bound; have hB:0≤ C:=budget_nonneg (hC 0); let v(k:ℕ):= C^k / (k+1).factorial; have hv i:0≤v i:=div_nonneg (pow_nonneg hB _) (by positivity)
    have hm:Summable v:= Summable.of_nonneg_of_le hv (fun i=> div_le_div_of_nonneg_left (pow_nonneg hB i) (by positivity) (Nat.cast_le.mpr (Nat.factorial_le (Nat.le_succ _)))) (Real.summable_pow_div_factorial C)
    let g(x:Reps ι) (i:↥x.1):ι×ℕ:=(i.val,x.2 i); let z(x:Reps ι):=image (g x) univ
    have hx (x:Reps ι): (z x).image Prod.fst=x.fst:=by ext i; simp [z,g]
    have hz: Injective z:=by
       rintro ⟨x,u⟩ ⟨y,w⟩ he; obtain rfl:x=y:= by rw [← show _=x from hx ⟨x,u⟩,he,hx]
       congr 1; funext i; have hh: g ⟨x,u⟩ i∈z ⟨x,w⟩:=he ▸ mem_image_of_mem _ (mem_univ i); obtain ⟨k,-,hk⟩:= mem_image.mp hh
       obtain rfl:k=i:=Subtype.ext (congr_arg Prod.fst hk); exact (congr_arg Prod.snd hk).symm
    let F n (s:ι×ℕ):= f n s.1 * v s.2; refine (((h.pairs (constant hm hv)).arbitrary).pull ⟨z,hz⟩).smaller (fun n r=>manyW_nonneg (h.value n) r) fun i r=>?_
    change _ ≤ ∏ x∈ z r,F i x; unfold z; rw [Finset.prod_image]; swap
    · exact fun k _ j _ h=>Subtype.ext (congr_arg Prod.fst h)
    exact Finset.prod_le_prod (fun k _=> div_nonneg (pow_nonneg (h.value ..) _) (by positivity)) (fun k _=> by
          change f i _ ^ _ / _ ≤ f i k.val * v (r.2 k); unfold v; rw [pow_succ',mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ (h.value ..); gcongr; exact h.value ..; exact budget_single (hC i) _)
lemma square {α:Type}[Fintype α] (h:Sparse f): Sparse (fun i (z:α→ι)=>∏ a,f i (z a)):=by
    let F(i:ℕ)(q:α×ι):= f i q.2
    have he:Sparse F:=by
        have hx:Sparse (fun _:ℕ => fun _:α=>(1:ℝ)):= constant ((hasSum_fintype _).summable) (fun _=>zero_le_one)
        simpa only [one_mul,F] using hx.pairs h
    let Z(v:α→ι):Finset (α×ι):= image (fun i=>(i,v i)) univ
    have ht : Injective Z :=by
          intro i j hx; funext k; have h:(k,i k)∈Z j:= hx ▸ mem_image_of_mem (fun k=>(k,i k)) (mem_univ k); simpa [Z,eq_comm] using h
    refine ((he.arbitrary).pull ⟨Z,ht⟩).smaller (fun i _=> prod_nonneg fun a _=>h.value ..) fun i z=>?_ ; change _ ≤ ∏ x∈ Z z,F i x; unfold Z; rw [Finset.prod_image] <;> first | rfl | skip
    · exact fun k _ j _ h=> congr_arg Prod.fst h
-- bounded rank by sparse fibre with order
lemma braid {ι: ℕ→ Type} {f:ℕ→ Sigma ι→ℝ}(h:∀ i:ℕ, Sparse fun n (x:ι i)=> f n ⟨i,x⟩) (S:Finset ℕ) : Sparse (fun n p=> if p.fst∈ S then f n p else 0):=by
    induction S using Finset.induction_on with
    | empty=>simpa only [notMem_empty,↓reduceIte] using (show Sparse (fun _=>fun _:Sigma ι=> (0:ℝ)) from constant (by simp) fun _=>le_rfl)
    | insert i s hi ih=>
      let g(n:ℕ)(p: Sigma ι):= if p.fst=i then f n p else 0
      let e:ι i ↪ Sigma ι:=⟨fun x=> ⟨i,x⟩,fun x y h=> Sigma.mk.inj_iff.mp h |>.2|>eq_of_heq⟩
      obtain ⟨u,hu⟩:= (h i).bound
      have hx n k:0≤g n k:=by
           unfold g; split; next he=> cases k; subst i; exact (h _|>.value ..)
           next hv=> rfl
      have he n (T: Finset (Sigma ι)): ∑ x∈ T,g n x = ∑ x∈T.preimage e e.injective.injOn,f n (e x):=by
          rw [← Finset.sum_image e.injective.injOn];
          rw [← sum_subset (f:= g n) (s₁:=image e (preimage _ _ e.injective.injOn)) (fun x h=> by rcases mem_image.mp h with ⟨i,hi,rfl⟩; exact (mem_preimage ..).mp hi) (fun x hk hh=>?_)]
          · exact sum_congr rfl fun i hi=> by rcases mem_image.mp hi with ⟨i,_,rfl⟩; exact if_pos rfl
          unfold g; refine if_neg fun hf=>hh ?_; rcases x with ⟨x,yy⟩; change x=i at hf; subst x; exact mem_image.mpr ⟨yy,(mem_preimage ..).mpr hk,rfl⟩
      have h' : Sparse g:=by
         refine ⟨⟨u,fun i=> budget_of_sum (hx i) fun s=> (he i s).trans_le (budget_sum (hu i) _)⟩,fun v hv=>?_⟩
         obtain ⟨S,hS⟩:=(h i|>.stalls v hv); exact ⟨S.map e,fun n T hv=> (he n T).trans_le (hS n _ (disjoint_left.mpr fun i hi hh=> disjoint_left.mp hv (mem_map_of_mem _ hi) ((mem_preimage ..).mp hh)))⟩
      convert! h'.tug ih using 1; ext a b; by_cases he:b.fst=i <;> simp_all [g]
lemma layer {d:ι→ℕ}(h:∀ i,Sparse fun n (p:ι)=>if d p< i then f n p else 0){v:ℕ→ℝ} (he:∀ z n,SumBudget (fun p=> if z≤ d p then f n p else 0) (v z))(hv:Tendsto v atTop (𝓝 0)): Sparse f:=by
   refine ⟨⟨v 0,fun i=> by simpa using he 0 i⟩,fun a ha=>?_⟩; obtain ⟨i,hi⟩:= (hv.eventually (gt_mem_nhds (half_pos ha))).exists
   obtain ⟨S,hS⟩:= (h i).stalls _ (half_pos ha); refine ⟨S,fun n T ht=>?_⟩; refine le_trans ?_ ((add_le_add (hS n T ht) ((budget_sum (he i n) T).trans (le_of_lt hi))).trans_eq (add_halves a)); rw [← sum_add_distrib]; exact sum_le_sum (fun _ _=> by split <;> grind)
end YM.FullVolume.Neptune.Sparse
