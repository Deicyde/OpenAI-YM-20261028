import YM.Push.ABSOLUTE_SUMS.Array
/-! Uniform absolute tightness at fixed stage. Not just bounded tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Neptune
open Function Filter Lattice RG Push Push.AbsoluteSums Finset
open scoped Topology Classical BigOperators
structure Sparse {ι:Type}(f:ℕ→ι→ℝ):Prop where
    bound : ∃ r:ℝ,∀ n,SumBudget (f n) r
    stalls : ∀ v>0,∃ I:Finset ι,∀ n T,Disjoint I T→∑ i∈T,f n i≤v
variable {ι κ:Type} {f g:ℕ→ι→ℝ}{w:ℕ→ κ→ℝ}
namespace Sparse
lemma value (h:Sparse f)(i k):0≤ f i k:= (h.bound.choose_spec i).1 k
lemma smaller (h:Sparse f)(hf:∀ i k,0≤g i k)(hs:∀ i k,g i k≤f i k):Sparse g:=by
    refine ⟨⟨_,fun i=>budget_mono (h.bound.choose_spec i) (hf i) (hs i)⟩,fun v hv=>?_⟩
    obtain ⟨I,hI⟩:=h.stalls v hv; exact ⟨I,fun i T ht=> (sum_le_sum fun j _=> hs i j).trans (hI i T ht)⟩
lemma tug (h:Sparse f) (hh:Sparse g): Sparse (fun i j=> f i j+g i j):=by
    refine ⟨⟨_,fun n=> budget_plus (h.bound.choose_spec n) (hh.bound.choose_spec n)⟩,fun v hv=>?_⟩
    obtain ⟨S,hS⟩:= h.stalls _ (half_pos hv); obtain ⟨T,hT⟩:=hh.stalls _ (half_pos hv); refine ⟨S∪ T,fun i u hu=>?_⟩; rw [sum_add_distrib]; obtain ⟨ha,hb⟩:= disjoint_union_left.mp hu; exact (add_le_add (hS i u ha) (hT i u hb)).trans_eq (add_halves _)
lemma climb (h:Sparse f){C:ℝ}(he:0≤C) : Sparse (fun i j=> C*f i j):=by
    refine ⟨⟨_,fun n=> budget_scale he (h.bound.choose_spec n)⟩,fun i hi=>?_⟩; rcases eq_or_lt_of_le he with hC|hC
    · exact ⟨∅,fun _ S _=> by simp [← hC,hi.le]⟩
    obtain ⟨T,hT⟩:= h.stalls _ (div_pos hi hC); refine ⟨T,fun n S hs=>?_⟩; rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (hT n S hs) he).trans_eq (by field_simp)
lemma ports (h:Sparse f)(b:ℕ→ℕ): Sparse (fun i=> f (b i)):=⟨⟨_,fun i=> h.bound.choose_spec _⟩,fun v hv=>⟨_,fun i T=> (h.stalls v hv).choose_spec (b i) T⟩⟩
lemma rings {I:Finset ι} (r:ℝ)(h:∀ i k,k∉I → f i k=0)(he:0≤r)(hp:∀ i j,0 ≤ f i j)(hh:∀ i j,j∈I→f i j≤r): Sparse f:=by
    refine ⟨⟨I.card*r,fun i=> budget_of_sum (hp i) (fun j=>?_)⟩,fun v hv=> ⟨I,fun i T ht=> (sum_eq_zero (fun x hx=> h i _ (fun hI=>disjoint_left.mp ht hI hx))).trans_le hv.le⟩⟩
    calc
     ∑ k∈ j,f i k =∑ k ∈ j.filter (· ∈ I),f i k := Eq.symm (sum_subset (filter_subset ..) fun k hk hv=> h i k fun hr=> hv (mem_filter.mpr ⟨hk,hr⟩))
     _ ≤ ∑ k ∈ I,f i k := sum_le_sum_of_subset_of_nonneg (fun x hx=> (mem_filter.mp hx).2) (fun x _ _=> hp _ _)
     _ ≤ ∑ _k ∈ I,r:= sum_le_sum fun x hx=> hh i _ hx
     _ = _:=by simp
lemma pull (h:Sparse f)(a:κ ↪ ι):Sparse (fun i j=> f i (a j)):=by
    refine ⟨⟨_,fun n=> budget_pull a a.injective (h.bound.choose_spec n)⟩,fun v hv=>?_⟩
    obtain ⟨S,hS⟩:= h.stalls v hv; let T:Finset κ:= S.preimage a a.injective.injOn
    refine ⟨T,fun i k hk=> (?_ : ∑ x∈k,f i (a x)≤v)⟩
    simpa only [Finset.sum_map] using hS i (k.map a) (disjoint_left.mpr fun x hx hz=> by
       obtain ⟨y,hy,rfl⟩:= mem_map.mp hz; exact disjoint_left.mp hk ((mem_preimage ..).mpr hx) hy)
lemma either {g:ℕ→(ι ⊕ κ)→ℝ}(h:Sparse fun i (y:ι)=> g i (.inl y))(he:Sparse fun i (y:κ)=>g i (.inr y)):Sparse g:=by
    let u:=fun i (k:ι)=>g i (.inl k); let v:= fun i (k:κ)=>g i (.inr k); obtain ⟨r,hr⟩:=h.bound; obtain ⟨t,ht⟩:= he.bound
    have hk (n:ℕ)(k:Finset (ι⊕κ)):∑ i∈ k,g n i= (∑ i∈ k.toLeft,u n i)+∑ i∈k.toRight,v n i:=by nth_rw 1 [← show k.toLeft.disjSum k.toRight=k by ext i; cases i <;> simp]; exact sum_disjSum ..
    refine ⟨⟨r+t,fun n=>budget_of_sum (fun k=>Sum.rec (motive:=fun i=> 0≤g n i) (h.value n) (he.value n) k) fun j=> (hk n j).trans_le (add_le_add (budget_sum (hr n) _) (budget_sum (ht n) _))⟩,fun e he'=>?_⟩
    obtain ⟨T,hT⟩:=h.stalls _ (half_pos he'); obtain ⟨I,hI⟩:= he.stalls _ (half_pos he')
    exact ⟨T.disjSum I,fun n k hv=> ((hk n k).trans_le (add_le_add (hT n k.toLeft (disjoint_left.mpr fun i hi hy=> disjoint_left.mp hv (Finset.inl_mem_disjSum.mpr hi) (mem_toLeft.mp hy))) (hI n k.toRight (disjoint_left.mpr fun i hi hy=>disjoint_left.mp hv (Finset.inr_mem_disjSum.mpr hi) (mem_toRight.mp hy))))).trans_eq (add_halves _)⟩
lemma arbitrary (h:Sparse f) : Sparse (fun i (k:Finset ι)=>∏ j∈k, f i j):=by
    obtain ⟨C,hC⟩:= h.bound; let g(i:ℕ)(k:Finset ι):=∏ j∈k,f i j
    have hg i k:0≤ g i k:= prod_nonneg fun k _=> h.value ..
    have hv (n:ℕ) (S:Finset (Finset ι)):∑ k∈S,g n k ≤ Real.exp C:=by
         let I:= S.biUnion id; refine (sum_le_sum_of_subset_of_nonneg (show S ⊆ I.powerset from fun k hk=> mem_powerset.mpr (subset_biUnion_of_mem id hk)) (fun x _ _=>hg n x)).trans ?_
         unfold g; rw [← Finset.prod_add_one]; calc
           _ ≤ ∏ k∈I,Real.exp (f n k):= Finset.prod_le_prod (fun i _=>add_nonneg (h.value ..) zero_le_one) (fun i _=>Real.add_one_le_exp _)
           _ ≤ _:=by rw [← Real.exp_sum]; exact Real.exp_monotone (budget_sum (hC n) _)
    refine ⟨⟨_,fun i=> budget_of_sum (hg i) (hv i)⟩,fun v hk=>?_⟩
    obtain ⟨I,hI⟩ := h.stalls _ (div_pos hk (Real.exp_pos C)); refine ⟨I.powerset,fun i S hs=>?_⟩
    let T:= (S.biUnion id).filter (· ∉ I)
    have hT (k) (hp:k∈S):∃ j∈T,j∈k:=by
          obtain ⟨j,hj,hk⟩:= Finset.not_subset.mp (show ¬ k ⊆ I from fun hz=> disjoint_left.mp hs (mem_powerset.mpr hz) hp)
          exact ⟨j,mem_filter.mpr ⟨(subset_biUnion_of_mem id hp) hj,hk⟩,hj⟩
    have hx : ∑ k∈ S,g i k ≤ ∑ k∈S,∑ j∈T,if j∈k then g i k else 0:=sum_le_sum fun k hk => by
         obtain ⟨j,h,hv⟩:= hT _ hk; exact le_trans (Eq.ge (if_pos hv)) (single_le_sum (f:=fun j=> if j∈k then g i k else 0) (fun j _=>by split; exact hg ..; exact le_rfl) h)
    rw [sum_comm] at hx; apply hx.trans; let V(j:ι):= S.filter (j∈·)
    have hV (j:ι): ∑ k∈S,(if j∈k then g i k else 0) ≤ f i j*Real.exp C:=by
         rw [← Finset.sum_filter]; let F:Finset ι→Finset ι:=fun k=> k.erase j
         have he : Set.InjOn F (V j):= fun x hx y hy h=> by
                change x.erase j=y.erase j at h; rw [← insert_erase ((mem_filter.mp hx).2), ← insert_erase ((mem_filter.mp hy).2),h]
         change ∑ k∈ V j,g i k≤ _; refine Eq.trans_le (sum_congr rfl (show ∀ k∈ V j,g i k=f i j*g i (F k) from fun k hk=> (Finset.mul_prod_erase _ _ (mem_filter.mp hk).2).symm)) ?_
         rw [← Finset.mul_sum, ← Finset.sum_image (f:=g i) (s:=V j)]; exact mul_le_mul_of_nonneg_left (hv i _) (h.value ..); exact fun _ hk _ hu=> he hk hu
    exact (sum_le_sum fun j hj=> hV j).trans ((by rw [← sum_mul]; apply mul_le_mul_of_nonneg_right (hI i _ (disjoint_left.mpr fun x hx hy=>((mem_filter.mp hy).2) hx)); exact (Real.exp_pos _).le : ∑ j∈T,f i j*Real.exp C ≤ v / Real.exp C * Real.exp C).trans_eq (div_mul_cancel₀ _ (Real.exp_pos _).ne'))
end Sparse
end YM.FullVolume.Neptune
