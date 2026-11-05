import YM.UVExtension.Steady.Swift
import YM.Push.ABSOLUTE_SUMS.Copies
import YM.Push.ABSOLUTE_SUMS.Product

/-!
 Multiplicity transport. tight=uniformly finite tail of absolute sums at FIXED volume;
 neither coefficient bound nor pointwise convergence is enough. No effectivity.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Push.AbsoluteSums Finset
open scoped BigOperators Topology ContDiff Classical
variable {ι κ π : Type*}{v:Filter ι}
namespace Swift
variable {a b:ι→κ→ℝ} {c c':ι→π→ℝ}

lemma stories (h:Swift v a) : Swift v (fun n (s: Finset κ)=> ∏ i∈s,a n i):= by
  obtain ⟨r,hr⟩:=h.books; refine ⟨⟨_,hr.mono fun i hi=> Product.set_products hi⟩,fun ε he=>?_⟩
  obtain ⟨s,hs⟩:= h.drops (ε/Real.exp r) (by positivity); refine ⟨s.powerset,?_⟩; filter_upwards [hr,hs] with i hi hh
  let Y k:=∏ j∈k, a i j; have hY: SumBudget Y (Real.exp r):=Product.set_products hi
  let g(b:Finset κ):= if b∈s.powerset then (0:ℝ) else Y b; have hg(b:Finset κ):0≤ g b:=by unfold g; split; exact le_rfl; exact hY.1 _
  convert (show SumBudget g ε from ?_) using 2
  · unfold g Y; split_ifs <;> rfl
  refine budget_of_sum hg fun t=>?_
  let Z:= t.biUnion id; let b(j:κ) (A:Finset κ):= if j∈A ∧ j∈ Z ∧ j∉s then (if j∈s then 0 else a i j)*Y (A.erase j) else 0; let T j:= t.filter (fun A=> j∈A ∧ j∈Z∧ j∉s)
  let f(j:κ):= if j∈s then 0 else a i j
  have hA (A:Finset κ)(hz:A∈t):g A ≤ ∑ j∈Z,b j A:=by
      have he(j:κ)(h:j∈ Z):0≤b j A:= by unfold b; split; exact mul_nonneg (hh.1 _) (hY.1 _); exact le_rfl
      unfold g; split
      · exact sum_nonneg he
      next h=> obtain ⟨x,hx,hy⟩:= Finset.not_subset.mp (mt mem_powerset.mpr h); have hT :x∈Z:= mem_biUnion.mpr ⟨A,hz,hx⟩; refine le_trans ?_ (single_le_sum he hT); unfold b; rw [if_pos ⟨hx,hT,hy⟩, if_neg hy]; exact (Finset.mul_prod_erase A _ hx).symm.le
  have hK j : ∑ i∈ t,b j i≤ f j*Real.exp r:=by
      calc
         _ = ∑ i∈ T j,b j i:= (sum_subset (filter_subset ..) fun i hi hk=> if_neg fun h=>hk (mem_filter.mpr ⟨hi,h⟩)).symm
         _ = ∑ i∈ T j,f j*Y (i.erase j):=sum_congr rfl fun i hi=> if_pos ((mem_filter.mp hi).2)
         _ = f j*∑ i∈ (T j).image (·.erase j), Y i:= by rw [← mul_sum,sum_image]; intro i hi k hk he; dsimp only at he; rw [← insert_erase ((mem_filter.mp hi).2.1),← insert_erase ((mem_filter.mp hk).2.1),he]
         _ ≤ _ := mul_le_mul_of_nonneg_left (budget_sum hY _) (hh.1 _)
  calc
    _ ≤ ∑ i∈t,∑ j∈Z,b j i:=sum_le_sum hA
    _ = _:= sum_comm
    _ ≤ ∑ i∈ Z,f i * Real.exp r:= sum_le_sum fun i _=> hK i
    _ ≤ ε:= by rw [← sum_mul]; exact (mul_le_mul_of_nonneg_right (budget_sum hh _) (Real.exp_pos _).le).trans_eq (by rw [div_mul_cancel₀ ε (Real.exp_pos _).ne'])

open Multiple
-- embed unordered repetitions as sets of tagged pairs.
def history (s: Reps κ):Finset (κ × ℕ):= Finset.univ.image fun i:↥s.fst=> (i.val,s.2 i)
lemma indexed (s:Reps κ)(i:κ)(x:ℕ): (i,x)∈history s ↔ ∃ h:i∈s.fst,s.2 ⟨i,h⟩=x:=by unfold history; simp
lemma history_inj : Injective (history (κ:=κ)):= by
   have h s : (history (κ:=κ) s).image Prod.fst=s.fst:=by ext i; rw [Finset.mem_image]; constructor; rintro ⟨⟨i,k⟩,hi,rfl⟩; exact ((indexed _ _ _).1 hi).choose; intro h; exact ⟨_,(indexed _ i _).2 ⟨h,rfl⟩,rfl⟩
   rintro ⟨s,z⟩ ⟨t,k⟩ he; have ht : s=t:=(h ⟨s,z⟩).symm.trans ((congr_arg _ he).trans (h ⟨t,k⟩)); subst t; congr 1; funext u; obtain ⟨v,hv⟩:= u; have hP:(v,k ⟨v,hv⟩)∈history ⟨s,z⟩:=he ▸ (indexed _ v _).2 ⟨hv,rfl⟩; obtain ⟨m,hm⟩:= (indexed _ v _).1 hP; exact hm
lemma repetitions (h:Swift v a) : Swift v (fun n s=> manyW (a n) s):= by
   obtain ⟨r,hr,hh⟩:= h.tills; let f n:= r^n/(n.factorial:ℝ)
   have hF :SumBudget f (∑' i,f i):= ⟨fun i=>by unfold f; positivity, Real.summable_pow_div_factorial r,le_rfl⟩
   let g(i)(q:κ×ℕ):= a i q.1^(q.2+1)/((q.2+1).factorial:ℝ)
   have hx:Swift v g:=by
      apply (h.mixes (nil _ hF)).le; filter_upwards [hh] with i hi p; have ht:0≤a i p.1:=hi.1 _; refine ⟨?_,?_⟩
      · unfold g; positivity
      unfold g f; rw [pow_succ',← mul_div_assoc]; refine div_le_div₀ ?_ ?_ (by positivity) ?_
      · positivity
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (budget_single hi _) _) ht
      exact_mod_cast Nat.factorial_le (show p.2≤p.2+1 by omega)
   apply (hx.stories.letters _ history_inj).eq; filter_upwards with i; funext j; unfold history; rw [prod_image]; exact rfl; intro x hx z hz h; exact Subtype.ext (congr_arg Prod.fst h)

lemma numbered (n:ℕ) (f:Fin n→ ι→κ→ ℝ) (h:∀ i,Swift v (f i)): Swift v (fun x (t:Fin n→κ)=>∏ i,f i x (t i)) := by
   induction n with
   | zero =>
     have : Finite (Fin 0→κ):= by exact Finite.of_subsingleton
     apply sight; intro i; exact ⟨1,by simp⟩
   | succ n ih =>
     simp_rw [Fin.prod_univ_succ]; exact ((h 0).mixes (ih (fun j=> f j.succ) (fun j=> h j.succ))).letters _ (Fin.consEquiv (fun _ : Fin (n+1)=>κ)).symm.injective
lemma items [Fintype π] (f:π→ι→κ→ℝ)(h:∀ i,Swift v (f i)): Swift v (fun x (t:π→κ)=> ∏ i,f i x (t i)):=by
   let a:= Fintype.equivFin π; let t:=Equiv.arrowCongr a (Equiv.refl κ)
   refine ((numbered _ (fun i=> f (a.symm i)) (fun i=>h _)).letters t t.injective).eq (Eventually.of_forall ?_); intro i; funext n; exact Equiv.prod_comp a.symm (fun i'=> f i' i (n i'))

open Trees
lemma finances {A:κ→Type*}{f:ι→ Sigma A → ℝ} (h:Swift v a)(hh:∀ i,Swift v (fun n j=> f n (Sigma.mk i j)))(ht:∀ᶠ n in v,∀ i, SumBudget (fun j=> f n (Sigma.mk i j)) (a n i)): Swift v f:=by
   obtain ⟨r,hr⟩:=h.books; constructor
   · exact ⟨r,(hr.and ht).mono fun n hi=> sigma_total _ _ hi.2 hi.1⟩
   intro ε he; let E:=ε/2; have hv:0<E:=half_pos he; obtain ⟨s,hs⟩:=h.drops E hv
   let z:=E/(s.card+1); have hp:0<z:= by unfold z; positivity
   choose u hu using fun i=> (hh i).drops z hp
   let b:= s.sigma u; refine ⟨b,?_⟩; filter_upwards [hs, (eventually_all_finset s).mpr (fun i _=> hu i),ht] with n hv' h hp'
   have hx : SumBudget (fun j=> if j∈s then z else 0) E:=by
       have hw:= budget_over s (fun j t=> if t=j then z else 0) (fun _=> z) ?_; swap
       · intro i _; exact budget_of_sum (fun j=>by split; exact hp.le; exact le_rfl) (fun j=>by simp only [Finset.sum_ite_eq']; split <;> first | exact le_rfl| exact hp.le)
       simp only [Finset.sum_const,nsmul_eq_mul] at hw; refine budget_loosen ?_ ((mul_le_mul_of_nonneg_right (show (s.card:ℝ) ≤ s.card+1 by linarith) hp.le).trans_eq (by unfold z; field_simp)); simpa only [sum_ite_eq] using hw
   apply budget_loosen _ (le_of_eq (add_halves ε)); refine sigma_total _ _ ?_ (budget_plus hx hv'); intro i; by_cases he:i∈s
   · simp only [b,mem_sigma,he,true_and,if_true,add_zero]; exact h i he
   simp only [b,mem_sigma,he,false_and,if_false,zero_add]; exact hp' _
end Swift
end YM.UVExtension.Steady
