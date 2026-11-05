import YM.TraceExtension.Filch.Vines
import YM.TraceExtension.Filch.Brad
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Drupes
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k:ℕ}{o:Site n}{r:ℕ}{F:Acr G n→ℝ}
private abbrev fee(G:Gauge)(t:ℕ):ℕ:= 2*((t+t+1)^4*Fintype.card (Loc G 1))
private lemma members : (univ.filter fun i:pairA G n=>landW o i ≤r).card ≤ fee G r:=by
   let A:= halo r {o} ×ˢ (univ:Finset (Loc G 1))
   have hp:(univ.filter fun i:pairA G n=>landW o i ≤r)⊆ disjSum A A:=by
       intro j hj; have h:landW o j ≤r:= (mem_filter.mp hj).2
       cases j with
       | inl k => exact inl_mem_disjSum.mpr (mem_product.mpr ⟨halo_spec.mpr ⟨o,mem_singleton_self o,h⟩,mem_univ _⟩)
       | inr k => exact inr_mem_disjSum.mpr (mem_product.mpr ⟨halo_spec.mpr ⟨o,mem_singleton_self o,h⟩,mem_univ _⟩)
   apply le_trans (card_le_card hp)
   unfold fee; rw [card_disjSum,two_mul]; apply add_le_add <;> simp only [A,card_product,card_univ] <;> exact Nat.mul_le_mul_right _ (by simpa using Corona.halo_size ({o}:Support n) r)
private lemma inits : (univ.filter fun i: Fin k→pairA G n=>limitN (landW o) i ≤ r).card ≤ (fee G r)^k:=by
   let A:= univ.filter fun i:pairA G n=>landW o i≤r
   let E:(Fin k→ A)↪(Fin k→ pairA G n):= ⟨fun x=> Subtype.val ∘ x, fun i j H=>funext fun z=>Subtype.ext (congr_fun H z)⟩
   have hp:(univ.filter fun i: Fin k→ pairA G n=>limitN (landW o) i ≤ r)⊆ univ.map E:=by
      intro i hi
      have h(x:Fin k): i x∈A:=mem_filter.mpr ⟨mem_univ _,limitN_le _ _ |>.mp ((mem_filter.mp hi).2) x⟩
      exact mem_map.mpr ⟨fun v=>⟨i v,h v⟩,mem_univ _,rfl⟩
   apply (card_le_card hp).trans; rw [card_map,card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]; gcongr; exact members
private lemma charges (j:pairA G n)(he:landW o j ≤ r)(p:ℕ)(hp:p≤4)(T:Acr G n→ ℝ)(hT:T=(fun x=>par o 4 x j))(t:ℕ)(a u:ℝ)(ha:0≤ a)(hu:0≤ u)(hh:Allows 4 T 0 u) :
   let R:=4*(r+1+1)
   Perfect.sail (par o 4) 0 (landW o) p j a t 0 ≤ (fee G R :ℝ)^p * (Perfect.shelter a t R*u):=by
    subst T; intro R; let F:= par (G:=G) o 4; let V(x:Acr G n):= F x j
    unfold Perfect.sail; let A(i:Fin p→ pairA G n):= spot a t 0 (limitN (landW o) i)* ‖leaf F 0 p i j‖
    let D:= univ.filter (fun i=> limitN (landW (G:=G) o) (i:Fin p→ pairA G n) ≤ R)
    change ∑ i,A i≤_
    have hv (i:Fin p→pairA G n): leaf F 0 p i j= entry V 0 i:=by
       unfold entry; let P:Acr G n→L[ℝ] ℝ:= ContinuousLinearMap.proj j
       rw [show V=P ∘ F from rfl,P.iteratedFDeriv_comp_left (parW ..) le_top]; change _=_; rfl
    have hp':(fun x=>Requests Set.univ V (af G n) o x) R:= requestsP j he
    have ht:∑ i∈D,A i=∑ i,A i:=sum_subset (subset_univ D) (fun i _ hi=>by
       unfold A; rw [hv]; obtain ⟨x,hx⟩: ∃ x:Fin p,¬landW o (i x) ≤ R:=by
          by_contra! hh; exact hi (mem_filter.mpr ⟨mem_univ _,(limitN_le _ _).mpr hh⟩)
       rw [hp'.zero (s:=Set.univ) (f:=V) univ_mem (hh.analytic.of_le le_top) i x (by rw[←a_f G n o]; exact hx),norm_zero,mul_zero])
    rw[← ht]; apply (sum_le_sum (g:=fun _=>Perfect.shelter a t (R:ℝ)*u) ?_).trans
    · rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show D.card ≤ _ from inits)) (mul_nonneg (shelter_pos _ _ (by positivity)|>.le) hu)
    intro i hi; unfold A; rw[hv]
    refine mul_le_mul ((spot_mono a t 0 ha ((mem_filter.mp hi).2)).trans (le_of_eq ?_)) ((entry_bound i).trans (hh.norm_le _ hp)) (norm_nonneg _) (shelter_pos _ _ (by positivity)|>.le)
    unfold spot;simp
private lemma poses (G:Gauge)(T:ℕ→ℕ)(h: MarksP fun i=>(T i:ℝ)): MarksP fun i=>(fee G (T i) :ℝ):=by
    unfold fee; push_cast; exact (token 2 (by norm_num)).pair (((((h.booth h).booth (token 1 zero_le_one)).tier 4)).pair (token _ (by positivity)))
-- Perfect.sail price times exp(a*height r)
lemma charZ(G:Gauge)(t:ℕ):∃ J:ℝ, ∃ P:ℕ,1≤J ∧ ∀ (n:Side)(o:Site n)(r:ℕ)(v:pairA G n), landW o v≤ r→∀ p,p≤4→∀ a u:ℝ,0≤ a→0≤ u→
    Perfect.sail (par o 4) 0 (landW o) p v a t u ≤ J*(1+r)^P*Real.exp (a*(4*(r+1+1):ℕ)):=by
   obtain ⟨F,hF,H⟩:= parPay G; let R(r:ℕ):ℕ:=4*(r+1+1); let V(i):ℝ:= ((1+(fee G (R i):ℝ))^4*(1+(R i:ℝ))^t*F i)
   have hr: MarksP fun i=>(R i:ℝ):=by simpa only [R, Nat.add_assoc] using covG (1+1)
   obtain ⟨hw,J,P,hJ,hP⟩:= ((((token 1 zero_le_one).booth (poses G R hr)|>.tier 4).pair (((token 1 zero_le_one).booth hr).tier t)).pair hF : MarksP V)
   refine ⟨J,P,hJ,fun n o r v hv p hp a u ha hu=>?_⟩
   apply (sail_anti _ _ _ _ _ _ _ 0 u ha hu).trans
   refine (charges v hv p hp _ rfl t a (F r) ha (hF.1 r) (H n o r v hv)).trans (le_trans ?_ (mul_le_mul_of_nonneg_right (hP r) (Real.exp_pos _).le))
   let T:=Perfect.shelter a t (R r :ℝ); let Z:ℝ:=fee G (R r); have hz:0≤ Z:=by positivity
   have hp:Z^p≤(1+Z)^4:=(pow_le_pow_left₀ hz (le_add_of_nonneg_left zero_le_one) p).trans (pow_le_pow_right₀ (le_add_of_nonneg_right hz) hp)
   apply (mul_le_mul_of_nonneg_right hp (show 0 ≤ T*F r from mul_nonneg (shelter_pos _ _ (by positivity)|>.le) (hF.1 _))).trans_eq
   change (1+Z)^4*(T*F r)=V r*_ ; unfold V T Perfect.shelter; unfold Z; ring
end YM.Trace.Filch
