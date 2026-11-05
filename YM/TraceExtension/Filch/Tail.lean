import YM.TraceExtension.Filch.Press
import YM.TraceExtension.Filch.Shoals
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Extra.Iteration
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k:ℕ}{o:Site n}{r:ℕ}{F:Acr G n→ℝ}{a A:ℝ}
private abbrev S(o:Site n)(r:ℕ): Acr G n→L[ℝ] Acr G n:= stone (landW o) r
private abbrev W(o:Site n): Acr G n→ Acr G n:=par o 4
def rusk (o:Site n)(r:ℕ)(F:Acr G n→ℝ):= choral 4 F-choral 4 F ∘ S o r
lemma walk_r (h:ContDiffAt ℝ ω F 0)(hh:F=ᶠ[𝓝 0] F ∘ exactP o): braid (F-(choral 4 F ∘ S o r) ∘ W o) (rusk o r F ∘ W o) 0 4:=by
    have ht:braid F (choral 4 F ∘ W o) 0 4:=by
       apply (braided (n:=4) hh).trans; apply (wove (a:=0) (w:=exactP o) ((exactZ o).symm ▸ repitch h 4) ((exactZ o).symm ▸ h) (rhythm F 4|>.contDiffAt) (exactW o)).trans
       exact enthral _ _ _ (v:=0) (exactZ _) (parZ ..) (par_charm o 4) (rhythm F 4|>.contDiffAt) (exactW o) (parW ..)
    have hp: ContDiffAt ℝ ω ((choral 4 F ∘ S o r) ∘ W o) 0:=((rhythm F 4|>.comp (S o r).contDiff).contDiffAt.comp _ (parW ..))
    exact ht.sub (braided (EventuallyEq.refl ..)) h (rhythm F 4|>.contDiffAt.comp _ (parW ..)) hp hp
section
variable (o r)
lemma leafU (he:ContDiffAt ℝ ω F 0)(hk:k≤4)(v:Fin k→pairA G n) : leaf (rusk o r F) 0 k v=if limitN (landW o) v≤r then 0 else leaf F 0 k v:=by
    unfold Perfect.leaf bank rusk; have hy:= rhythm F 4
    rw [iteratedFDeriv_sub_apply (hy.contDiffAt.of_le (m:=k) le_top) ((hy.comp (S o r).contDiff).contDiffAt.of_le le_top),iter_lin_at (show ContDiffAt ℝ (↑k) _ (S o r 0) from hy.contDiffAt.of_le (m:=k) le_top),map_zero (S o r),← repitch he 4 k hk, _root_.sub_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    split <;> rename_i hv
    · have hp (i:Fin k): S o r (desk (v i))=desk (v i):=by
          have hx:= (limitN_le ..).mp hv i; ext1 j
          rw[stone_at (landW o)]; split_ifs with hh; · rfl
          simp [desk,Pi.single_apply,show j≠v i from fun e=> hh (e.symm ▸ hx)]
      simp only [Function.comp_apply, hp,← Function.comp_def desk v,sub_self]
    obtain ⟨i,hi⟩:∃ i,¬landW o (v i) ≤r:=by by_contra! h; exact hv ((limitN_le ..).mpr h)
    suffices h: (S o r (desk (v i)))=0 by rw [show iteratedFDeriv ℝ k F 0 (fun j=> S o r ((desk ∘ v) j))=0 from ContinuousMultilinearMap.map_coord_zero (i:=i) _ h,sub_zero]
    funext j; change S o r (desk (v i)) j=0
    rw [stone_at (landW o)]; split_ifs with hh; · simp [desk, Pi.single_apply,show j ≠ v i from fun h=> hi (h ▸ hh)]
    rfl
-- cost only t=4; can amplify local t via log.Need e positive.
include o r
private lemma hale (t:ℕ)(R:ℕ)(h:0<a)(hp:a≤1) {L:ℕ}{B:ℝ} (hR:r ≤ R)(hB:1≤ B)(M:ℕ)(hm:M≤4):
    Perfect.shelter (a/100) 4 R*(B*(1+R)^L*Real.exp ((a/100)*(4*(R+1+1):ℕ)))^M ≤ Perfect.spot a 4 0 R*(B^4*Real.exp 100*momentPrice (L*4) (a/4)*Real.exp (-(a/4)*r)):=by
    let D:= B*(1+R)^L*Real.exp ((a/100)*(4*(R+1+1):ℕ)); have hx0:1 ≤ 1+(R:ℝ):=by simp
    have hx:1≤D:=by
       unfold D; exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hx0)) (Real.one_le_exp (by positivity))
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hm) (Perfect.shelter_pos _ _ (by positivity)|>.le)) ?_
    unfold Perfect.shelter Perfect.spot Perfect.shelter; rw [sub_zero,max_eq_right (show 0 ≤ (R:ℝ) by positivity),mul_pow,mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    let p:=a/100*R;let q:=a/100*(4*(R+1+1):ℕ)
    have hc: Real.exp (p+4*q+(a/4)*R) ≤ Real.exp (a*R+100-(a/4)*r):=by
        apply Real.exp_le_exp.mpr; unfold p q; push_cast; have hx:(r:ℝ)≤R:=Nat.cast_le.mpr hR
        nlinarith only[hp,mul_le_mul_of_nonneg_left hx h.le,mul_nonneg h.le (show (0:ℝ)≤R by positivity)]
    let A:ℝ:=(1+(R:ℝ))^4; have ha : 0 ≤ A:=pow_nonneg (by positivity) _
    let C:= momentPrice (L*4) (a/4); have hg:0<C:=momentPrice_pos _ (by positivity)
    change A * _ * _ ≤ _
    norm_num only [Nat.cast_ofNat]; have he:=spendMoment (L*4) (η:=a/4) (by positivity) (show 0 ≤ (R:ℝ) by positivity)
    calc
     A*Real.exp p*(B^4*(1+R)^ (L*4)*Real.exp (4*q)) ≤ A* Real.exp p*(B^4*(C*Real.exp (a/4*(R:ℝ)))*Real.exp (4*q)):=by gcongr
     _ = (A*B^4*C)*Real.exp (p+4*q+(a/4)*R):= by rw[Real.exp_add,Real.exp_add];ring
     _ ≤ _ :=(mul_le_mul_of_nonneg_left hc (by positivity : 0≤ A*B^4*C)).trans_eq (by rw [sub_eq_add_neg (a*R+100),Real.exp_add,Real.exp_add]; rw [←neg_mul]; unfold A C; ring)
end
def pay(B:ℝ)(L:ℕ)(a:ℝ) (r:ℕ):=B^ (4:ℕ)*Real.exp 100*momentPrice (L*4) (a/4)*Real.exp (-(a/4)*(r:ℝ))
def jointM(B:ℝ)(L:ℕ):= B^ (4:ℕ)*Real.exp 100* ∑ i∈range 5,(Fintype.card (OrderedFinpartition i):ℝ)
def jointC (B:ℝ)(L:ℕ)(a:ℝ) (r:ℕ):= jointM B L*momentPrice (L*4) (a/4)*Real.exp (-(a/4)*(r:ℝ))
lemma longshoals (G:Gauge): ∃ D:ℝ,∃ P:ℕ,0 ≤ D ∧ ∀ (n:Side)(o:Site n)(r:ℕ)(a A:ℝ)(F:Acr G n→ℝ),0<a→a≤1→0≤ A→ ContDiffAt ℝ ω F 0→ F=ᶠ[𝓝 0] F ∘ exactP o→(∀ k,k≤4→cost (landW o) a 4 0 (leaf F 0 k) ≤ A)→
    ∀ i,i≤4→ cost (landW o) (a/100) 4 0 (leaf (F-(choral 4 F ∘ S o r) ∘ W o) 0 i) ≤ D * momentPrice P (a/4) *Real.exp (-(a/4)*r)*A:=by
    obtain ⟨B,L,hB,H⟩:= charZ G 4
    have hb:0<B:=lt_of_lt_of_le zero_lt_one hB
    refine ⟨jointM B L,L*4,?_,?_⟩
    · unfold jointM; positivity
    intro n o r a A F ha hp hA he h hv i hi
    let R:=landW (G:=G) o; let K:= a/100; let P:=pay B L a r; let V:=rusk o r F; have hp':0≤P:=by unfold P pay; have hh:0 < momentPrice _ (a/4):=momentPrice_pos (L*4) (by positivity); positivity
    have hz:=walk_r (r:=r) he h i hi
    have hy:ContDiffAt ℝ ω V ((W o) 0):=((rhythm F 4).sub ((rhythm F 4).comp (S o r).contDiff)).contDiffAt
    have hu:leaf (F-(choral 4 F ∘ S o r) ∘ W o) 0 i = leaf (V ∘ W o) 0 i := congr_arg bank hz
    rw [hu]; refine (split_fees (A:=R) V _ _ hy (parW ..) i).trans ((sum_le_sum (g:=fun _=>P*A) (fun c _=>?_)).trans ?_)
    · apply (fares V (W o) 0 c (L:=1) (B:=R) le_rfl (show 0 ≤ K by positivity)).trans
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (hv _ (c.length_le.trans hi)) hp'); unfold cost; rw[mul_sum]; apply sum_le_sum; intro j _
      let g:= limitN R j; let Z:= Fintype.card (OrderedFinpartition c.length)
      simp only[show W (G:=G) o 0=0 from parZ .., show V=rusk o r F from rfl, leafU o r he (c.length_le.trans hi) j]
      by_cases hh: limitN (landW o) j ≤ r
      · rw [if_pos hh,norm_zero,mul_zero]; apply mul_nonneg hp' (mul_nonneg (spot_pos ..).le (norm_nonneg _))
      rw [if_neg hh, ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      let D:=B*(1+g)^L*Real.exp (K*(4*(g+1+1):ℕ)); have hZ:
          (∏ i:Fin c.length,sail (W o) 0 R (c.partSize i) (j i) K 4 (g:ℝ)) ≤ D ^ c.length:=by
          refine (prod_le_prod (fun i _=> sail_nn ..) (g:=fun _=>D) (fun i _=>H n o g (j i) (limitN_ge _ _ _) (c.partSize i) ((c.partSize_le i).trans hi) _ _ (by positivity) (by positivity))).trans (le_of_eq (by simp))
      simp only [div_one]; apply (mul_le_mul_of_nonneg_left hZ (Perfect.shelter_pos _ _ (by positivity)|>.le)).trans
      rw [mul_comm P]; exact hale o r 0 g ha hp (by change _ ≤ limitN (landW _) _; omega) hB _ (c.length_le.trans hi)
    rw [sum_const,card_univ,nsmul_eq_mul]; have hX:= single_le_sum (s:= range 5) (f:=fun i=>(Fintype.card (OrderedFinpartition i):ℝ)) (fun i _=>by positivity) (mem_range.mpr (show i < 5 by omega)); exact (mul_le_mul_of_nonneg_right hX (mul_nonneg hp' hA)).trans_eq (by unfold P pay jointM; ring)
end YM.Trace.Filch
