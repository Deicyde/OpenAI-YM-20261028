import YM.TraceExtension.Perfect.Chaff

/-! # Mean-transpose probe as ink of weight 3 (shift by one extra due continuum response rooting). -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Matrix Lattice Precision Laurent Stationary Bloch Next.Free Exterior Finset RG
open YM.AnalyticNext.QuarticMatch.Hessian
open Tracks
open scoped BigOperators Topology ContDiff
variable {c f:Side}
def trench (S:StepData c f)(x:Site f)(j:Body 1 f):= (mean S).transpose (x,j.2)

lemma polar_bud (α T:ℝ)(t j:ℕ)(hα:0≤α)(hT:0≤T): ∃ C:ℝ,0 ≤ C ∧ ∀ (c f:Side)(S:StepData c f),S.patch.J=j → ∀ (v:Site c)(x:Site f),(separation (S.ratio.embed v) x:ℝ) ≤ T*S.ratio.count.val→
     Settle (roof v) (fun p:Body 1 f=> separation p.1 x) (mean S).transpose 0 (trench S x) α t S.ratio.count.val C:=by
 let K:ℕ:=small j
 let W:=shelter α t (T+K+5)
 have htℓ:0≤T+K+5:=by positivity
 have hW:0 ≤ W:= (shelter_pos α t htℓ).le
 refine ⟨8*W,mul_nonneg (by norm_num) hW, fun c f S e v x h =>?_⟩
 let L:ℝ:=S.ratio.count.val; have hp:1 ≤ L:= by unfold L; exact_mod_cast (show 1≤S.ratio.count.val from S.ratio.count.property)
 have hL : 0<L:=lt_of_lt_of_le zero_lt_one hp
 let A(p:Body 1 c):=roof v p
 let g:=S.ratio
 have hA(z:Site f)(r:ℝ)(y : TypeFace 1)(p:Body 1 c)(hw:mean S p (z,y)≠0)(hz:(separation x z:ℝ) ≤ L*(5+r)) : spot α t r (separation v p.1) ≤ W:=by
     have h' : L*separation v p.1 ≤ (separation (g.embed v) x:ℝ)+(separation x z:ℝ)+(separation z (g.embed p.1):ℝ):=by
        have he:= (Corona.below g v p.1).trans (le_trans (separation_triangle _ z _) (Nat.add_le_add_right (separation_triangle _ x z) _)); change (g.count.val:ℝ)*_≤_; exact_mod_cast he
     have hs : (separation z (g.embed p.1):ℝ) ≤ K*L := by
         rw [separation_comm]; by_contra! hn; apply hw; apply mean_radius S
         unfold L K at hn; rw [e]; exact_mod_cast hn
     refine shelter_top hα le_rfl (le_max_left ..) (max_le htℓ ?_) le_rfl
     apply le_of_mul_le_mul_left _ hL; change (separation (g.embed v) x:ℝ) ≤ T*L at h; nlinarith only[h,hz,h',hs]
 have hc (z:Site f)(r:ℝ)(y: TypeFace 1)(hz:(separation x z:ℝ) ≤ L*(5+r)): sh A α t r ((mean S).transpose (z,y))≤W/L^3:=by
    unfold sh; apply le_trans (sum_le_sum (g:=fun i=> W*mean S i (z,y)) ?_)
    · rw [← mul_sum,mean_columns]; change W*(L^3)⁻¹ ≤ _; rw [← div_eq_mul_inv]
    intro i _; rw [transpose_apply, Real.norm_of_nonneg (mean_pos ..)]; by_cases hw: mean S i (z,y)=0
    · simp [hw]
    exact mul_le_mul_of_nonneg_right (hA z r y i hw hz) (mean_pos ..)
 refine ⟨fun p=> ?_, fun p=> ?_, fun p=> ?_, fun p hp'=> ?_⟩
 · let r:= separation p.1 x; apply (hc p.1 (r/L) p.2 (by rw [separation_comm]; change (r:ℝ) ≤ _; field_simp; nlinarith only [hL])).trans
   have hx : L⁻¹ ≤ min 1 ((1+r)/L):= le_min (inv_le_one_of_one_le₀ hp) (by rw [← one_div]; gcongr; simp)
   change W/L^3≤8*W*rush L r
   refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hL.le)) (mul_nonneg (by norm_num : (0:ℝ)≤8) hW))
   field_simp; nlinarith only[hW,hp, mul_le_mul_of_nonneg_right hp hW]
 · change sh A α t 0 0 ≤_ ; rw [sh_zero]; positivity
 · apply (hc x 0 p.2 (by rw [separation_self,Nat.cast_zero]; positivity)).trans
   change W/L^3≤ 8*W*((1+(separation p.1 x:ℝ))^2/L^3); field_simp; have he:= one_le_pow₀ (show 1 ≤ 1+(separation p.1 x:ℝ) by simp) (n:=2); nlinarith only [mul_le_mul_of_nonneg_left he hW,hW]
 rcases p with ⟨q,a⟩; let r:= separation q x
 let F (i:Cover):=(mean S).transpose (wrap f i+x,a); let z:= lift (q-x); have hs:(size z:ℝ)≤4*r:=by exact_mod_cast ambient_size (q-x)
 have he:F z=(mean S).transpose (q,a):=by simp [F,z]
 have hv(y:Cover)(hy:size y≤ size z)(i:Axis): sh A α t 0 (move F i y) ≤ W*(2/L^4):=by
    unfold F move; dsimp only; erw [map_add, wrap_step, add_right_comm]
    let b:= wrap f y+x
    have hN : sh A α t 0 ((mean S).transpose (b+step i,a)-(mean S).transpose (b,a)) =
        ∑ p:Body 1 c, spot α t 0 (A p)* |mean S p (b+step i,a) - mean S p (b,a)|:= rfl
    rw [hN]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (mean_motion S a b i) hW); rw [mul_sum]; apply Finset.sum_le_sum; intro p _
    have hf : (separation x b:ℝ) ≤ 4*L := calc
       _ ≤ (size y:ℝ):=by unfold b; rw [separation_comm, separation, add_sub_cancel_right]; exact_mod_cast within_size ..
       _ ≤ (size z:ℝ) := Nat.cast_le.mpr hy
       _ ≤ _:= hs.trans (mul_le_mul_of_nonneg_left hp' (by norm_num))
    by_cases he: mean S p (b,a)=0
    · by_cases ht: mean S p (b+step i,a)=0
      · simp [he,ht]
      apply mul_le_mul_of_nonneg_right (hA _ _ _ _ ht ?_) (abs_nonneg _)
      have hh : separation b (b+step i) ≤ 1 := by rw [separation_comm,separation, add_comm b,add_sub_cancel_right]; exact pdist_step _
      have hz : (separation x (b+step i):ℝ) ≤ (separation x b:ℝ)+1 := by exact_mod_cast (separation_triangle x b (b+step i)).trans (Nat.add_le_add_left hh _)
      linarith only [hz,hf,hp]
    exact mul_le_mul_of_nonneg_right (hA _ _ _ _ he (by linarith only[hf,hp])) (abs_nonneg _)
 have hz:=walk_tiny F (R:=size z) (W*(2/L^4)) hv z le_rfl
 change sh A α t 0 ((mean S).transpose (q,a) - 0 -(mean S).transpose (x,a))≤ 8*W*((1+r)^3/L^4); rw [← he,sub_zero, show (mean S).transpose (x,a)=F 0 by simp [F]]
 refine hz.trans ((mul_le_mul_of_nonneg_right hs (show 0≤W*(2/L^4) by positivity)).trans ?_)
 field_simp; have hf : (r:ℝ) ≤ (1+r)^3:=by
   refine le_trans (le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)) ?_
   conv_lhs=> rw [← pow_one (1+(r:ℝ))];
   apply pow_le_pow_right₀ (by simp); norm_num
 nlinarith only [mul_le_mul_of_nonneg_left hf hW]
end YM.Trace.Perfect
