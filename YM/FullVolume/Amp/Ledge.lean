import YM.FullVolume.Amp.Gavel
/- closed real linear stages for Lift. Restricts to any closed sleeve and lifts operator acts for Binder Work.Function rows.Graph.B\. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset Set RG Push.AbsoluteSums Ray
open scoped Topology BigOperators Classical ContDiff
variable {X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y][NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z]
lemma hardy (R:Beam X) (S:Submodule ℝ X)(hs:IsClosed (↑S:Set X))(hX:∀ v:sun,R.arc v∈ S)(m:ℕ) : R m∈S:=by
   induction m using Nat.strong_induction_on with
   | h n ih =>
   change R n ∈ ((↑S):Set X)
   rw [← show closure (↑S:Set X)= (↑S:Set X) from hs.closure_eq]
   refine Metric.mem_closure_iff.mpr ?_; intro ε hε
   let t:=min (ε/(1+‖R‖)/2) 1; have ht:0<t:=lt_min (by positivity) zero_lt_one
   let s:sun:=⟨t, ⟨by linarith,min_le_right _ _⟩⟩
   let V:= R.arc t; let P:= ∑ k∈Finset.range n,t^k • R k; have hh:0<t^n:= pow_pos ht n
   let y:= (t^n)⁻¹ • (V-P); refine ⟨y,S.smul_mem _ (S.sub_mem (hX s) (S.sum_mem (fun i hi=> S.smul_mem _ (ih i (Finset.mem_range.mp hi))))),?_⟩
   have he:= macroH (B:=R.arc) (togg R) (n+1) (abs_le.mpr s.property) (spar R (abs_le.mpr s.property))
   unfold shell at he; rw [sum_range_succ] at he
   have hv:y-R n=(t^n)⁻¹ • (V-(P+t^n • R n)):= by unfold y; rw [smul_sub,smul_sub,smul_add,inv_smul_smul₀ hh.ne']; abel
   rw [dist_comm,dist_eq_norm,hv,norm_smul,norm_inv, Real.norm_of_nonneg hh.le,inv_mul_lt_iff₀ hh]; apply lt_of_le_of_lt he
   change ‖t‖^(n+1)*‖R‖ < _; rw [Real.norm_of_nonneg ht.le,pow_succ, mul_assoc]; apply mul_lt_mul_of_pos_left _ hh
   have h : t < ε/(1+‖R‖):= lt_of_le_of_lt (min_le_left ..) (half_lt_self (by positivity)); rw [lt_div_iff₀ (by positivity)] at h; nlinarith
lemma slate (X:Beam X) (e:Y→L[ℝ] _) (he:Isometry e) (hX:∀ v:sun,X.arc v ∈Set.range e) :∃ P:Beam Y, ‖P‖=‖X‖∧∀ s:sun, e (read _ s P)=read _ s X:=by
   have h(i:ℕ):∃ y:Y,e y=X i:= hardy X (LinearMap.range e.toLinearMap) (by exact he.isClosedEmbedding.isClosed_range) hX i
   choose f hf using h; have hx(i:ℕ): ‖f i‖=‖X i‖:= (he.norm_map_of_map_zero (map_zero _) _).symm.trans (congr_arg _ (hf i))
   let B:Beam Y:=⟨f,memℓp_gen (by simp only [hx,ENNReal.toReal_one,Real.rpow_one]; exact (paid X).summable)⟩
   refine ⟨B,?_,fun s=>?_⟩
   · rw [← (paid B).tsum_eq,← (paid X).tsum_eq];exact tsum_congr hx
   apply HasSum.unique ?_ (spar X (abs_le.mpr s.property)); have ht:=e.hasSum (spar B (abs_le.mpr s.property))
   simp_rw [map_smul,show ∀ i,e (B i)=X i from hf] at ht; exact ht
section
/- Given f a continuous-linear real map of input samples into beams, apply to analytic X without aperture loss. Coefficientwise ∑ proof. -/
variable (f:X→L[ℝ] Beam Y)(V:Beam X)
def tune (i:ℕ):= brave (ContinuousLinearMap.lsmul ℝ ℝ) (lp.single (E:=fun _:ℕ=>ℝ) 1 i 1) (f (V i))
lemma tuneN : SumBudget (fun i=> ‖tune f V i‖) (‖f‖ * ‖V‖):=by
    refine budget_mono (budget_scale (norm_nonneg f) (togg V)) (fun i=>norm_nonneg _) fun i=>?_ ; apply (braveN ..).trans; rw [lp.norm_single (by norm_num),norm_one,one_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_lsmul_le ..)).trans (f.le_opNorm _)
variable (s:sun)
lemma tuneL (i:ℕ): read Y s (tune f V i)= read Y s (f (s.val^i • V i)):=by
   unfold tune; rw [harp,map_smul,map_smul]; apply congr_arg (fun a:ℝ=>a • read Y s (f (V i))) _ ; change ∑' n:ℕ, s.val^n • lp.single _ _ _ n = _; rw [tsum_eq_single i]; simp only [lp.single_apply,Pi.single_eq_same,smul_eq_mul,mul_one]; intro j hj; simp [lp.single_apply,hj]
def song : Beam Y:= ∑' i:ℕ,tune f V i
lemma songN : ‖song f V‖≤ ‖f‖*‖V‖:= let h:= tuneN f V;(norm_tsum_le_tsum_norm h.2.1).trans h.2.2
lemma songL : read Y s (song f V)=read Y s (f (read X s V)):=by
    have h:= (read Y s).hasSum (tuneN f V).2.1.of_norm.hasSum
    have hf:= (read Y s).hasSum (f.hasSum (V.spar (abs_le.mpr s.property)))
    simp_rw [tuneL] at h; exact h.unique hf
end
end YM.FullVolume.Amp.Beam
