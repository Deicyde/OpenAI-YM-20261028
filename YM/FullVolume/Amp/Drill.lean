import YM.FullVolume.Amp.Pin
/-! Germ statement with fixed price: around every base near origin x all lines have true series. Coefficients mint uniquely. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y I : Type*} [DecidableEq I][SeminormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable (s:Finset I)(u:I→X){f:X→Y}{x:X}{c p r k:ℝ}{n j:ℕ}{P:ℕ→Y}
structure Often (p:ℝ) (f:X→Y)(x:X)(r c:ℝ):Prop where
   width:0<r
   lens:∀ᶠ x' in 𝓝 x,∀ y, ‖y‖≤ r → Scout p (fun t:ℝ=> f (x'+t • y)) c
variable {B:ℝ→Y}
def shell (P:ℕ→Y) (n:ℕ)(t:ℝ):=∑ j∈range n,t^j • P j
def Tip (P:ℕ→Y) (B:ℝ→Y):Prop:=∀ n:ℕ,(fun t=> B t-shell P n t)=O[𝓝 (0:ℝ)]fun t=> t^n
lemma pace (hp: Tip P B)(hk:B=O[𝓝 (0:ℝ)]fun t=>t^n):j<n→ P j=0:=by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have hz t:shell P (j+1) t=t^j • P j:= by
      unfold shell; rw [sum_range_succ,sum_eq_zero,zero_add]; intro k hk; rw [ih _ (mem_range.mp hk) (lt_trans (mem_range.mp hk) hj),smul_zero]
    have h₀:= ((hk.trans_isLittleO (isLittleO_pow_pow (𝕜:=ℝ) hj)).sub ((hp (j+1)).trans_isLittleO (isLittleO_pow_pow (𝕜:=ℝ) (Nat.lt_succ_self j))))
    by_contra hh; have he:=norm_pos_iff.mpr hh
    have h_t:= h₀.def (half_pos he)
    simp_rw [hz,sub_sub_cancel,norm_smul] at h_t
    obtain ⟨t,ht,h⟩:= ((h_t.filter_mono (show 𝓝[>] (0:ℝ) ≤ _ from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
    have ht':0<t:=h; have he:= norm_pos_iff.mpr (pow_ne_zero j ht'.ne'); nlinarith
lemma sole {P':ℕ→Y}(h:Tip P B)(hv:Tip P' B):P=P':=by
  have ht: Tip (P-P') (0:ℝ→Y):=by
    intro k; have hh:= (h k).sub (hv k); refine hh.congr_left fun x=>?_; simp [Pi.sub_apply, shell, smul_sub,sum_sub_distrib]
  funext j; exact sub_eq_zero.mp (pace ht (n:=j+1) (isBigO_zero ..) j.lt_succ_self)
lemma macroH (h:SumBudget (fun i=> ‖P i‖) c)(i:ℕ) (hv:‖k‖≤1)(he : HasSum (fun j:ℕ=> k^j • P j) (B k)): ‖B k-shell P i k‖≤ ‖k‖^i*c:=by
   have hz: SumBudget (fun j:ℕ=> ‖k^(j+i) • P (j+i)‖) (‖k‖^i*c):=by
     have hg:= budget_scale (pow_nonneg (norm_nonneg k) i) (budget_pull (fun j:ℕ=>j+i) (fun _ _=>Nat.add_right_cancel) h)
     exact budget_mono hg (fun _=>norm_nonneg _) fun j=> by rw [norm_smul,norm_pow,pow_add]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) hv)) (norm_nonneg _)
   unfold shell; rw [← he.tsum_eq,← he.summable.sum_add_tsum_nat_add i, add_sub_cancel_left]; exact (norm_tsum_le_tsum_norm hz.2.1).trans hz.2.2
lemma sprite (a:ℝ): ∀ᶠ t in 𝓝 (0:ℝ), |a*t| ≤1:= by
  have h:(fun t:ℝ=>|a*t|) ∘ id =fun t=>|a*t|:=rfl
  exact (show ∀ᶠ t in 𝓝 (0:ℝ), |a*t|<1 from (Continuous.tendsto (show Continuous fun t:ℝ=>|a*t| by fun_prop) 0).eventually (gt_mem_nhds (show |a*0|<1 by simp))).mono fun _ h=> h.le
lemma signpost (a:ℝ)(h:SumBudget (fun i=> ‖P i‖) c)(hb:∀ᶠ s in 𝓝 (0:ℝ),HasSum (fun j:ℕ=> (a*s)^j • P j) (B s)): Tip (fun i=>a^i • P i) B:=by
   intro n; refine IsBigO.of_bound (‖a‖^n*c) ?_
   filter_upwards [hb,sprite a] with t ht hy
   rw [shell]; change ‖_‖≤_*‖t^n‖; simp_rw [smul_smul, ← mul_pow,mul_comm t]
   exact (macroH (B:=fun _=>B t) h n hy ht).trans_eq (by rw [norm_pow,norm_mul,mul_pow]; ring)
variable (L : Often p f x r c)
include L
namespace Often
lemma looking (y:X)(hv:‖y‖≤r):Scout p (fun t:ℝ=> f (x+t • y)) c:= mem_of_mem_nhds L.lens _ hv
lemma pays : 1≤p∧ 0≤c:= let h:= L.looking 0 (by rw [norm_zero]; exact L.width.le); ⟨h.ray,h.nonneg⟩
omit L
-- polynomial cancellation basis
lemma cold (hj:j<n): (∑ i∈range (n+1),hat n i*(i:ℝ)^j)=0:= by
  have hp:= face (X:=ℝ) (Y:=ℝ) (f:=fun t:ℝ=> t^j) (x:=(0:ℝ))
  specialize hp 1 n; simpa [fwdDiff_iter_pow_eq_zero_of_lt (R:=ℝ) hj,smul_eq_mul] using hp.symm
include L
-- from lines varying centers. Pure ∆^n f at t w
lemma reveal (u z:X)(n:ℕ): (fun (t:ℝ)=> (fwdDiff (t • u))^[n] f (x+t • z)) =O[𝓝 (0:ℝ)] fun t=> t^n:=by
   let b:ℝ:= (‖u‖+1)/r; have hu:0<r:= L.width; have hb:0<b:=by unfold b; positivity
   let y: X:= b⁻¹ • u; have hV: ‖y‖≤ r:= by
     unfold y; rw [norm_smul,norm_inv,Real.norm_of_nonneg hb.le, inv_mul_le_iff₀ hb]; unfold b; rw [div_mul_cancel₀ _ hu.ne']; linarith
   have hz: ∀ᶠ t in 𝓝 (0:ℝ),Scout 1 (fun i:ℝ=>f (x+t • z+i • y)) c:= ((show Tendsto (fun t:ℝ=>x+t • z) (𝓝 (0:ℝ)) (𝓝 x) from (by simpa using! ((continuous_const.add (continuous_id'.smul continuous_const)): Continuous (fun t:ℝ=>x+t • z)).tendsto 0)).eventually L.lens).mono fun t h=> (h y hV).lessen le_rfl L.pays.1
   let S:= range (n+1); refine IsBigO.of_bound (∑ i∈ S, ‖hat n i‖*(‖(i:ℝ)*b‖^n*c)) ?_
   filter_upwards [hz,(eventually_all_finset S).mpr (fun i _=>sprite ((i:ℝ)*b))] with t ht h
   obtain ⟨_,P,hP,hz⟩ := ht
   let H i := ((i:ℕ):ℝ)*b*t
   let v:=x+t • z
   have hi i: v+(i:ℕ) • t • u=v+H i • y:= by unfold H y; rw [←Nat.cast_smul_eq_nsmul ℝ,smul_smul,smul_smul]; field_simp
   have hc: (∑ i∈ S,hat n i • shell P n (H i))=0:= by
     unfold shell; simp_rw [smul_sum]; rw [sum_comm]; apply sum_eq_zero; intro j hj
     unfold H; simp_rw [smul_smul,mul_pow,←mul_assoc]; unfold S; rw [←sum_smul,← sum_mul, ← sum_mul, cold (mem_range.mp hj),zero_mul,zero_mul,zero_smul]
     -- simp [smul_smul,pow_mul]
   change ‖_‖≤ _*‖t^n‖; rw [face]
   let Y i : Y:= f (v+H i • y)
   simp_rw [Nat.cast_smul_eq_nsmul]
   change ‖∑ j∈ S, hat n j • f (v+j • t • u)‖ ≤ _
   simp_rw [hi]; conv_lhs=> arg 1; rw [← sub_zero (∑ i∈S,_),←hc]
   simp only [←sum_sub_distrib,← smul_sub]; rw [sum_mul]; refine (norm_sum_le ..).trans ?_; apply sum_le_sum; intro i hi; rw [norm_smul]
   have ht':= h i hi; have hh:=hz (H i) (abs_le.mp ht'); simp_rw [div_one] at hh; exact (mul_le_mul_of_nonneg_left (macroH (B:=fun _=>Y i) hP n ht' hh) (norm_nonneg _)).trans_eq (by simp only [norm_mul,mul_pow,norm_pow]; ring)
end Often
end YM.FullVolume.Amp
