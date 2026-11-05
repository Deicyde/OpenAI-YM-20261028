import YM.FullVolume.Ray.Gain
import Mathlib.Analysis.SpecialFunctions.Exponential
/-! Scout algebra. real line aperture. Absolute costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray.Scout
open Filter Function RG Push.AbsoluteSums Finset
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {a v p c d : ℝ} {f g : ℝ → ℝ} {s:ℕ→ℝ}
lemma multiplies (h:Scout p f c) (hv : Scout p g d): Scout p (fun i=>f i*g i) (c*d):=by
  obtain ⟨hp,b,hb,hk⟩:=h; obtain ⟨r,hr,he⟩:=hv.scored
  let F (b r:ℕ→ℝ) n:=∑ x∈antidiagonal (n:ℕ),b x.1*r x.2
  have hs (b r:ℕ→ℝ) (h:Summable (fun i=> ‖b i‖)) (hv:Summable (fun i=>‖r i‖)):HasSum (F b r) ((∑' i,b i)*∑' i,r i):=by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h hv]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm h hv).of_norm.hasSum
  refine ⟨hp,F b r,?_,fun i hi=>?_⟩
  · let u n:= ‖b n‖; let v n:= ‖r n‖; have hu:0≤u:=fun _=>norm_nonneg _; have ht:0≤v:=fun _=>norm_nonneg _
    have hP := hs u v ((show Summable u from hb.2.1).norm) ((show Summable v from hr.2.1).norm)
    have hx: SumBudget (F u v) (c*d):= ⟨fun n=> Finset.sum_nonneg (fun i _=> mul_nonneg (hu _) (ht _)), hP.summable, hP.tsum_eq.trans_le (mul_le_mul hb.2.2 hr.2.2 (tsum_nonneg ht) ((tsum_nonneg (g:=u) hu).trans hb.2.2))⟩
    refine budget_mono hx (fun i=>norm_nonneg _) (fun i=>(norm_sum_le ..).trans ?_)
    unfold F; exact (Finset.sum_le_sum fun x _=> (norm_mul ..).le)
  let z:=i/p
  let u n:= z^n • b n; let v n:= z^n • r n
  have hz: ‖z‖≤1:=ratio_le hp hi
  have h:=hs u v (at_flight z hz hb).2.1 (at_flight z hz hr).2.1
  change HasSum (fun n=> z^n • _) (f i*g i); rw [← (show HasSum u (f i) from hk _ hi).tsum_eq, ← (show HasSum v (g i) from he _ hi).tsum_eq]
  refine h.congr_fun fun n=> ?_; simp only [smul_eq_mul,F, Finset.mul_sum]; apply sum_congr rfl; intro j hj
  dsimp only [u,v,smul_eq_mul]; rw [← mem_antidiagonal.mp hj,pow_add]; ring
lemma power (h:Scout p f c) (k:ℕ):Scout p (fun t=> f t^k) (c^k):=by
  induction k with
  | zero => simpa using still h.ray (1:ℝ)
  | succ k ih => simpa only [pow_succ] using ih.multiplies h
section infinite
variable {ι : Type*} {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma infinite {a:ι→ℝ} {g:ι→ℝ→E} (h:SumBudget a c) (hp:1≤p) (hv:∀ i,Scout p (g i) (a i)): Scout p (fun t=>∑' i,g i t) c:=by
  choose f b hf using fun i=>(hv i).scored
  let t n:=∑' i, f i n
  let F(i:ι × ℕ):= ‖f i.1 i.2‖; have hF:0≤ F:=fun _=> norm_nonneg _
  let u i:=∑' n,F (i,n); have hu:0≤u:=fun i=> tsum_nonneg fun n=> hF _
  have ha := budget_mono h (f:=a) (g:=u) hu (fun i=>(b i).2.2)
  have hK : Summable F:= (summable_prod_of_nonneg hF).2 ⟨fun i=>(b i).2.1,ha.2.1⟩
  let R:=Equiv.prodComm ℕ ι; let v : ℕ×ι→ℝ:=F ∘ R; have hU:Summable v:= R.summable_iff.2 hK; have ht i:=hU.prod_factor i
  have he n: ‖t n‖≤ ∑' i, v (n,i):= norm_tsum_le_tsum_norm (ht n)
  refine ⟨hp,t,budget_mono (budget_loosen ?_ (show ∑' i,u i≤c from ha.2.2)) (fun n=>norm_nonneg _) he,?_⟩
  · exact ⟨fun n=> tsum_nonneg (fun i=> hF _), hU.prod, le_of_eq (hU.tsum_prod.symm.trans ((R.tsum_eq F).trans hK.tsum_prod))⟩
  intro x hx
  let q (i:ℕ×ι):= (x/p)^i.1 • f i.2 i.1
  have hq:Summable q:= hU.of_norm_bounded fun i=> by
    unfold q; rw [norm_smul]; apply mul_le_of_le_one_left (norm_nonneg _); rw [Real.norm_eq_abs, abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ratio_le hp hx) (n:=i.fst) -- simp
  have hL:= R.symm.summable_iff (f:=q)|>.2 hq
  have hh:∑' i:ℕ × ι, q i=∑' i,g i x:= by
    refine Eq.trans (R.symm.tsum_eq q).symm (hL.tsum_prod.trans ?_); apply tsum_congr; intro i; exact (hf i x hx).tsum_eq
  rw [hq.tsum_prod] at hh; rw [← hh]
  apply hq.prod.hasSum.congr_fun; intro i; unfold q t; dsimp only
  rw [Summable.tsum_const_smul ..]; exact (ht _).of_norm
end infinite

lemma blaze_bill (x : ℝ) : ∑' i:ℕ,x^(i+1) / ((i+1).factorial:ℝ) = Real.exp x-1:=by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]; dsimp only
  rw [← Summable.sum_add_tsum_nat_add 1 (Real.summable_pow_div_factorial x)]; simp
lemma burn (h:Scout p f c): Scout p (fun i=> Real.exp (f i)-1) (Real.exp c -1):=by
  have hr:=h.nonneg; let a(i:ℕ):= c^(i+1) / ((i+1).factorial:ℝ); let g (i:ℕ) t:= f t^(i+1) / ((i+1).factorial:ℝ)
  refine (infinite (ι:=ℕ) (g:=g) (a:=a) ⟨fun i=>by unfold a; positivity,(summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial _), (blaze_bill _).le⟩ h.ray ?_).replace fun i _=>blaze_bill _
  intro i; let q:= ((i+1).factorial:ℝ)⁻¹; have hp := (h.power (i+1)).scale q; refine (hp.enlarged ?_).replace (fun i hi=> ?_)
  · change _ ≤ a i; unfold q a; rw [norm_inv,Real.norm_of_nonneg (Nat.cast_nonneg _) ,div_eq_mul_inv,mul_comm]
  unfold q g; dsimp only; rw [smul_eq_mul,div_eq_mul_inv,mul_comm]
lemma ignite (h:Scout p f c):Scout p (fun i=> Real.exp (f i)) (Real.exp c):=by
  have hp := (h.burn).pair (still h.ray (1:ℝ)); simpa using hp
end YM.FullVolume.Ray.Scout
