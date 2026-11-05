import YM.Extension.UV.Station.Drives
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.StationaryData
open RG Filter Set Function
open scoped Topology BigOperators Classical NNReal
variable {κ : Type*}
namespace tight
def mass (f:κ→ℝ) σ (l:κ→ℕ) C:= SumBudget (fun i=> |f i| * Real.exp (σ*l i)) C
def read (f:κ→ℝ) σ (l:κ→ℕ) := ∑' i, |f i| * Real.exp (σ*l i)
variable {l:κ→ℕ} {C σ τ : ℝ} {F:ℕ→κ→ℝ} {x:κ→ℝ}
    (h : ∀ᶠ n in atTop,mass (F n) σ l C) (hf:Tendsto F atTop (𝓝 x))
lemma sub {f g:κ→ℝ} (hf:mass f σ l C) (hg:mass g σ l C): (mass (f-g) σ l (C+C)):= by
   let a i := |f i| * Real.exp (σ*l i)
   let b i := |g i| * Real.exp (σ*l i)
   let d i := |(f-g) i| * Real.exp (σ*l i)
   have hd i : d i ≤ a i + b i := by simpa only [d,a,b,Pi.sub_apply,add_mul] using mul_le_mul_of_nonneg_right (abs_sub _ _) (Real.exp_nonneg (σ*l i))
   have hn i : 0≤d i:=by unfold d; positivity
   have hh:=Summable.of_nonneg_of_le hn hd (hf.2.1.add hg.2.1)
   refine ⟨hn,hh,(hh.tsum_le_tsum hd (hf.2.1.add hg.2.1)).trans ?_⟩
   rw [hf.2.1.tsum_add hg.2.1]; gcongr <;> first | exact hf.2.2 | exact hg.2.2
include h hf in
lemma mass_closed : mass x σ l C:= by
   have he (s:Finset κ): Tendsto (fun n=>∑ i∈s, |F n i| * Real.exp (σ*l i)) atTop ((𝓝 (∑ i∈s,|x i| * Real.exp (σ*l i)))) := tendsto_finsetSum s (fun i hi=> (continuous_abs.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hf) i)).mul_const _)
   have he s := le_of_tendsto (he s) (h.mono fun n ht => (ht.2.1.sum_le_tsum s (fun i hi=> ht.1 _)).trans ht.2.2)
   have hp (i:κ): 0≤ |x i| *Real.exp (σ*l i) := by positivity
   have hv:= summable_of_sum_le hp he
   exact ⟨hp,hv,hv.tsum_le_of_sum_le he⟩
include hf in
lemma prefix_cheap (s:Finset κ) : Tendsto (fun n=>∑ i∈s, |F n i-x i| * Real.exp (τ*l i)) atTop (𝓝 0):= by
  suffices he: Tendsto _ atTop (𝓝 (∑ x∈s,(0:ℝ))) from by simp only [Finset.sum_const_zero] at he;exact he
  apply tendsto_finsetSum; intro i _
  rw [show (0:ℝ)=(0:ℝ)*Real.exp (τ*l i) by simp]
  apply Tendsto.mul_const
  convert continuous_abs.continuousAt.tendsto.comp (show Tendsto (fun n=>F n i-x i) _ (𝓝 (0:ℝ)) by simpa only [sub_self] using ((tendsto_pi_nhds.mp hf) i).sub_const (x i)) using 1
  all_goals simp [Function.comp_def]
lemma tail_control (f:κ→ℝ) (hσ:τ≤σ) (hf:mass f σ l C) (M:ℕ) {s : Finset κ} (hs:∀ i, i ∉s → M≤l i): read f τ l ≤ (∑ i∈s, |f i| * Real.exp (τ*l i)) + Real.exp (-((σ-τ)*M))*C := by
   let d (r:ℝ) i:= |f i| * Real.exp (r*l i)
   have hlt i : d τ i ≤ d σ i:= by unfold d; gcongr
   have hδ : Summable (d τ):=Summable.of_nonneg_of_le (fun _=>by unfold d; positivity) hlt hf.2.1
   apply Summable.tsum_le_of_sum_le hδ; intro U
   let T:= U \ s; have e:U=(U ∩ s)∪T := by ext i; by_cases h:i∈s <;> simp [T,h]
   change (∑ i ∈ U, d τ i) ≤ (∑ i∈ s, d τ i) + _
   rw [e, Finset.sum_union (show Disjoint (U∩s) T from Finset.disjoint_left.mpr fun x hx hT=> (Finset.mem_sdiff.mp hT).2 (Finset.mem_inter.mp hx).2)]
   let z := Real.exp (-((σ-τ)*M))
   apply add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right) (fun _ _ _=>by unfold d; positivity))
   calc
     (∑ i∈T,d τ i) ≤ ∑ i∈T, z*d σ i := by
        refine Finset.sum_le_sum fun i hi=> ?_
        dsimp only [d,z]
        conv => rhs; rw [mul_left_comm,← Real.exp_add]
        gcongr
        have he1:=sub_nonneg.mpr hσ; have he2 : 0≤(l i:ℝ)-(M:ℝ):=sub_nonneg.mpr (by exact_mod_cast hs i (Finset.mem_sdiff.mp hi|>.2))
        nlinarith [mul_nonneg he1 he2]
     _ = z *∑ i∈T,d σ i := by rw [Finset.mul_sum]
     _ ≤ z*C := mul_le_mul_of_nonneg_left ((hf.2.1.sum_le_tsum _ fun i _=>by unfold mass at hf; apply hf.1).trans hf.2.2) (Real.exp_nonneg _)

include h hf in
lemma strict_limit (hv:∀ M:ℕ, Set.Finite {i|l i≤M}) (he:τ<σ): Tendsto (fun n=>read (F n-x) τ l) atTop (𝓝 0):= by
   have h₀:= mass_closed h hf
   have hi : Tendsto (fun M:ℕ => Real.exp (-((σ-τ)*(M:ℝ)))*(C+C)) atTop (𝓝 0):=by
     simpa only [neg_mul,mul_comm _ (C+C),mul_zero,Function.comp_def] using (tendsto_const_nhds (x:=C+C)).mul (Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (r:= -(σ-τ)) (by linarith)))) -- mul_comm use replace
   apply Metric.tendsto_atTop.mpr; intro ε hε
   obtain ⟨b,hb⟩:= eventually_atTop.mp (hi.eventually (gt_mem_nhds (half_pos hε)))
   let s := (hv b).toFinset
   obtain ⟨k,hk⟩:= eventually_atTop.mp ((prefix_cheap hf (τ:=τ) s).eventually (gt_mem_nhds (half_pos hε)))
   obtain ⟨j,hj⟩:=eventually_atTop.mp h
   refine ⟨max k j,fun n hn=> ?_⟩
   rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (by unfold read; exact tsum_nonneg fun _=>by positivity)]
   have hh:= tail_control (F n-x) he.le (sub (hj n (by omega)) h₀) b (s:=s) (fun i hi=> (not_le.mp (by simpa only [s,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using hi : ¬ l i≤b)).le)
   exact hh.trans_lt ((add_lt_add (hk n (by omega)) (hb b le_rfl)).trans_eq (add_halves ε))
end tight
end YM.Extension.UV.StationaryData
