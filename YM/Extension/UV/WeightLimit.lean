import YM.Extension.UV.Native
/-! Visible row limits in absolute true-displacement exponent weights. Does not infer convergence
of invisible/closed-form components of the vacuum prescription.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Extension.UV.Linear
open Set Function Filter Lattice Laurent Exterior Bloch Metric Precision RG Next.Free Work.F08
open scoped Topology BigOperators
variable {α β : Type*}

def Weighted (R : ℕ→ Row α β) (τ:ℝ) (V : Row α β):=∀ a b,Tendsto (fun n=>∑' x,(weight τ x)*‖R n a b x-V a b x‖) atTop (𝓝 0)

lemma row_cauchy_of_acts {R : ℕ→Row α β} {σ C:ℝ} (h:0<σ) (hc:0 ≤ C) (hr:∀ᶠ n in atTop, (R n).strip σ C) {L : ℕ→Side} (hL:Tendsto (fun n=>(L n).val) atTop atTop)
    (a b) (x: Cover) (hv:∀ l,CauchySeq (fun n=>(R n).acts (L l) (0,a) (wrap (L l) x,b))) : CauchySeq (fun n=> R n a b x):= by
  refine Metric.cauchySeq_iff.mpr fun ε he=> ?_
  obtain ⟨l,hA⟩ := ((leaks h hc x hL).eventually_lt_const (show 0<ε/8 by positivity)).exists
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hv l) (ε/2) (by positivity)
  obtain ⟨N',hN'⟩:=eventually_atTop.mp hr
  refine ⟨max N N',fun m hm n hn=> ?_⟩
  have hy n hn := leak_bound h hc (hN' n hn) a b x L l
  have hw := hN m (by omega) n (by omega); have h1 := hy m (by omega); have h2 := hy n (by omega)
  simp only [Real.dist_eq] at hw ⊢
  -- h₁ raw Row.acts; sum of absolute errors via triangle
  linarith [abs_sub_le (R m a b x) ((R m).acts (L l) (0,a) (wrap (L l) x,b)) (R n a b x),
    abs_sub_le ((R m).acts (L l) (0,a) (wrap (L l) x,b)) ((R n).acts (L l) (0,a) (wrap (L l) x,b)) (R n a b x),abs_sub_comm (R m a b x) ((R m).acts (L l) (0,a) (wrap (L l) x,b))]

lemma row_visible {R : ℕ→Row α β} {σ C:ℝ} (h:0<σ) (hc:0 ≤ C) (hr:∀ᶠ n in atTop, (R n).strip σ C) {L : ℕ→Side} (hL:Tendsto (fun n=>(L n).val) atTop atTop)
    (hX:∀ l,CauchySeq (fun n=>(R n).acts (L l))) : ∃ V, (∀ a b x, ‖V a b x‖≤ C*weight (-σ) x) ∧ ∀ τ:ℝ, τ<σ → Weighted R τ V:= by
  have hp a b x : CauchySeq (fun n=>R n a b x):=row_cauchy_of_acts h hc hr hL a b x fun l=>by
     obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete (hX l)
     exact Tendsto.cauchySeq (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv _) _)
  choose V hV using fun a b (x:Cover) => cauchySeq_tendsto_of_complete (hp a b x)
  have hM a b x : ‖V a b x‖ ≤ C*weight (-σ) x:= le_of_tendsto (hV a b x).norm (hr.mono fun n hn=>priced_row_point h hn _ _ _)
  refine ⟨V,hM,fun τ hτ a b=> ?_⟩
  have ht := (weight_summable (by linarith : 0 < σ-τ)).mul_left (2*C)
  simp only [neg_sub] at ht
  have hb : ∀ᶠ n in atTop, ∀ x, ‖weight τ x * ‖R n a b x-V a b x‖‖ ≤ 2*C*weight (τ-σ) x := by
    filter_upwards [hr] with n hn x
    have h' := priced_row_point h hn a b x
    have hy := hM a b x
    have hu : 0≤ C*weight (-σ) x := by have := weight_pos (-σ) x; positivity
    rw [Real.norm_of_nonneg (by have := weight_pos τ x; positivity)]
    calc
      _ ≤ weight τ x*(2*C*weight (-σ) x) := (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add h' hy)) (weight_pos _ _).le).trans_eq (by ring)
      _ = _:= by unfold weight; rw [sub_mul,sub_eq_add_neg, Real.exp_add,neg_mul]; ring
  have hx x : Tendsto (fun n=>weight τ x * ‖R n a b x - V a b x‖) atTop (𝓝 0):= by
    simpa only [sub_self,norm_zero,mul_zero] using (((hV a b x).sub_const (V a b x)).norm.const_mul (weight τ x))
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence ht hx hb
end YM.Extension.UV.Linear
