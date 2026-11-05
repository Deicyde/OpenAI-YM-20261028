import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.LinkBounds

/-! Pure Taylor helpers for leading-degree transport. -/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Jets
open Filter Function Set Precision Finset
open scoped Topology ContDiff BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma drop {f : ℝ → ℝ} {n k : ℕ} (hn : k < n) {a : ℝ} (h : Tendsto (fun t => f t / t^n) (𝓝[≠] 0) (𝓝 a)) :
    Tendsto (fun t => f t / t^k) (𝓝[≠] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t^(n-k)) (𝓝[≠] 0) (𝓝 0) := by simpa only [id_eq, zero_pow (show n-k ≠ 0 by omega)] using
      ((tendsto_id (x:=𝓝 (0:ℝ))).mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))).pow (n-k)
  have hh := h.mul ht; rw [mul_zero] at hh
  refine hh.congr' ?_; filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 from self_mem_nhdsWithin] with t ht
  rw [show t^n = t^(n-k)*t^k by rw [← pow_add, Nat.sub_add_cancel hn.le]]; field_simp

private lemma little {d : ℕ} {f : ℝ → ℝ} (h : ContDiffAt ℝ d f 0) (hf : Tendsto (fun t => f t / t ^ d) (𝓝[≠] 0) (𝓝 0)) :
    ∀ i ≤ d, iteratedDeriv i f 0 = 0 := by
  intro i hi
  induction i using Nat.strong_induction_on with | h i ih
  have ht := (h.of_le (Nat.cast_le.mpr hi)).contDiffOn (m:=(i:WithTop ℕ∞)) le_rfl (by simp)
  obtain ⟨s,hs,hh⟩ := ht
  obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp hs
  let I := Metric.ball (0:ℝ) r
  have hz : (0:ℝ) ∈ I := Metric.mem_ball_self hr
  have hw (x : ℝ) : taylorWithinEval f i I 0 x = (i.factorial:ℝ)⁻¹ * x^i * iteratedDeriv i f 0 := by
    have he (j : ℕ) : iteratedDerivWithin j f I 0 = iteratedDeriv j f 0 := iteratedDerivWithin_of_isOpen Metric.isOpen_ball hz
    rw [taylor_within_apply,Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, he]
    · simp
    intro b hb
    have hv := Finset.mem_range.mp hb
    rw [he,ih b hv (hv.le.trans hi),smul_zero]
  have hl := Real.taylor_tendsto (n:=i) (convex_ball (0:ℝ) r) hz (hh.mono hb)
  unfold I at hw; simp_rw [hw,sub_zero, nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds hz)] at hl
  have hq : Tendsto (fun t => f t / t ^ i) (𝓝[≠] 0) (𝓝 0) := by
    rcases lt_or_eq_of_le hi with h|h
    · exact drop h hf
    exact h.symm ▸ hf
  have hu := hq.sub (hl.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))); rw [sub_zero] at hu
  have hu' : Tendsto (fun _ : ℝ => (i.factorial:ℝ)⁻¹ * iteratedDeriv i f 0) (𝓝[≠] 0) (𝓝 0) := by
    refine hu.congr' ?_; filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 from self_mem_nhdsWithin] with t ht; field_simp; ring
  have := tendsto_nhds_unique tendsto_const_nhds hu'
  exact (mul_eq_zero.mp this).resolve_left (by positivity)

theorem negligible {d : ℕ} {f : E → ℝ} (hf : ContDiffAt ℝ d f 0)
    (lim : ∀ x : E, Tendsto (fun t : ℝ => f (t • x) / t ^ d) (𝓝[≠] 0) (𝓝 0)) :
    ∀ j ≤ d, iteratedFDeriv ℝ j f 0 = 0 := by
  have he (x : E) : ContDiffAt ℝ d (fun t : ℝ => f (t • x)) 0 :=
    (show ContDiffAt ℝ d f ((0:ℝ) • x) by simpa using hf).comp 0 (by fun_prop)
  have h : Work.G05.blockTaylor d f = 0 := by
    funext x; rw [Work.G05.blockTaylor,Finset.sum_apply]; refine sum_eq_zero fun j hj => ?_
    have hj' := Nat.le_of_lt_succ (mem_range.mp hj)
    have hx := little (he x) (lim x) j hj'
    rw [Next.Foundations.iteratedDeriv_on_line (hf.of_le (Nat.cast_le.mpr hj'))] at hx
    unfold Tensor.diagonal Tensor.coeff; rw [smul_apply, show iteratedFDeriv ℝ j f 0 (fun _ => x)=(0:ℝ) from hx, smul_zero]
  intro j hj; rw [← Work.G05.blockTaylor_jets hf j hj,h]
  cases j with
  | zero => ext1; rw [iteratedFDeriv_zero_eq_comp]; rfl
  | succ j => exact congr_fun (iteratedFDeriv_const_of_ne (by omega : j+1 ≠ 0) (0:ℝ)) _

theorem leading {d : ℕ} {f g : E → ℝ} {Q : E → ℝ} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0)
    (lf : ∀ x, Tendsto (fun t : ℝ => f (t • x) / t ^ d) (𝓝[≠] 0) (𝓝 (Q x)))
    (lg : ∀ x, Tendsto (fun t : ℝ => g (t • x) / t ^ d) (𝓝[≠] 0) (𝓝 (Q x))) : ∀ j ≤ d, SameJet j f g := by
  have he := negligible (d:=d) (f:=f-g) (hf.sub hg |>.of_le le_top) fun x => (by simpa [sub_div] using (lf x).sub (lg x))
  intro j hj; refine ⟨hf,hg,sub_eq_zero.mp ?_⟩
  rw [← iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top), he j hj]

lemma length_parts {n : ℕ} (c : OrderedFinpartition n) (h : c.length = n) : ∀ i, c.partSize i = 1 := by
  have hb := Fintype.card_le_of_injective _ c.emb_injective
  rw [Fintype.card_sigma,Fintype.card_fin] at hb; simp_rw [Fintype.card_fin] at hb
  intro i; by_contra! he
  have := Finset.sum_lt_sum (s:=Finset.univ) (f:=fun _ => 1) (g:=fun j => c.partSize j) (fun j _ => c.partSize_pos j)
    ⟨i,mem_univ i,(lt_of_le_of_ne (c.partSize_pos i) he.symm)⟩
  simp [h] at this
  omega

lemma tangent {d : ℕ} {f : F → ℝ} {g : E → F} (h : ContDiffAt ℝ d f 0) (hg : ContDiffAt ℝ d g 0) (hz : g 0 = 0)
    (hv : ∀ j < d, iteratedFDeriv ℝ j f 0 = 0) : ∀ j ≤ d,
    iteratedFDeriv ℝ j (f ∘ g) 0 = iteratedFDeriv ℝ j (f ∘ (fderiv ℝ g 0)) 0 := by
  intro j hj
  let A := fderiv ℝ g 0
  have hy : (⇑A) 0 = 0 := A.map_zero
  rw [iteratedFDeriv_comp (hz.symm ▸ h) hg (Nat.cast_le.mpr hj), iteratedFDeriv_comp (hy.symm ▸ h) A.contDiff.contDiffAt (Nat.cast_le.mpr hj),hz,hy]
  apply sum_congr rfl; intro c _
  ext x
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
  rcases lt_or_eq_of_le c.length_le with h'|h'
  · rw [hv c.length (h'.trans_le hj)]; rfl
  congr! 1 with i
  funext i
  have ht {n : ℕ} (hn : n=1) (u : Fin n → E) : iteratedFDeriv ℝ n g 0 u = iteratedFDeriv ℝ n (⇑A) 0 u := by
    subst n; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,A.fderiv]
  exact ht (length_parts c h' i) _

end YM.Extra.Iteration.Jets
