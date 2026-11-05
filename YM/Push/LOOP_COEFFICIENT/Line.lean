import YM.Push.LOOP_COEFFICIENT.Pullback




/-!
# Complex jets at zero momentum

Continue identities, *not* finite-torus interpolants. Ordered/isolated-zeros
trick as in BOUNDARY. Real counting values versus complex line calculus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Bloch Complex Set Metric
open scoped Topology ContDiff BigOperators

lemma continue_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {s : Set Momentum} {f g : Momentum → F} (hs : Convex ℝ s) (ho : IsOpen s)
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s)
    (h : ∀ p∈s, star p = p → f p = g p) (z : Momentum) (hz : z∈s)
    (hR : (fun i => ((z i).re:ℂ)) ∈ s) : f z = g z := by
  let W (t : ℂ) : Momentum := fun i => ((z i).re:ℂ)+t*((z i).im:ℂ)
  have hw : ContDiff ℂ ω W := by unfold W; fun_prop
  let U := W ⁻¹' s
  have hU : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change W (a • x + b • y) ∈ s
    rw [show W (a • x+b • y) = a • W x+b • W y from ?_]
    · exact hs hx hy ha hb hab
    funext i; dsimp [W, real_smul]
    have hab' : (a:ℂ) + b = 1 := by exact_mod_cast hab
    linear_combination - ((z i).re:ℂ) * hab'
  have hO := ho.preimage hw.continuous
  have ht : (0:ℂ) ∈ U := by simpa [U,W] using hR
  have hI : W I = z := by ext1 i; dsimp [W]; rw [mul_comm, re_add_im]
  have hT : Tendsto ((↑):ℝ→ℂ) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    filter_upwards [self_mem_nhdsWithin] with t ht; simpa using (mem_Ioi.mp ht).ne'
  have he := (hf.comp (hw.analyticOnNhd) (mapsTo_preimage W s)).eqOn_of_preconnected_of_frequently_eq
    (hg.comp (hw.analyticOnNhd) (mapsTo_preimage W s)) hU.isPreconnected ht (by
      intro hn; obtain ⟨t,h₁,h₂⟩ := ((hT.eventually hn).and ((hT.mono_right nhdsWithin_le_nhds).eventually (hO.mem_nhds ht))).exists
      exact h₁ (h _ h₂ (by ext1; simp [W]))) (show I ∈ U from (show W I ∈ s by rwa [hI]))
  simpa [comp_def,hI] using he

lemma germ_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f g : Momentum → F} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : ∀ᶠ p in 𝓝 0, star p = p → f p = g p) : f =ᶠ[𝓝 0] g := by
  obtain ⟨r,hr,he⟩ := Metric.nhds_basis_ball.mem_iff.mp ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and h)
  filter_upwards [ball_mem_nhds (0:Momentum) hr] with p hp
  refine continue_real (convex_ball 0 r) isOpen_ball (fun x hx => (he hx).1.1) (fun x hx => (he hx).1.2) (fun x hx => (he hx).2) p hp ?_
  simp only [mem_ball,dist_zero_right] at hp ⊢
  refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun i => ?_) hp
  exact (by simpa using (abs_re_le_norm (p i)).trans (norm_le_pi_norm p i))

/-- Momentum derivative along a complex line (not divided by factorial).
Keep scalar to avoid accidental norm instances for matrices. -/
def lineD (f : Momentum → ℂ) (p : Momentum) (n : ℕ) := iteratedDeriv n (fun t : ℂ => f (t • p)) 0

def Below (f : Momentum → ℂ) (p : Momentum) (n : ℕ) : Prop := ∀ i < n,lineD f p i = 0

variable {f g : Momentum → ℂ} {n a b : ℕ} {p : Momentum}

@[simp] lemma line_zero : lineD f p 0 = f 0 := by simp [lineD]
@[simp] lemma line_vac (p n) : lineD (fun _ => 0) p n = 0 := by simp [lineD]
lemma line_neg (f : Momentum → ℂ) (p n) : lineD f (-p) n = (-1)^n * lineD f p n := by
  simpa [lineD, neg_smul] using iteratedDeriv_comp_neg n (fun t : ℂ => f (t • p)) 0
lemma tendsto_ray (p : Momentum) : Tendsto (fun t : ℂ => t • p) (𝓝 0) (𝓝 0) := by
  simpa only [zero_smul] using ((show Continuous (fun t : ℂ => t • p) by fun_prop).tendsto 0)
lemma line_congr (h : f =ᶠ[𝓝 0] g) (p n) : lineD f p n = lineD g p n := by
  apply EventuallyEq.iteratedDeriv_eq
  exact (tendsto_ray p).eventually h

lemma below_zero : Below f p 0 := by simp [Below]
lemma below_one (h : f 0 = 0) : Below f p 1 := by simpa [Below] using h
lemma below_succ : Below f p (n+1) ↔ Below f p n ∧ lineD f p n = 0 := by unfold Below; exact ⟨fun h => ⟨fun _ hi => h _ (by omega),h n (by omega)⟩,fun ⟨h,h'⟩ i hi => by rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with ha|rfl; exacts [h i ha,h']⟩

variable (hf : ContDiffAt ℂ ω f 0) (hg : ContDiffAt ℂ ω g 0)
include hf
lemma line_smooth (p : Momentum) (n : ℕ∞ω) : ContDiffAt ℂ n (fun t : ℂ => f (t • p)) 0 :=
  ((show ContDiffAt ℂ ω f ((0:ℂ) • p) by rwa [zero_smul]).of_le le_top).comp (f:=fun t => t • p) (0:ℂ) (by fun_prop)

lemma line_one (p : Momentum) : lineD f p 1 = fderiv ℂ f 0 p := by
  rw [lineD, iteratedDeriv_one]; have h₁ : HasDerivAt (fun t : ℂ => t • p) p 0 := by simpa only [one_smul] using (hasDerivAt_id' (0:ℂ)).smul_const p
  exact ((show HasFDerivAt f (fderiv ℂ f 0) ((0:ℂ) • p) by simpa using (hf.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 h₁).deriv

private lemma fd_ray (p : Momentum) : deriv (fun t : ℂ => f (t • p)) =ᶠ[𝓝 0] fun t : ℂ => fderiv ℂ f (t • p) p := by
  have h : Tendsto (fun t : ℂ => t • p) (𝓝 0) (𝓝 0) := tendsto_ray p
  filter_upwards [h.eventually (hf.eventually (by simp))] with t ht
  exact ((ht.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (show HasDerivAt (fun z : ℂ => z • p) p t by simpa only [one_smul] using (hasDerivAt_id' t).smul_const p)).deriv
lemma line_two (p : Momentum) : lineD f p 2 = fderiv ℂ (fderiv ℂ f) 0 p p := by
  rw [lineD, iteratedDeriv_succ,iteratedDeriv_one,(fd_ray hf p).deriv_eq]
  have h₁ : HasDerivAt (fun t : ℂ => t • p) p 0 := by simpa only [one_smul] using (hasDerivAt_id' (0:ℂ)).smul_const p
  have h₂ := ((hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt (fun z : ℂ => fderiv ℂ f (z • p)) (fderiv ℂ (fderiv ℂ f) 0 p) 0 := (show HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) 0) ((0:ℂ) • p) by rw [zero_smul]; exact h₂).comp_hasDerivAt 0 h₁
  have h₃ := hcomp.clm_apply (hasDerivAt_const 0 p)
  simpa only [map_zero,add_zero,Function.comp_def] using h₃.deriv

include hg
lemma line_mul (p n) : lineD (fun z => f z * g z) p n =
    ∑ i ∈ Finset.range (n+1),(n.choose i:ℂ) * lineD f p i * lineD g p (n-i) := iteratedDeriv_fun_mul (line_smooth hf p n) (line_smooth hg p n)
lemma line_sub (p n) : lineD (fun z => f z - g z) p n = lineD f p n - lineD g p n :=
  iteratedDeriv_fun_sub (line_smooth hf p n) (line_smooth hg p n)
lemma line_add (p n) : lineD (fun z => f z + g z) p n = lineD f p n + lineD g p n :=
  iteratedDeriv_fun_add (line_smooth hf p n) (line_smooth hg p n)
lemma Below.mul (h : Below f p a) (h' : Below g p b) : Below (fun z => f z * g z) p (a+b) := by
  intro k hk; rw [line_mul hf hg]
  apply Finset.sum_eq_zero; intro i hi; by_cases hi' : i < a
  · rw [h i hi',mul_zero,zero_mul]
  rw [h' (k-i) (by simp only [Finset.mem_range] at hi; omega),mul_zero]
lemma Below.product (h : Below f p a) (h' : Below g p b) : lineD (fun z => f z * g z) p (a+b) =
    ((a+b).choose a:ℂ) * lineD f p a * lineD g p b := by
  rw [line_mul hf hg,Finset.sum_eq_single a,Nat.add_sub_cancel_left]
  · intro i hi ha; by_cases hi' : i < a
    · rw [h i hi',mul_zero,zero_mul]
    rw [h' (a+b-i) (by simp only [Finset.mem_range] at hi; omega),mul_zero]
  simp
omit hf hg in
lemma line_sum {ι : Type*} (s : Finset ι) (u : ι → Momentum → ℂ) (h : ∀ i∈s,ContDiffAt ℂ ω (u i) 0) (p n) :
    lineD (fun z => ∑ i∈s,u i z) p n = ∑ i∈s,lineD (u i) p n := iteratedDeriv_fun_sum fun i hi => line_smooth (h i hi) p n
omit hf hg in
lemma line_const_mul (c : ℂ) (p n) : lineD (fun z => c * f z) p n = c * lineD f p n := iteratedDeriv_const_mul_field ..

omit hf hg

lemma real_line {u : ℂ → ℂ} {x : ℝ} (h : ∀ᶠ (t : ℝ) in 𝓝 x, star (u (t:ℂ)) = u (t:ℂ)) (hd : DifferentiableAt ℂ u (x:ℂ)) :
    star (deriv u (x:ℂ)) = deriv u (x:ℂ) := by
  have he : (fun t : ℝ => ((u (t:ℂ)).re:ℂ)) =ᶠ[𝓝 x] fun t : ℝ => u (t:ℂ) := h.mono fun t ht => by
    rw [Complex.star_def] at ht
    rw [Complex.conj_eq_iff_re] at ht; exact ht
  have he' := hd.hasDerivAt
  rw [← he'.comp_ofReal.deriv, ← he.deriv_eq,he'.real_of_complex.ofReal_comp.deriv]; simp

lemma real_iterate {u : ℂ → ℂ} {x : ℝ} (h : ∀ᶠ (t : ℝ) in 𝓝 x, star (u (t:ℂ)) = u (t:ℂ)) (hd : ContDiffAt ℂ ω u (x:ℂ)) (n : ℕ) :
    star (iteratedDeriv n u (x:ℂ)) = iteratedDeriv n u (x:ℂ) := by
  induction n generalizing u with
  | zero => simpa using h.self_of_nhds
  | succ n ih =>
    rw [iteratedDeriv_succ']; exact ih (by
      filter_upwards [eventually_eventually_nhds.mpr h, (continuous_ofReal.tendsto x).eventually (hd.eventually (by simp))] with t ht h'
      exact real_line ht (h'.differentiableAt (by simp))) ((hd.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => (1:ℂ)) contDiffAt_const)
end YM.Push.Loops
