import YM.Heat.Rows



/-!
# Scales between 0 and infinity match F and have no kernel
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : Semigroup H a)

lemma quotient (p n : ℕ) (hp : 0<p) (hn : 0<n) :
    S.F (duration (p/(n:ℝ≥0)))=S.E (p/(n:ℝ≥0)) := by
  let d := (p:ℝ≥0)/n
  let t := (n:ℝ≥0)⁻¹
  have he : 0 < d := by dsimp only [d]; positivity
  have hpos := dur.mpr he
  let y := S.E t
  have hs : (S.E 1)=y^n := by
    rw [show S.E 1=S.E (n • t) from congr_arg S.E (by dsimp only [t]; simp [hn.ne']),S.clock_mul]
  have hv : S.E d = y ^ p := by
    dsimp only [d]; rw [show (p:ℝ≥0)/n=p•t by simp [t,div_eq_mul_inv],S.clock_mul]
  let U := fun x : ℂ => x ^ (duration d)
  have ht : ContinuousOn U (spectrum ℂ (S.E 1)) := continuousOn_iff_continuous_restrict.mpr (S.adopt 1 _ hpos).continuous
  have hh : ContinuousOn U ((· ^ n : ℂ → ℂ) '' spectrum ℂ y) := by
    rwa [← cfc_map_spectrum (fun x : ℂ => x ^ n) y (S.stare t).isStarNormal (by fun_prop),cfc_pow_id (R := ℂ) y n (S.stare t).isStarNormal,← hs]
  change S.F (duration d) = S.E d
  have hid : S.F (duration d) = cfc U (S.E 1) := by
    rw [F,cfc_apply U _ (S.stare 1).isStarNormal ht]; apply congr_arg; simp [roots,hpos,U];rfl
  rw [hid,hs, hv,← cfc_comp_pow U n y hh (S.stare t).isStarNormal, ← cfc_pow_id (R := ℂ) y p (S.stare t).isStarNormal]
  apply cfc_congr
  intro x hx
  obtain ⟨r,hr,hh,rfl⟩ := S.at_root hx
  dsimp only [U,duration]
  rw [← ofReal_pow,← ofReal_pow,← ofReal_cpow (pow_nonneg hr n),← Real.rpow_natCast_mul hr,
    show (n:ℝ)*(d:ℝ)=(p:ℝ) by simp [d]; field_simp,rpow_cast]
where rpow_cast (x : ℝ) (p : ℕ) : x^(p:ℝ)=x^p := by norm_cast

lemma roots_heat {t : ℝ≥0} (ht : 0<t) : S.F (duration t)=S.E t := by
  let p (n : ℕ) := ⌊(t:ℝ)*((n+1:ℕ):ℝ)⌋₊+1
  let r n := (p n : ℝ≥0)/((n+1:ℕ):ℝ≥0)
  have he : Tendsto r atTop (𝓝 t) := by
    apply NNReal.tendsto_coe.mp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (t:ℝ)) (h := fun n : ℕ => (t:ℝ) + 1/(n+1:ℕ))
      tendsto_const_nhds ?_ ?_ ?_
    · have hv : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      simpa using (tendsto_const_nhds (x := (t:ℝ))).add ((tendsto_const_nhds (x := (1:ℝ))).div_atTop hv)
    · intro n
      dsimp only [r]; rw [NNReal.coe_div, NNReal.coe_natCast,NNReal.coe_natCast,le_div_iff₀ (by positivity)]
      unfold p; simpa using (Nat.lt_floor_add_one ((t:ℝ)*((n+1:ℕ):ℝ))).le
    intro n
    have hz : (0:ℝ)<(n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
    dsimp only
    dsimp only [r]; rw [NNReal.coe_div, NNReal.coe_natCast,NNReal.coe_natCast,div_le_iff₀ hz, add_mul,div_mul_cancel₀ _ hz.ne']
    unfold p; rw [Nat.cast_add_one]; gcongr
    exact Nat.floor_le (by positivity)
  ext1 v
  have hp : Tendsto (fun n => S.F (duration (r n))) atTop (𝓝 (S.F (duration t))) :=
    (S.localHeat _ (dur.mpr ht)).continuousAt.tendsto.comp ((continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.comp he)
  have hH := (((ContinuousLinearMap.apply ℂ H.space v).continuous.continuousAt (x := S.F (duration t))).tendsto.comp hp).congr' (f₂ := fun n => S.E (r n) v)
    (Eventually.of_forall fun i => congr_arg (fun f : H.Op => f v) (S.quotient (p i) (i+1) (Nat.succ_pos _) (by omega)))
  exact tendsto_nhds_unique hH ((S.continuousE v).continuousAt.tendsto.comp he)

/-!
## Dense range for each positive time
 Identity theorem (F on nonzero real times) simplifies kernel=0. -/
lemma heat_faithful (t : ℝ≥0) (x : H) (h : S.E t x=0) : x=0 := by
  let f : ℂ → H := fun z => S.F z x
  have he : AnalyticOnNhd ℂ f inside := fun z hz => (ContinuousLinearMap.apply ℂ H.space x).analyticAt _
    |>.comp (S.localHeat z hz)
  let z : ℂ := duration (t+1)
  have hv : z∈inside := dur.mpr (by positivity)
  have hf (u : ℝ≥0) (hu : t ≤ u) (hw : 0<u) : f (duration u)=0 := by
    dsimp only [f]; rw [S.roots_heat hw,show S.E u=(S.E (u-t)).comp (S.E t) from by rw [← S.time, tsub_add_cancel_of_le hu],ContinuousLinearMap.comp_apply,h,map_zero]
  have hu : EqOn f 0 inside := by
    apply he.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0 |>.isPreconnected) hv
    intro hn
    have hy : Tendsto duration (𝓝[>] (t+1)) (𝓝[≠] z) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with i hi
      have hI := mem_Ioi.mp hi
      change ¬duration i=z; exact fun he => hI.ne' (Subtype.ext (Complex.ofReal_injective he))
    obtain ⟨i,hi,hq⟩ := ((hy.eventually hn).and self_mem_nhdsWithin).exists
    have ht := lt_trans (lt_add_of_pos_right t (by norm_num : (0:ℝ≥0)<1)) (mem_Ioi.mp hq)
    exact hi (hf _ ht.le (lt_of_le_of_lt t.property ht))
  have ht : Tendsto (fun i : ℝ≥0 => S.E i x) (𝓝[>] (0:ℝ≥0)) (𝓝 x) := by
    have hx := ((S.continuousE x).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
          -- rewrite only
    rw [show S.E 0 x=x by rw [S.eZero];rfl] at hx; exact hx
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (by
    filter_upwards [self_mem_nhdsWithin] with i hi
    rw [← S.roots_heat (mem_Ioi.mp hi)]; exact (hu (dur.mpr hi)).symm))
end YM.OS.Semigroup
