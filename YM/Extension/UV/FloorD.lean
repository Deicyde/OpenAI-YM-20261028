import YM.Extension.UV.FreeTail
/-! Decay pre-floor for the linear Wilson data. Only about actual Levels satisfying this extra
schedule estimate; no UV interaction premise inferred from free convergence.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Extension.UV.Linear
open Set Filter Function Lattice RG Laurent Bloch Metric Next.Free
open scoped Topology BigOperators
variable {G:Gauge}
/-- A pre-L floor available in fixed kernel schedule quantifier order. -/
def SizeFloor (k : ℝ) (A:Levels G) := ∀ i, Dcost k (A.clock.J (i+1)) ≤ (A.S.block i).val
lemma cost_decays (k : ℝ) (A:Levels G) (h:SizeFloor k A) (m:ℕ) : Tendsto (fun i=>Dcost k (A.clock.J i) / ((location A i m).mass.val:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun i:ℕ=> (2:ℝ)^(i-1-m)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp (tendsto_atTop_atTop.mpr fun j=> ⟨j+m+1,fun i hi=> by omega⟩)
  apply squeeze_zero' (Eventually.of_forall fun i=> div_nonneg (Dcost_pos _ _).le (by positivity)) ?_ (tendsto_inv_atTop_zero.comp ht)
  filter_upwards [eventually_ge_atTop (m+1)] with i hi
  change Dcost k (A.clock.J i) / _ ≤ (2^(i-1-m))⁻¹
  have hM := mass_growth A m i (by omega)
  rw [div_le_iff₀ (by positivity : 0< ((location A i m).mass.val:ℝ)), inv_mul_eq_div,le_div_iff₀ (by positivity)]
  apply le_trans (b:= ((A.S.block (i-1)).val:ℝ)*2^(i-1-m))
  · exact mul_le_mul_of_nonneg_right (by simpa only [show i-1+1=i by omega] using h (i-1)) (by positivity)
  exact hM

lemma converges_D (k:ℝ) (A:Levels G) (h:SizeFloor k A) (m:ℕ) (a:Axis) {p:Momentum} (hp:p∈baseCube) (h0:p≠0) : ∃ z, Tendsto (fun n=>Train.levelD k (location A n m) a p) atTop (𝓝 z) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr ?_)
  obtain ⟨b,hb,ht⟩ := Dtail_bound k A m a p hp h0
  intro ε he
  have hv : ∀ᶠ n in atTop,(b * (Dcost k (A.clock.J n) / ((location A n m).mass.val:ℝ))) < ε := ((tendsto_const_nhds (x:=b)).mul (cost_decays k A h m)).eventually_lt_const  (by simpa using he)
  obtain ⟨N,hN⟩:= eventually_atTop.mp hv
  refine ⟨max m N,fun n hn=>?_⟩
  rw [dist_eq_norm]
  exact (ht (max m N) (by omega) n hn (max m N) le_rfl).trans_lt (hN _ (by omega))

end YM.Extension.UV.Linear
