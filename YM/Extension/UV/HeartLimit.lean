import YM.Extension.UV.FloorD
/-! Limits of Free's analytic metric including at zero and all lattice momenta. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Set Filter Function Lattice RG Laurent Exterior Bloch Metric Next.Free
open scoped Topology BigOperators
variable {G:Gauge}

lemma Dnorm_lower (k : ℝ) (hk : 0 < k) (A:Levels G) (m : ℕ) {p : Momentum} (hp:p ∈ baseCube) (he:p≠0) : ∃ c>0,∀ (a:Axis) (n:ℕ), c ≤ ‖Train.levelD k (location A n m) a p‖ := by
  obtain ⟨η,c,hη,hc,hb⟩ := Train.bulb_firm k hk (fun x : Train (A.clock.J m) × Axis => x.1) (fun x=> x.2)
  have hg := meter.high_pos
  have hl := lengthSq_pos he
  refine ⟨c/((meter.high)^2*lengthSq p),by positivity,fun a n=>?_⟩
  let v := location A n m
  have hh := (divisor_real_bounds v.mass (base_subset_realCube zone_pos hp)).2
  have hh' : (divisor v.mass p).re = ‖divisor v.mass p‖ := (Silver.chipSq _ hp.1).norm.symm
  rw [hh'] at hh
  have h' := hb (v,a) p (base_subset_realCube hη hp)
  simp only [mul_one] at h'
  rw [v.D_bulb k (base_subset_realCube zone_pos hp) he]
  rw [norm_div]
  apply div_le_div₀ (norm_nonneg _) _ _ _
  · exact h'
  · exact norm_pos_iff.mpr (divisor_ne v.mass (base_subset_realCube zone_pos hp) he)
  exact hh

lemma D_and_rho (k:ℝ) (hk : 0<k) (A:Levels G) (h:SizeFloor k A) (m:ℕ) {p:Momentum} (hp:p∈baseCube) (h0:p≠0) :
    ∃ z : Axis → ℂ, ∃ y:ℂ, (∀ a, Tendsto (fun n=>Train.levelD k (location A n m) a p) atTop (𝓝 (z a))) ∧
    Tendsto (fun n=>Train.rho k (location A n m) p) atTop (𝓝 y) ∧ (∀ a,z a≠0) ∧ y≠ 0 := by
  choose z hZ using fun a=> converges_D k A h m a hp h0
  set y:=∑ a, jewel 1 p a / z a
  have hv a n := Train.D_cost k hk (location A n m) a hp.1
  obtain ⟨c,hc,hge⟩ := Dnorm_lower k hk A m hp h0
  have hnv a : z a≠0 := norm_pos_iff.mp (hc.trans_le (ge_of_tendsto' (hZ a).norm (hge a)))
  have hz a : Silver (z a) := by
    have ht : Tendsto (fun i=> ((Train.levelD k (location A i m) a p).re:ℂ)) atTop (𝓝 ((z a).re:ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp (Complex.continuous_re.continuousAt.tendsto.comp (hZ a))
    simp_rw [(hv a _).of_real] at ht
    exact ⟨(z a).re, ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp (hZ a)) (fun i=> (hv a i).re_nonneg), tendsto_nhds_unique (hZ a) ht⟩
  have hu : Tendsto (fun n=>Train.rho k (location A n m) p) atTop (𝓝 y) := by
    unfold Train.rho y
    apply tendsto_finsetSum
    intro a _
    exact tendsto_const_nhds.div (hZ a) (hnv a)
  have hy : (y.re)>0 := by
    have hd := divisor_ne 1 (base_subset_realCube zone_pos hp) h0
    have hg : ∃ a, jewel 1 p a ≠ 0:= by contrapose hd; push Not at hd; simp only [divisor,jewel] at *; simp [hd]
    obtain ⟨a,ha⟩:=hg
    have h₁ := ((jewel_price _ _ hp.1).div (hz a)).re_ne (div_ne_zero ha (hnv a))
    change (∑ i, jewel 1 p i / z i).re > 0; rw [Complex.re_sum]
    exact h₁.trans_le (Finset.single_le_sum (f:=fun i=> (jewel 1 p i / z i).re) (fun i _=> ((jewel_price _ _ hp.1).div (hz i)).re_nonneg) (Finset.mem_univ a))
  exact ⟨z,y,hZ,hu,hnv,fun he=> by simp_all⟩

lemma tendsto_inventory (n : ℕ) {I : Type*} {l : Filter I} (q : I → Axis→ℂ) (w : Axis→ℂ) (h: ∀ a,Tendsto (fun i=>q i a) l (𝓝 (w a))) : Tendsto (fun i=>mask n (q i)) l (𝓝 (mask n w)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  simp only [mask,inventory,Matrix.diagonal_apply]
  split_ifs with he
  · apply tendsto_finsetProd
    intro c _
    exact h c
  exact tendsto_const_nhds

lemma pulse_vault_limits (k : ℝ) (hk : 0<k) (A:Levels G) (h:SizeFloor k A) (m:ℕ) {p:Momentum} (hp:p∈baseCube):
    ∃ x y, Tendsto (fun n=>pulse k (location A n m) p) atTop (𝓝 x) ∧ Tendsto (fun n=>vault k (location A n m) p) atTop (𝓝 y) := by
  by_cases h0 : p=0
  · subst p; simp
  obtain ⟨z,b,hz,hb,hn,hbn⟩ := D_and_rho k hk A h m hp h0
  refine ⟨b⁻¹ • mask 2 z⁻¹ ,b • mask 2 z,?_,?_⟩
  · simp_rw [pulse_sources _ hk _ (base_subset_realCube zone_pos hp) h0]
    exact (hb.inv₀ hbn).smul (tendsto_inventory _ _ z⁻¹ (fun a=> (hz a).inv₀ (hn a)))
  simp_rw [vault_sources _ hk _ (base_subset_realCube zone_pos hp) h0]
  exact hb.smul (tendsto_inventory _ _ z hz)
end YM.Extension.UV.Linear
