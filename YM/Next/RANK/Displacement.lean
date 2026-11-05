import YM.Next.RANK.Hydro
import YM.Next.RANK.Walling

/-! Geometry at all offsets needed by the endpoint kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer Maxwell
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n d p k l : ℕ} (A : Levels G)

lemma range_bound (x : Points n) (i j) (hr : x i ≠ x j) (L S : Degree G) (hg : G.Simple) {b : ℝ} (hb : 0<b) :
    ∃ C c : ℝ, 0<c ∧ 1≤C ∧ ∀ᶠ k in atTop, ∀ u w : Cover, street u ≤ wood A k → street w ≤ wood A k →
      let K:=moved x A b i j k u w
      let M:=mag A b k
      c*M≤ ‖K‖ ∧ ‖K‖ ≤ C*M ∧ ‖gleam L S (M⁻¹ • K)‖≤C := by
  let H:= x i - x j
  have h : H∈away := sub_ne_zero.mpr hr
  let c:= ‖H‖/2
  have hf : 0<c := half_pos (norm_pos_iff.mpr h)
  let C:= 1+‖H‖+‖gleam L S H‖
  have hv := (gleam_diff L S H h).continuousAt (open_away.mem_nhds h)
  have hx : ∀ᶠ z in 𝓝 H, c ≤ ‖z‖ ∧ ‖z‖ ≤ C ∧ ‖gleam L S z‖ ≤ C := by
    refine (continuous_norm.continuousAt.eventually (le_mem_nhds (half_lt_self (norm_pos_iff.mpr (show H≠0 from h))))).and ((continuous_norm.continuousAt.eventually (ge_mem_nhds ?_)).and
      (hv.norm.eventually (ge_mem_nhds ?_)))
    · change ‖H‖<C; unfold C; linarith [norm_nonneg (gleam L S H)]
    change ‖_‖<C; unfold C; linarith [norm_nonneg H]
  obtain ⟨ε,hε,hx⟩ := Metric.mem_nhds_iff.mp hx
  refine ⟨C,c,hf,?_,(near_offsets x A hb i j hg ε hε).mono ?_⟩
  · unfold C; linarith [norm_nonneg H,norm_nonneg (gleam L S H)]
  intro k hk u w h₁ h₂ K M
  have he : 0 < M := mag_pos ..
  have ht : M⁻¹ • K ∈ Metric.ball H ε := hk u w h₁ h₂
  obtain ⟨hx,h₂,H⟩ := hx ht; rw [norm_smul,norm_inv,Real.norm_of_nonneg he.le,← div_eq_inv_mul,le_div_iff₀ he] at hx; rw [norm_smul,norm_inv,Real.norm_of_nonneg he.le,← div_eq_inv_mul,div_le_iff₀ he] at h₂; exact ⟨hx,h₂,H⟩

lemma radiant_cost (ε c B b : ℝ) (i : ℕ) (hg : G.Simple) : ∀ᶠ k in atTop, ∀ p : ℕ,
    let r := mag A b k
    r^i * bill ε (clim A k) * (c * r / (A.S.side k p).val) ≤ bill B (clim A k) := by
  let d:= b*i+ε+b-B
  filter_upwards [far A hg d c] with k h p
  intro r; have he := h p
  let t:= clim A k
  rw [show r= _ from mag_bill A b k,bills,overlap]
  apply le_of_mul_le_mul_right (a:=bill (-B) t) _ (Real.exp_pos _);
  rw [overlap,add_neg_cancel,bill_zero]; convert! he using 1
  rw [show d=b*i+ε+(b+ -B) by dsimp only [d]; ring]; simp only [← overlap,t]; ring

lemma summer (b : ℝ) (u : ℕ) (h : 6 ≤ b) (hg : G.Simple) {c C : ℝ} (hc : 0<c) (_hC : 1 ≤ C) : ∀ᶠ k in atTop,∀ p : ℕ,∀ z : E4,
    let M:=mag A b k; let s:=clim A k
    c*M ≤ ‖z‖→ ‖z‖ ≤ C*M → M^(4+u)*bill 1 s * stature u z ((A.S.side k p).val:ℝ) ≤ bill (-4) s := by
  have hb : 0<b := by linarith
  filter_upwards [radiant_cost A 1 (2*(1+C)) (-4) b (4+u) hg,
    (hat_rate A hg).eventually (transports (show (1:ℝ) < -4+b by linarith) (2/(c^(u+5))))] with k hr ht p z
  let s:=clim A k
  let N := (A.S.side k p).val
  intro M s hL hR
  have hw : 1 ≤ M := by change 1≤mag _ _ _; rw [mag_bill]; exact Glimmer.costed b _ hb.le
  have hz := mul_pos hc (zero_lt_one.trans_le hw)
  have hp : 0<‖z‖ := hz.trans_le hL
  have ht' : 2*(M^(4+u)*bill 1 s* (1/‖z‖^(u+5))) ≤ bill (-4) s := calc
    _ ≤ 2*(M^(4+u)*bill 1 s * (1/(c*M)^(u+5))) := by
      have hY : 0 < bill 1 s := Real.exp_pos _
      gcongr
    _ ≤ _ := by
      have he : (2/c^(u+5))*bill 1 s ≤ bill (-4) s * M := by
        change _ ≤ bill (-4+b) _ at ht; rw [← overlap] at ht; rw [show M=_ from mag_bill ..]; exact ht
      rw [show 2*(M^(4+u)*bill 1 s*(1/(c*M)^(u+5)))=(2/c^(u+5))*bill 1 s / M by rw [mul_pow,show u+5=(4+u)+1 by omega,pow_succ M]; field_simp]; exact (div_le_iff₀ (zero_lt_one.trans_le hw)).2 he
  have ha : (1+‖z‖) ≤ (1+C)*M := by linarith
  have hN : 0 < (N:ℝ) := by positivity
  have hv : 0 < M^(4+u)*bill 1 s := mul_pos (pow_pos (zero_lt_one.trans_le hw) _) (Real.exp_pos _)
  have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ha hN.le) hv.le
  have hf : M^(4+u)*bill 1 s*(2*(1+C)*M/(N:ℝ)) ≤ _ := hr p
  unfold stature; rw [mul_add]; let V:= M^(4+u)*bill 1 s; change 2*(V*_) ≤ _ at ht'
  apply (add_le_add_right hh _).trans
  rw [show M^(4+u)*bill 1 s*(2*(1+C)*M/(N:ℝ))=2*(V*((1+C)*M/N)) by dsimp [V]; ring] at hf
  change V*_+V*_≤_; linarith only [ht',hf]
end YM.Next.Rank.Wall
