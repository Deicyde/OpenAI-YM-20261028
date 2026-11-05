import YM.Next.RANK.Hydro
import YM.Next.RANK.Walling

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer
open scoped Topology BigOperators Classical

variable {G : Gauge} {n d p k v j : ℕ}

lemma near_offsetsX (x : Points n) (A : Levels G) {b : ℝ} (hp : 0<b) (i j : Fin n) (hg : G.Simple) (ε : ℝ) (he : 0<ε) (ζ : ℕ→ℕ) (hz:Tendsto ζ atTop atTop)(px:ℕ → Points n)(zφ:Tendsto (fun i=> tested A b (ζ i) (px i)) atTop (𝓝 x)) :
    ∀ᶠ k in atTop, ∀ a c : Cover, street a≤ wood A (ζ k) → street c≤ wood A (ζ k) → dist ((mag A b (ζ k))⁻¹ • moved (px k) A b i j (ζ k) a c) (x i - x j)<ε := by
  let f (k) := tested A b (ζ k) (px k) i-tested A b (ζ k) (px k) j
  have ht : Tendsto f atTop (𝓝 (x i-x j)) :=
    (show Continuous (fun x : Points n => x i-x j) from by fun_prop).continuousAt.tendsto.comp zφ
  let Y k := wood A (ζ k)
  filter_upwards [ht.eventually (Metric.ball_mem_nhds _ (half_pos he)),
    ((hat_rate A hg).comp hz).eventually (transports (show b/2<b by linarith) (4/ε)),
    ((hat_rate A hg).comp hz).eventually (zone_power 1 (show 0<b/2 by linarith))] with k hk h1 h2 a c ha hc
  let M:=Station.mag A b (ζ k)
  have hv : 0<M := mag_pos ..
  simp only [pow_one] at h2
  let w := M⁻¹ • (mapZ a-mapZ c)
  have hy : ‖mapZ a-mapZ c‖ ≤ 2*↑(Y k) := by
    apply (norm_sub_le ..).trans; linarith only [le_trans (norm_road a) (show (street a:ℝ) ≤ Y k by exact_mod_cast ha),le_trans (norm_road c) (show (street c:ℝ) ≤ Y k by exact_mod_cast hc)]
  have hh : ‖w‖ ≤ ε/2 := by
    unfold w; rw [norm_smul,norm_inv, Real.norm_of_nonneg hv.le]
    apply (mul_le_mul_of_nonneg_left hy (inv_pos.mpr hv).le).trans
    rw [← div_eq_inv_mul, div_le_iff₀ hv]; unfold Y; field_simp at h1; change (↑(lengthW _):ℝ) ≤ _ at h2; unfold M; rw [mag_bill]; dsimp only [Function.comp_apply] at h1 h2; unfold wood clim; nlinarith only [h1,h2]
  rw [settled]; change dist (f k+w) _< ε
  have ht : dist (f k+w) (f k) ≤ ε/2 := by rw [dist_eq_norm, add_comm,add_sub_cancel_right]; exact hh
  exact lt_of_le_of_lt (dist_triangle _ (f k) _) (by linarith only [ht, Metric.mem_ball.mp hk])


end YM.Next.Rank.Wall
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer Maxwell
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n d p k l : ℕ} (A : Levels G)

lemma range_boundX (x : Points n) (i j) (hr : x i ≠ x j) (L S : Degree G) (hg : G.Simple) {b : ℝ} (hb : 0<b) (ζ : ℕ→ℕ) (hz:Tendsto ζ atTop atTop)(px:ℕ → Points n)(zφ:Tendsto (fun i=> tested A b (ζ i) (px i)) atTop (𝓝 x)) :
    ∃ C c : ℝ, 0<c ∧ 1≤C ∧ ∀ᶠ k in atTop, ∀ u w : Cover, street u ≤ wood A (ζ k) → street w ≤ wood A (ζ k) →
      let K:=moved (px k) A b i j (ζ k) u w
      let M:=mag A b (ζ k)
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
  refine ⟨C,c,hf,?_,(near_offsetsX x A hb i j hg ε hε ζ hz px zφ).mono ?_⟩
  · unfold C; linarith [norm_nonneg H,norm_nonneg (gleam L S H)]
  intro k hk u w h₁ h₂ K M
  have he : 0 < M := mag_pos ..
  have ht : M⁻¹ • K ∈ Metric.ball H ε := hk u w h₁ h₂
  obtain ⟨hx,h₂,H⟩ := hx ht; rw [norm_smul,norm_inv,Real.norm_of_nonneg he.le,← div_eq_inv_mul,le_div_iff₀ he] at hx; rw [norm_smul,norm_inv,Real.norm_of_nonneg he.le,← div_eq_inv_mul,div_le_iff₀ he] at h₂; exact ⟨hx,h₂,H⟩


end YM.Next.Rank.Wall
