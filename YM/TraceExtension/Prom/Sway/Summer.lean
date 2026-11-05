import YM.Next.RANK.Displacement
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer Maxwell
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n d p k l : ℕ} (A : Levels G)

lemma mag_rank {b a:ℝ}(h:b ≤ a) (k:ℕ): mag A b k ≤ mag A a k:= by rw [mag_bill, mag_bill]; exact Glimmer.billed _ h
lemma racing (h:G.Simple) (b:ℝ)(hb:0 < b) (ζ : ℕ→ℕ) (hz : Tendsto ζ atTop atTop)(a:ℕ→ℝ) (hv:∀ i,b ≤ a i) : Tendsto (fun k=> mag A (a k) (ζ k)) atTop atTop:=by
    apply tendsto_atTop.2; intro d; filter_upwards [((mag_rate A h hb).comp hz).eventually_ge_atTop d] with k hi; exact hi.trans (mag_rank A (hv k) _)

lemma summerSky (b B : ℝ) (u : ℕ) (h : 6 ≤ b) (hg : G.Simple) {c C : ℝ} (hc : 0<c) (_hC : 1 ≤ C) : ∀ᶠ k in atTop,∀ w:ℝ,b ≤ w → w ≤ B →∀ p : ℕ,∀ z : E4,
    let M:=mag A w k; let s:=clim A k
    c*M ≤ ‖z‖→ ‖z‖ ≤ C*M → M^(4+u)*bill 1 s * stature u z ((A.S.side k p).val:ℝ) ≤ bill (-4) s := by
  have hb : 0<b := by linarith
  filter_upwards [radiant_cost A 1 (2*(1+C)) (-4) B (4+u) hg,
    (hat_rate A hg).eventually (transports (show (1:ℝ) < -4+b by linarith) (2/(c^(u+5))))] with k hr ht w hwB hW p z
  let s:=clim A k
  let N := (A.S.side k p).val
  intro M s hL hR
  have hw : 1 ≤ M := by change 1≤mag _ _ _; rw [mag_bill]; exact Glimmer.costed w _ (hb.le.trans hwB)
  have hz := mul_pos hc (zero_lt_one.trans_le hw)
  have hp : 0<‖z‖ := hz.trans_le hL
  have ht' : 2*(M^(4+u)*bill 1 s* (1/‖z‖^(u+5))) ≤ bill (-4) s := calc
    _ ≤ 2*(M^(4+u)*bill 1 s * (1/(c*M)^(u+5))) := by
      have hY : 0 < bill 1 s := Real.exp_pos _
      gcongr
    _ ≤ _ := by
      have he : (2/c^(u+5))*bill 1 s ≤ bill (-4) s * M := by
        change _ ≤ bill (-4+b) _ at ht; change _ * _ ≤ _; rw [show M=_ from mag_bill ..,overlap]; exact ht.trans (Glimmer.billed _ (by linarith only [hwB]))
      rw [show 2*(M^(4+u)*bill 1 s*(1/(c*M)^(u+5)))=(2/c^(u+5))*bill 1 s / M by rw [mul_pow,show u+5=(4+u)+1 by omega,pow_succ M]; field_simp]; exact (div_le_iff₀ (zero_lt_one.trans_le hw)).2 he
  have ha : (1+‖z‖) ≤ (1+C)*M := by linarith
  have hN : 0 < (N:ℝ) := by positivity
  have hv : 0 < M^(4+u)*bill 1 s := mul_pos (pow_pos (zero_lt_one.trans_le hw) _) (Real.exp_pos _)
  have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ha hN.le) hv.le
  have hf : M^(4+u)*bill 1 s*(2*(1+C)*M/(N:ℝ)) ≤ bill (-4) s := by
    let Z:=mag A B k; have hz : M ≤ Z:= mag_rank _ hW k; have hC : 0 ≤ 1+C:=by linarith only [_hC]
    have hA : 0<bill 1 s:= Real.exp_pos _
    apply le_trans _ (hr p); change _ ≤ Z^(4+u)*bill 1 s*(2*(1+C)*Z / _)
    gcongr
    exact mul_nonneg (pow_nonneg (zero_le_one.trans (hw.trans hz)) _) hA.le
  unfold stature; rw [mul_add]; let V:= M^(4+u)*bill 1 s; change 2*(V*_) ≤ _ at ht'
  apply (add_le_add_right hh _).trans
  rw [show M^(4+u)*bill 1 s*(2*(1+C)*M/(N:ℝ))=2*(V*((1+C)*M/N)) by dsimp [V]; ring] at hf
  change V*_+V*_≤_; linarith only [ht',hf]
end YM.Next.Rank.Wall
