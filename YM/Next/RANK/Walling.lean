import YM.Next.RANK.ParticleGate

/-!
# Check separation and period costs for Fourier-port outputs

Translate by normalization BEFORE taking limit. Don't interchange N estimates with
those after going to period. Take A start and rounding, any distinct probe pair.
Include offsets even out to *all* high residual lookup points admitted at that
probe's W0 test (on lifted street ball, including winding declarations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch   Atlas Station CellsInt Configuration Glimmer Filter Beamer
open scoped Topology BigOperators Classical

variable {G : Gauge} {n d p k v j : ℕ}

lemma norm_road (x : Cover) : ‖mapZ x‖ ≤ (street x:ℝ) := by
  have he : mapZ x=∑ i : Axis,(x i:ℝ) • basis i := by ext1 i; simp [mapZ, apply_ite]
  rw [he]; apply (norm_sum_le ..).trans
  simp only [norm_smul,basis_norm,mul_one,Real.norm_eq_abs,← Int.cast_abs, Int.abs_eq_natAbs,Int.cast_natCast,street,Nat.cast_sum]; exact le_rfl
lemma sends_map (x y : Cover) : mapZ (x+y)=mapZ x+mapZ y := by ext1 i; simp [mapZ]
lemma sends_sub (x y : Cover) : mapZ (x-y)=mapZ x-mapZ y := by ext1 i; simp [mapZ]


-- k-relative physical displacement. measurement on $ρ$ scale, not a_l.

def moved (x : Points n) (A : Levels G) (b : ℝ) (i j : Fin n) (k : ℕ) (L S : Cover) : E4 :=
    let f:= Station.choose A b k x; mapZ ((f i+L)-(f j+S))
lemma settled (x : Points n) (A : Levels G) (b : ℝ) (i j) k L S : (mag A b k)⁻¹ • moved x A b i j k L S =
    ((tested A b k x) i-(tested A b k x) j)+ (mag A b k)⁻¹ • (mapZ L-mapZ S) := by
  unfold moved; rw [sends_sub,sends_map,sends_map, add_sub_add_comm,smul_add,smul_sub _ (mapZ ((choose A b k x) i)) (mapZ ((choose A b k x) j))]
  congr 1; rw [reading]; rfl

-- decay of sum of offset costs. no supports after reading omitted.

lemma near_offsets (x : Points n) (A : Levels G) {b : ℝ} (hp : 0<b) (i j : Fin n) (hg : G.Simple) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ a c : Cover, street a≤ wood A k → street c≤ wood A k → dist ((mag A b k)⁻¹ • moved x A b i j k a c) (x i - x j)<ε := by
  let f (k) := tested A b k x i-tested A b k x j
  have ht : Tendsto f atTop (𝓝 (x i-x j)) :=
    (show Continuous (fun x : Points n => x i-x j) from by fun_prop).continuousAt.tendsto.comp (tuning A x hg hp)
  let Y k := wood A k
  filter_upwards [ht.eventually (Metric.ball_mem_nhds _ (half_pos he)),
    (hat_rate A hg).eventually (transports (show b/2<b by linarith) (4/ε)),
    (hat_rate A hg).eventually (zone_power 1 (show 0<b/2 by linarith))] with k hk h1 h2 a c ha hc
  let M:=Station.mag A b k
  have hv : 0<M := mag_pos ..
  simp only [pow_one] at h2
  let w := M⁻¹ • (mapZ a-mapZ c)
  have hy : ‖mapZ a-mapZ c‖ ≤ 2*↑(Y k) := by
    apply (norm_sub_le ..).trans; linarith only [le_trans (norm_road a) (show (street a:ℝ) ≤ Y k by exact_mod_cast ha),le_trans (norm_road c) (show (street c:ℝ) ≤ Y k by exact_mod_cast hc)]
  have hh : ‖w‖ ≤ ε/2 := by
    unfold w; rw [norm_smul,norm_inv, Real.norm_of_nonneg hv.le]
    apply (mul_le_mul_of_nonneg_left hy (inv_pos.mpr hv).le).trans
    rw [← div_eq_inv_mul, div_le_iff₀ hv]; unfold Y; field_simp at h1; change (↑(lengthW _):ℝ) ≤ _ at h2; unfold M; rw [mag_bill]; nlinarith only [h1,h2]
  rw [settled]; change dist (f k+w) _< ε
  have ht : dist (f k+w) (f k) ≤ ε/2 := by rw [dist_eq_norm, add_comm,add_sub_cancel_right]; exact hh
  exact lt_of_le_of_lt (dist_triangle _ (f k) _) (by linarith only [ht, Metric.mem_ball.mp hk])

-- grow any fixed power of p vs side on original clock, uniform all periods without selecting larger p.
lemma beyond_hat (A : Levels G) (hg : G.Simple) (b : ℝ) : Tendsto (fun k => bill b (clim A k)*A.S.a k) atTop (𝓝 0) := by simp_rw [← mag_bill]; simpa only [mul_comm] using! gap_rate A hg b
lemma far (A : Levels G) (hg : G.Simple) (b C : ℝ) : ∀ᶠ k in atTop,∀ p : ℕ, C*bill b (clim A k)/(A.S.side k p).val ≤ 1 := by
  rcases le_or_gt C 0 with H|H
  · refine Eventually.of_forall fun k p => ?_
    exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg H (Real.exp_pos _).le) (by positivity)).trans zero_le_one
  have he := (beyond_hat A hg b).const_mul C; rw [mul_zero] at he
  filter_upwards [he.eventually (ge_mem_nhds zero_lt_one)] with i hi p
  rw [div_le_one (show 0<((A.S.side i p).val:ℝ) by positivity)]
  let u:= A.S.denominator i
  have hp : u.val ≤ (A.S.side i p).val := Nat.le_mul_of_pos_left _ (A.S.period p).property
  refine le_trans ?_ (Nat.cast_le.mpr hp)
  have hr : A.S.a i=(u.val:ℝ)⁻¹ := rfl
  change C*(_*A.S.a i) ≤ _ at hi; rw [hr,← mul_assoc,← div_eq_mul_inv,div_le_one (by positivity)] at hi; exact hi

-- normalized kpcu error primitive. `e0` actual promised coefficient (tested uniformly through rack), costs exponent.

def stature (D : ℕ) (z : E4) (p : ℝ) := 1/‖z‖^(D+5)+(1+‖z‖)/p

end YM.Next.Rank.Wall
