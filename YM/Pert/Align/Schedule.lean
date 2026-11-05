import YM.Pert.Align.Burst
import YM.Pert.Lattice.Bundles
/-! The reporting schedule sends every compact group of physical positions to the interior far from the inversion image. -/
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Pert.Align
open Function Filter Lattice Topology
variable {n : Side} (L : Side)
def dgrid (m : ℕ) : Side := ⟨4*L.val^(m^2+1),by positivity⟩
lemma grid_rule (m : ℕ): ((dgrid L m).val:ℝ) = ((Full.period L m).val:ℝ) * Full.topSpacing L m := by
  unfold dgrid Full.period Full.topSpacing; dsimp; rw [show m^2+m+1=m^2+1+m by omega, zpow_neg]; push_cast; rw [pow_add,zpow_natCast]; have hpos : 0 < (L.val:ℝ) := by positivity
  field_simp
  simp_rw [pow_add,pow_one]
lemma L_pos (hL : 1<L.val) : 1<(L.val:ℝ) := by exact_mod_cast hL
lemma clear_rule (hL : 1<L.val): Tendsto (fun i=> (dgrid L i).val) atTop atTop := by
  apply tendsto_natCast_atTop_iff (R:=ℝ) |>.mp
  apply tendsto_atTop_mono' atTop _ (tendsto_pow_atTop_atTop_of_one_lt (L_pos L hL))
  apply Eventually.of_forall; intro m
  change ((L.val:ℝ)^m) ≤ ((dgrid L m).val:ℝ); dsimp [dgrid]; push_cast
  calc _ ≤ ((L.val:ℝ)^(m^2+1)) := pow_le_pow_right₀ (L_pos L hL).le (by nlinarith)
       _ ≤ _ := by nlinarith [one_le_pow₀ (n:=m^2+1) ((L_pos L hL).le)]
lemma cutoff_rule (hL : 1<L.val): Tendsto (Full.topSpacing L) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (L_pos L hL)))
  unfold Full.topSpacing; simp only [zpow_neg,zpow_natCast]
  exact h
lemma size_rule (hL : 1<L.val) (d : ℕ): Tendsto (fun m => ((Full.period L m).val:ℝ)*(Full.topSpacing L m)^d) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_pow_atTop_atTop_of_one_lt (L_pos L hL))
  filter_upwards [eventually_ge_atTop d] with m (hm : d≤m)
  unfold Full.period Full.topSpacing; dsimp; rw [zpow_neg,zpow_natCast,inv_pow,←pow_mul]; push_cast
  have hl : (1:ℝ)≤L.val := (L_pos L hL).le
  change (L.val:ℝ)^m ≤ 4*(L.val:ℝ)^(m^2+m+1)*((L.val:ℝ)^(m*d))⁻¹
  apply (le_div_iff₀ (show 0<(L.val:ℝ)^(m*d) by positivity)).mpr -- div definitional?
  rw [←pow_add]
  have := pow_le_pow_right₀ (a:=(L.val:ℝ)) hl (show m+m*d ≤ m^2+m+1 from by nlinarith [Nat.mul_le_mul_left m hm])
  nlinarith [one_le_pow₀ (n:=m^2+m+1) hl]

def itinerary (hL : 1<L.val) : Itinerary where
  period := Full.period L
  grid := dgrid L
  gap := Full.topSpacing L
  grid_eq:=grid_rule L
  clears:=clear_rule L hL
  positive:=Full.spacing_pos _
  cutoff:=cutoff_rule L hL
  huge := size_rule L hL
  even_at (m):= even_iff_two_dvd.mpr (Full.sized L m).2
variable {L}
lemma four_places (hL : 1<L.val) (m : ℕ) : 4 ∣ ((itinerary L hL).period m).val := dvd_mul_right ..
variable (T : Itinerary)
def rel (x : StepPath T) (i : ℕ) : Cover := lift (x i - Full.center _)
def Home (x : StepPath T) (v : E4) := Tendsto (fun i=>Full.incVec (T.gap i) (rel T x i)) atTop (𝓝 v)
lemma position_rel (x : StepPath T) (i : ℕ) : x i = Full.center _ + wrap _ (rel T x i) := by rw [rel,wrap_lift];abel
lemma inc_const (p : Cover) : Tendsto (fun m=> Full.incVec (T.gap m) p) atTop (𝓝 (0:E4)) := by
  have e (m : ℕ) : Full.incVec (T.gap m) p = T.gap m • Full.incVec 1 p := by ext k; change T.gap m * (p k:ℝ) = T.gap m * ((1:ℝ)*(p k)); ring
  simp_rw [e]; simpa only [zero_smul] using T.cutoff.smul_const (Full.incVec 1 p)
lemma large : Tendsto (fun m=>T.gap m * ((T.period m).val:ℝ)) atTop atTop := by simp_rw [mul_comm (T.gap _)]; simpa only [pow_one] using T.huge 1
lemma simple_bounds {u : ℕ→Cover} {v : E4} (hu : Tendsto (fun i=>Full.incVec (T.gap i) (u i)) atTop (𝓝 v)) : ∀ᶠ i in atTop, ∀ k : Axis, 4*|(u i k)| < (T.period i).val := by
  filter_upwards [hu.norm.eventually (gt_mem_nhds (lt_add_one ‖v‖)), (large T).eventually (eventually_gt_atTop (4*(‖v‖+1)))] with i hi h k
  have hd := PiLp.norm_apply_le (Full.incVec (T.gap i) (u i)) k
  rw [Real.norm_eq_abs] at hd
  change |T.gap i * (u i k:ℝ)| ≤ _ at hd
  rw [abs_mul, abs_of_pos (T.positive i),←Int.cast_abs] at hd
  have he : (4*|(u i k)|:ℤ) < ((T.period i).val:ℝ) := by
    push_cast; rw [←Int.cast_abs]
    nlinarith [T.positive i]
  exact_mod_cast he
lemma direct (x y : StepPath T) (p : Cover) (m:ℕ) : Full.incVec (T.gap m) (rel T x m - rel T y m +p) = Full.incVec (T.gap m) (rel T x m) - Full.incVec (T.gap m) (rel T y m) + Full.incVec (T.gap m) p := by ext k; simp [Full.incVec,mul_add,mul_sub]
lemma straight (x y : StepPath T) (p : Cover) (m : ℕ) : Full.incVec (T.gap m) (rel T x m + rel T y m+p) = Full.incVec (T.gap m) (rel T x m) + Full.incVec (T.gap m) (rel T y m) + Full.incVec (T.gap m) p := by ext k; simp [Full.incVec,mul_add]
lemma scene_home (x y : StepPath T) (u v : E4) (hx : Home T x u) (hy : Home T y v) : Scene T x y (u-v) := by
  intro p
  have he : Tendsto (fun i=>Full.incVec (T.gap i) (rel T x i-rel T y i+p)) atTop (𝓝 (u-v)) := by simp only [direct]; simpa only [add_zero] using (Tendsto.sub hx hy).add (inc_const T p)
  apply he.congr' -- eventual equality
  filter_upwards [simple_bounds T he] with i hi
  have eq : (x i - y i + wrap _ p) = wrap _ (rel T x i-rel T y i+p) := by nth_rw 1 [position_rel T x i,position_rel T y i]; simp only [map_add,map_sub]; abel
  rw [eq,lift_eq_iff.mpr ⟨rfl,fun k=>by have := hi k; have hu := neg_le_abs ((rel T x i - rel T y i + p) k);have hv := le_abs_self ((rel T x i - rel T y i + p) k); omega⟩]
lemma dist_half {x : Site n} (h4 : 4 ∣ n.val) (w : Cover) (k : Axis) (hw : 4*|w k|<(n.val:ℤ)) (eq : x = Full.center n + Full.center n + wrap n w) : (n.val:ℤ) ≤ 4*|Lattice.lift x k| := by
  have he : n.val/4 + n.val/4 = n.val/2 := by omega
  have hh : (wrap n (lift x)) k = ↑((n.val/2:ℕ):ℤ) + ↑(w k) := (congrFun (wrap_lift _) k).trans ((congrFun eq k).trans (show (↑(n.val/4:ℕ):ZMod n.val)+ ↑(n.val/4:ℕ)+↑(w k) = _ from by rw [←Nat.cast_add,he]; rw [Int.cast_natCast]))
  obtain ⟨a,ha⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (show (↑(Lattice.lift x k):ZMod n.val) = ↑((↑(n.val/2:ℕ) : ℤ)+w k) by push_cast; exact hh)
  have hpos : (0:ℤ) ≤ n.val := by positivity
  have hl := neg_le_abs (Lattice.lift x k)
  have hL := le_abs_self (w k)
  have hU := neg_le_abs (w k)
  have hp := le_abs_self (Lattice.lift x k)
  by_cases h : a<0; · have := mul_le_mul_of_nonneg_left (show a≤-1 by omega) hpos; omega
  by_cases H : a=0; · rw [H,mul_zero] at ha; omega
  have hb:=mul_le_mul_of_nonneg_left (show 1≤a by omega) hpos; omega
lemma finale_home (x y : StepPath T) (u v z : E4) (hx : Home T x u) (hy : Home T y v) (h4 : ∀ i, 4∣(T.period i).val) : Finale T x y z := by
  intro p
  have he : Tendsto (fun i=>Full.incVec (T.gap i) (rel T x i+rel T y i+p)) atTop (𝓝 (u+v)) := by simp only [straight]; simpa only [add_zero] using (Tendsto.add hx hy).add (inc_const T p)
  apply tendsto_atTop_mono' atTop _ (show Tendsto (fun i=> (T.gap i * ((T.period i).val:ℝ)) * 4⁻¹) atTop atTop from (large T).atTop_mul_const (by norm_num))
  filter_upwards [simple_bounds T he] with i hi
  let o := x i + y i + wrap (T.period i) p
  let r := (0:Axis)
  have ef : o = Full.center _ + Full.center _ + wrap _ (rel T x i+rel T y i+p) := by dsimp only [o];nth_rw 1 [position_rel T x i,position_rel T y i]; simp only [map_add]; abel
  have hf : ((T.period i).val:ℝ) ≤ 4*|(Lattice.lift o r:ℝ)| := by exact_mod_cast (dist_half (h4 i) _ _ (hi r) ef)
  have hd := PiLp.norm_apply_le (Full.incVec (T.gap i) (Lattice.lift o)) r
  rw [Real.norm_eq_abs] at hd
  change |T.gap i * (Lattice.lift o r:ℝ)| ≤ _ at hd
  rw [abs_mul,abs_of_pos (T.positive i)] at hd
  change (T.gap i* ((T.period i).val:ℝ))*4⁻¹ ≤ ‖Full.incVec _ (Lattice.lift o)‖; linarith [mul_le_mul_of_nonneg_left hf (T.positive i).le]
end YM.Pert.Align
