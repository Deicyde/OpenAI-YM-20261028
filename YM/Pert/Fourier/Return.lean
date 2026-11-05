import YM.Pert.Fourier.Temper
/-! Separated matching of the direct scalar difference through any finite list of directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open Topology Filter Metric Lattice MeasureTheory YM.Next.Rank.Radian Set
open scoped BigOperators Classical RealInnerProductSpace

lemma telescope {F : ℝ→ℂ} {w h : ℕ→ℝ} {C s : ℝ} (hs : s>0) (hw : ∀ i, w i = C/(2^i*s)) (L : ∀ i:ℕ, dist (F (2*(2^i*s))) (F (2^i*s)) ≤ w i) (k : ℕ) :
  dist (F (2^k*s)) (F s) ≤ 2*(1-(1/2:ℝ)^k)*(C/s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := Real.pi_pos
    convert! le_trans (dist_triangle _ (F ((2:ℝ)^k*s)) (F s)) (add_le_add (L k) ih) using 1
    · congr 1; rw [pow_succ];ring
    rw [hw, pow_succ,one_div,inv_pow]; field_simp [(show (2:ℝ)^k≠0 from by positivity)];ring
lemma temp_estimate (D : List Axis) (z : E4) (hz : z≠0) : ∃ C≥0, ∀ (s b : ℝ), s>0 → b>0 → dist (harmon (press D (liturgy b)) z) (mild D s b z) ≤ 2*C/s := by
  obtain ⟨C,hCp,H⟩ := precious_upper D z hz
  refine ⟨C,hCp,fun s b hs hb=>?_⟩
  apply le_of_tendsto ((mild_fresh D s b hs hb z).dist tendsto_const_nhds) (Eventually.of_forall ?_); intro k
  refine (le_trans (b:=2*(1-(1/2:ℝ)^k)*(C/s)) (telescope (F:=fun t=>mild D t b z) (w:=fun i=>C/(2^i*s)) (h:=fun _=>b) hs (fun _=>rfl) (fun i=>?_ ) _) ?_)
  · rw [dist_eq_norm, mild_step D _ _ (by positivity) hb.le]; exact H _ b (by positivity) hb.le
  have e : ((1/2:ℝ)^k)*(C/s) ≥ 0 := by positivity
  rw [mul_div_assoc]; nlinarith only [e]
lemma mild_heat (D : List Axis) (s : ℝ) (hs : s>0) (z : E4) : Tendsto (fun j=>mild D s (UVHeat j) z) atTop (𝓝 (mild D s 0 z)) := by
  unfold mild; let f k := Real.exp 1 * ‖wave z k * press D (liturgy (factor s ^ 2)) k‖
  apply tendsto_integral_of_dominated_convergence (μ:=volume) (F:=fun i=> tonic D s (UVHeat i) z) f (fun i=> (tonic_int D s _ hs (UVHeat_pos _).le z).aestronglyMeasurable)
  · simpa [f, YM.Next.Rank.Radian.wave] using ((Moment.pressed D (passion (sq_pos_of_pos (factor_pos _ hs)))).integral.norm.const_mul (Real.exp 1))
  · intro i; let τ := UVHeat i; refine Eventually.of_forall fun k=>?_
    by_cases h : 1 < ‖radial D s k‖
    · unfold tonic; rw [disk_out h.le]; simp [f]; positivity
    simpa only [tonic,f, norm_mul,YM.Next.Rank.Radian.wave,Circle.norm_coe,one_mul] using le_trans (mul_le_of_le_one_right (norm_nonneg (press D _ k)) (disk_always (radial D s k))) (press_cost D s τ hs (UVHeat_pos _).le k (le_of_not_gt h))
  apply Eventually.of_forall
  intro k; have he (D : List Axis) : Tendsto (fun j=>press D (liturgy (UVHeat j)) k) atTop (𝓝 (press D (liturgy 0) k)) := by
    refine (Continuous.continuousAt (x:=(0:ℝ)) (f:=fun b=>press D (liturgy b) k) ?_).tendsto.comp UVHeat_zero
    show Continuous (fun v : ℝ=>press D (liturgy v) k)
    induction D with
    | nil => simp [press,liturgy,major];fun_prop
    | cons a D IH=> apply continuous_const.mul IH
  exact (tendsto_const_nhds.mul (he D)).mul (tendsto_const_nhds (x:=(disk (radial D s k):ℂ)))
lemma c_estimate (D : List Axis) (z : E4) (hz : z≠0) : ∃ B≥0,∃ C≥0, ∀ {s : ℝ}, s>0 → ‖mild D s 0 z‖ ≤ s^(D.length+2)*B ∧ dist (casual D z) (mild D s 0 z) ≤ C/s := by
  obtain ⟨C,hC,H⟩ := temp_estimate D z hz
  refine ⟨_,(show 0 ≤ (∫ k, Real.exp 1 * ‖wave z k * press D (liturgy (turn^2)) k‖) from integral_nonneg fun i=> by positivity),2*C,by positivity,fun {s} hs=>⟨precious_lower _ _ _ hs le_rfl z,?_⟩⟩
  exact le_of_tendsto ((off_zero_moll D z hz).dist (mild_heat D s hs z)) (Eventually.of_forall fun i=> H s (UVHeat i) hs (UVHeat_pos i))

lemma approach {F : ℕ→ℝ→ℂ} {A : ℝ→ℂ} (H : ∀ s>0, Tendsto (fun i=> F i (2*s)-F i s) atTop (𝓝 (A (2*s)-A s))) (k : ℕ) (s) (hs : s>0) : Tendsto (fun i=>F i ((2:ℝ)^k*s)-F i s) atTop (𝓝 (A ((2:ℝ)^k*s)-A s)) := by
  induction k with
  | zero => simpa using tendsto_const_nhds  -- wrong tag
  | succ k ih => convert! (H ((2:ℝ)^k*s) (by positivity)).add ih using 1 <;> simp only [pow_succ,mul_left_comm,mul_comm,sub_add_sub_cancel] -- cancellations

lemma enlarged_clock (C : ℝ) (hC : 0≤C) (s : ℝ) (hs : s>0) (ε : ℝ) (he : ε>0) : ∃ k:ℕ, C/(2^k*s)< ε := by
  have hv := tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℝ) by norm_num)
  obtain ⟨k,hk⟩ := (hv.eventually (eventually_gt_atTop (C/(ε*s)))).exists
  exact ⟨k,(div_lt_iff₀ (by positivity)).2 (by have ht := (div_lt_iff₀ (by positivity : 0<ε*s)).1 hk; linarith only [ht])⟩
lemma wrap_tube {F : ℕ→ℂ} {cash : ℕ→ℝ→ℂ} {graph : ℝ→ℂ} {g : ℂ} (d : ℕ) (hv : ∀ s>0, Tendsto (fun i=>cash i (2*s)-cash i s) atTop (𝓝 (graph (2*s)-graph s)))
    (Hl : ∃ C≥0,∃ B≥0, ∀ s>0,∀ᶠ i in atTop, ‖cash i s‖ ≤ s^d*s*C ∧ dist (F i) (cash i s) ≤ B/s)
    (Hh : ∃ C≥0,∃ B≥0, ∀ s>0, ‖graph s‖ ≤ s^d*s*C ∧ dist g (graph s) ≤ B/s) : Tendsto F atTop (𝓝 g) := by
  rw [Metric.tendsto_atTop]; intro ε he; have hp : 0<ε/3 := by positivity
  obtain ⟨C,hCp,B,hBp,H⟩ := Hl; obtain ⟨E,hEp,D,hDp,L⟩ := Hh
  let s:=min (1:ℝ) (((ε/3)/(E+C+1)))
  have hs : 0<s := lt_min zero_lt_one (by apply div_pos hp (by linarith))
  have hlow : s^d*s*(C+E) ≤ ε/3 := by
    have he : s^d ≤ 1 := pow_le_one₀ hs.le (min_le_left ..)
    grw [he,show s≤(ε/3)/(E+C+1) from min_le_right ..,one_mul]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by linarith)]; nlinarith only [he,hp] -- nonexistent.
  obtain ⟨q,hq⟩ := enlarged_clock (B+D) (add_nonneg hBp hDp) s hs _ hp
  let S:=(2:ℝ)^q*s
  have hsmall := (approach (F:=cash) hv q s hs).dist (tendsto_const_nhds (x:=graph S-graph s))
  apply Filter.eventually_atTop.mp
  filter_upwards [H s hs, H S (by unfold S; positivity), hsmall.eventually (gt_mem_nhds (lt_of_eq_of_lt (dist_self _) hp))] with i hi hI hc
  let b:=cash i S; let c:=cash i s; let a:=graph S; let u:=graph s
  have ht := dist_triangle (F i) b g; have hu := dist_triangle b a g
  have hl : dist c u ≤ ‖c‖+‖u‖ := by simpa using (dist_triangle (α:=ℂ) c 0 u)
  have ha := (L _ (show 0 < S from mul_pos (by positivity) hs)); have hb := L s hs
  change dist (b-c) (a-u) < ε/3 at hc
  have hab : dist b a ≤ dist (b-c) (a-u) + dist c u := by simpa using dist_add_add_le (b - c) c (a - u) u
  rw [dist_comm a g] at hu
  apply lt_of_le_of_lt ht (add_lt_add_of_le_of_lt hI.2 (lt_of_le_of_lt hu (add_lt_add_of_lt_of_le (lt_of_le_of_lt hab (add_lt_add_of_lt_of_le hc (hl.trans (add_le_add hi.1 hb.1)))) ha.2))) |> fun h=>h.trans_le ?_
  calc _ = (B+D)/S + (ε / 3+s^d*s*(C+E)) := by unfold S;ring
                       _ ≤ _ := by apply le_trans (add_le_add hq.le (add_le_add (show ε/3 ≤ ε/3 from le_rfl) hlow)) (le_of_eq (by ring))

variable (n c : ℕ→Side) (h : ℕ→ℝ) (D : List Axis) (x : ∀ i, Site (n i))
lemma mesh_light (hc : ∀ i, (c i).val=((n i).val:ℝ)* h i) (hv : Tendsto (fun i=>(c i).val) atTop atTop) (s : ℝ) (hs : 0<s) : ∀ᶠ i in atTop, Full.mesh (n i) * ((D.length+4:ℕ):ℝ) ≤ h i*s := by
  filter_upwards [((tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp hv).eventually (eventually_ge_atTop (turn*((D.length:ℝ)+4)/s)))] with i hi
  unfold Full.mesh; push_cast; rw [div_mul_eq_mul_div,div_le_iff₀ (Full.val_pos _)]; have H := (div_le_iff₀ (by positivity : 0<s)).1 (show turn*((D.length:ℝ)+4)/s≤ (c i).val from hi); rw [hc] at H; linarith only [H]
lemma hbound (he : Tendsto h atTop (𝓝 0)) (s : ℝ) : ∀ᶠ i in atTop, h i * s ≤ 1/2 := (he.mul_const s).eventually (ge_mem_nhds (by simp))
lemma initial_estimate (hc : ∀ i, (c i).val=((n i).val:ℝ)* h i) (hh : ∀ i, 0<h i) (hv : Tendsto (fun i=>(c i).val) atTop atTop) (he : Tendsto h atTop (𝓝 0))
    (hz : ∃ R>0,∀ᶠ i in atTop, R ≤ ‖Full.incVec (h i) (Lattice.lift (x i))‖) : ∃ C≥0,∃ B≥0,∀ s>0,∀ᶠ i in atTop, ‖piece (h i) s D (x i)‖ ≤ s^(D.length+1)*s*C ∧ dist (joint (h i) D (x i)) (piece (h i) s D (x i)) ≤ B/s := by
  obtain ⟨R,hR,h⟩ := hz; obtain ⟨B,hB,H⟩ := upper_tail D R hR; refine ⟨purse,by unfold purse; positivity,B,hB.le,fun s hs=>?_⟩
  filter_upwards [hbound _ he s, mesh_light n c _ D hc hv s hs, h] with i hi h' ht
  rw [dist_eq_norm]
  have e := H (hh i) hs hi h' (x i) ht
  exact ⟨le_trans (lower _ _ hs (hh i) (by linarith) (x i) D) (le_of_eq (by ring)),e⟩
lemma joint_casual {z : E4} (hz : z≠0) (hc : ∀ i, (c i).val=((n i).val:ℝ)* h i) (hh : ∀ i, 0<h i) (hv : Tendsto (fun i=>(c i).val) atTop atTop) (he : Tendsto h atTop (𝓝 0))
    (hxy : Tendsto (fun i=>Full.incVec (h i) (Lattice.lift (x i))) atTop (𝓝 z)) : Tendsto (fun i=>joint (h i) D (x i)) atTop (𝓝 (casual D z)) := by
  have hw := initial_estimate n c h D x hc hh hv he ⟨‖z‖/2,half_pos (norm_pos_iff.mpr hz),hxy.norm.eventually (le_mem_nhds (half_lt_self (norm_pos_iff.mpr hz)))⟩
  apply wrap_tube (cash:=fun i s => piece (h i) s D (x i)) (graph:=fun s=>mild D s 0 z) (D.length+1) (fun s hs=>?_ ) hw
  · obtain ⟨C,hCp,B,hBp,H⟩ := c_estimate D z hz
    refine ⟨C,hCp,B,hBp,fun s hs=>?_⟩; rw [show s^(D.length+1)*s=s^(D.length+2) from rfl]; exact H hs
  rw [mild_step _ _ _ hs le_rfl]; exact corona_limit n c h x hc hh hv he hxy D s hs
end YM.Pert.Band
