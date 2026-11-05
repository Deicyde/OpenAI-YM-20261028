import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Parterre
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tatami

/-!
# Specialized light controls for shell chart displacements (derivative)

Physically Smooth in marked raw output directions inside and around ball. Use
inverse normalizations relative to βhat, never multiply bounds by βhat^k
for this small shell! Allows post-S. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
open Brush  Frond 
variable {v z r Q s : ℝ} {k : ℕ} {U : E → Config G c} {x : E}

lemma shrinker {F : E → Y} (h : Brush k z v F x) (hf : ‖F x‖ ≤ s) (he : v ≤ 1) :
    Brush k (s+z*v) 1 F x := by
  apply offer.mpr; refine ⟨h.smooth,?_⟩; rintro (_|j) hj
  · exact (norm_iteratedFDeriv_zero (𝕜:=ℝ)).trans_le (hf.trans (le_add_of_nonneg_right (mul_nonneg h.nonneg h.pos)))
  apply (h.order _ hj).trans
  have hp : v^(j+1) ≤ v := by simpa only [pow_one] using pow_le_pow_of_le_one h.pos he (by omega : 1 ≤ j+1)
  exact (mul_le_mul_of_nonneg_left hp h.nonneg).trans (le_add_of_nonneg_left ((norm_nonneg _).trans hf))

lemma snaps {f : E→ℝ} {B : E→G.Color} (h : Brush k s v f x) (p : Brush k Q z B x) :
    Brush k (s*Q) (v+z) (fun i=> f i • B i) x := by
  refine (h.twins p (ContinuousLinearMap.lsmul ℝ ℝ)).climb ?_ le_rfl
  apply mul_le_of_le_one_left (mul_nonneg h.nonneg p.nonneg)
  exact ContinuousLinearMap.opNorm_lsmul_le ..

lemma inverse_mist (G : Gauge) (L : Side) : Rate G L (1/2) (fun x=> (Pressure.fiery G x L)⁻¹) := by
  refine Rate.power.compare ?_
  filter_upwards [Delay.shift_pos G L] with x hx
  let u:=Real.sqrt (Pressure.betaF G x L)
  let f:=Pressure.fiery G x L
  have he : 0 < u := Real.sqrt_pos.mpr hx
  have ht : 1 ≤ Delay.fineMonitor G L x := Real.one_le_exp (sq_nonneg _)
  have hp : u⁻¹ ≤ f := le_mul_of_one_le_right (inv_nonneg.mpr he.le) ht
  rw [← Real.sqrt_eq_rpow,abs_of_nonneg (show 0 ≤ _ from inv_nonneg.mpr ((inv_nonneg.mpr he.le).trans hp)),abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (inv_anti₀ (inv_pos.mpr he) hp).trans (inv_inv u).le

-- Costs core given K before L. Need K>0, W positive supplied by ShellAccess at x (may require if no Works yet; in void use trivial).
lemma jewelled (G : Gauge) (L : Side) (χ : Chi) {K : ℝ} (γ : ℝ) (j : ℕ) {v : ℝ→ℝ}
    (h : Rate G L (-(1/2)) v) : ∃ B : ℝ→ℝ, Rate G L (-(1/2)) B ∧ ∀ᶠ x in atTop,
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ G.El) (z:E), Brush j (royalty G) (v x) (G.mat ∘ U) z →
      let Z:=K*Pressure.fiery G x L
      Reliable G Z γ → Brush j (|B x|) 1 (fun i=>cutLog χ Z (U i)) z := by
  obtain ⟨J,d,he⟩:= cleanly G j 1 zero_lt_one
  have hu : ContDiff ℝ (↑j) χ.read := χ.smooth.of_le (show (↑(↑j:ℕ∞):WithTop ℕ∞)≤(↑(⊤:ℕ∞)) from WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C,hC,hΘ⟩ := Brush.compact (s:=Set.Icc 0 4) isCompact_Icc (fun _ _=> hu.contDiffAt)
  let m:= royalty G; let f x:= K*Pressure.fiery G x L; let D x:= (1+m)*v x
  let H x:= γ*(2*f x)+(j.factorial*J)*D x; let Y x:= (m*f x)⁻¹*((2*f x)*m+(m+m)*v x); let B x:=
    (j.factorial*C * H x)*(1+((1+Y x*Y x)*(1+1)+1))^j
  have hp : 0 < m := zero_lt_one.trans_le (royalty_ge _)
  have hf : Rate G L (-(1/2)) f := Rate.flame.mul_left K
  have hd := h.mul_left (1+m)
  refine ⟨B,?_,?_⟩
  · have hr := ((hf.mul_left 2).mul_left γ).add (hd.mul_left (j.factorial*J))
    have hh : Rate G L (1/2) (fun x=> (m*f x)⁻¹) := by
      have hk:= inverse_mist G L
      simpa only [f,_root_.mul_inv_rev] using! (hk.mul_right K⁻¹).mul_right m⁻¹
    have hY : Rate G L 0 Y := by
      convert hh.mul (((hf.mul_left 2).mul_right m).add (h.mul_left (m+m))) using 1; norm_num
    have hx := Rate.const (G:=G) (L:=L) (1:ℝ)
    have h1 : Rate G L 0 (fun x=>Y x*Y x):= (hY.mul hY).weaken (by simp)
    convert (hr.mul_left ((j.factorial:ℝ)*C)).mul ((hx.add (((hx.add h1).mul_right (1+1)).add hx)).pow j) using 1; simp
  filter_upwards [((hf.mul_left 2).mul_right m).below (by norm_num) _ he.pos,
    h.below (by norm_num) 1 zero_lt_one, hd.below (by norm_num) 1 zero_lt_one] with x hX hx ht E _ _ U z h Z hr
  have hp' : 0 < Z := hr.down
  have h₂ : v x ≤ 1 := (le_abs_self _).trans hx
  by_cases hi : G.chord (U z) ≤ 2*Z
  · let V i:= χ.innerShare Z (G.chord (U i))
    let P i := G.plog (G.mat (U i)); let c':= (j.factorial:ℝ)*C
    have hh : ‖G.mat (U z)-1‖ ≤ (2*f x)*m := (div_le_iff₀ hp).1 hi
    have hV : Brush j c' ((1+Y x*Y x)*(1+1)) V z := by
      let D (i:E) := (m*Z)⁻¹ • (G.mat (U i)-1); let f (x:E) := ‖D x‖^2
      have hp'' (i : E) : ‖D i‖ = G.chord (U i)/Z := by unfold D Gauge.chord; rw [norm_smul, Real.norm_of_nonneg (by positivity)]; unfold m royalty; ring
      have heq (i:E) : V i=χ.read (f i) := by unfold V f Chi.innerShare; rw [hp'']
      have hw : ‖D z‖≤ 2 := by rw [hp'',div_le_iff₀ hp']; exact hi
      rw [show V=(fun i=>χ.read (f i)) from funext heq]
      have hz : Brush j (Y x) 1 D z := by
        have ha:= (shrinker (h.separating (a_oneB G 1 h.pos)) hh h₂).smul ((m*Z)⁻¹); simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (m*Z)⁻¹)] using! ha
      have hh : f z ∈ Set.Icc 0 4 := ⟨sq_nonneg _,by unfold f; nlinarith [norm_nonneg (D z)]⟩
      exact (squared hz).pine (hΘ _ hh)
    have hX' : Brush j (H x) 1 P z := shrinker (h.pine (he.sound _ (hh.trans ((le_abs_self _).trans hX))))
      ((hr.cap _ hi).trans (mul_le_mul_of_nonneg_left hi hr.price.le)) ((le_abs_self _).trans ht)
    exact ((snaps hV hX').trim).climb (le_abs_self _) le_rfl
  apply Brush.shimmy (g:=fun y=> cutLog χ Z (U y)) (f:=fun _ : E=> (0:G.Color))
    ((Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl)
  have hz : ContinuousAt (fun y=> G.chord (U y)) z := ((h.smooth.continuousAt.sub_const _).norm.div_const _)
  filter_upwards [hz (lt_mem_nhds (lt_of_not_ge hi))] with y hy
  have hu : χ.innerShare Z (G.chord (U y))=0 := by
    by_contra hp; exact (χ.chosen_lt _ _ hr.down hp).not_ge (show _<_ from hy).le
  rw [cutLog,hu,zero_smul]
end YM.ConnectedActivityE6.Blaze
