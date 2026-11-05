import YM.Euclid.Window
import YM.Org.Input

/-!
Shell geometry: one compact shell (in variables of the weak test),
also used at its physical scale; Jacobian in four dimensions. Fit the
whole testing set including moving stress point into a Track window.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A05
open Set Function Filter Analysis MeasureTheory Table Ward Climb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n : ℕ}

lemma has_window (x : Points (n+1)) (hx : x ∈ conf (n+1)) : ∃ χ, Table.Window x χ := by
  let A := Set.range fun i : Fin n => x i.succ
  have ho : IsOpen Aᶜ := (Set.finite_range _).isClosed.isOpen_compl
  have hz : x 0 ∈ Aᶜ := by
    rintro ⟨i,hi⟩
    exact Fin.succ_ne_zero _ (hx hi)
  obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hz)
  let B : ContDiffBump (x 0) := ⟨r/4,r/2,by positivity,by linarith⟩
  refine ⟨B,B.contDiff,B.hasCompactSupport,B.eventuallyEq_one,?_⟩
  intro i hh
  rw [B.tsupport_eq] at hh
  exact hb (Metric.closedBall_subset_ball (show B.rOut < r from half_lt_self hr) hh) ⟨i,rfl⟩

lemma smul_cons (r : ℝ) (x : Points n) (y : E4) :
    r • Points.cons y x = Points.cons (r • y) (r • x) := by
  apply PiLp.ext; intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons]

lemma smul_conf {r : ℝ} (hr : 0 < r) {x : Points n} (hx : x ∈ conf n) : r • x ∈ conf n := by
  intro i j hij
  exact hx (smul_right_injective E4 hr.ne' hij)

/-- Topological support of the shell derivative avoids all insertion points. -/
lemma window_avoids (x : Points (n+1)) {χ : E4 → ℝ} (hw : Window x χ) :
    ∀ i, x i ∉ tsupport (fderiv ℝ χ) := by
  intro i
  apply notMem_tsupport_iff_eventuallyEq.mpr
  refine Fin.cases ?_ (fun j => ?_) i
  · have ht := hw.2.2.1.fderiv (𝕜 := ℝ)
    change fderiv ℝ χ =ᶠ[𝓝 (x 0)] fderiv ℝ (Function.const E4 (1:ℝ)) at ht
    simpa only [fderiv_const] using ht
  · have hj := notMem_tsupport_iff_eventuallyEq.mp (hw.2.2.2 j)
    have ht := hj.fderiv (𝕜 := ℝ)
    simpa using ht

lemma window_cons_conf {x : Points (n+1)} (hx : x ∈ conf (n+1)) {χ : E4 → ℝ} (hw : Window x χ)
    {y} (hy : y ∈ tsupport (fderiv ℝ χ)) : Points.cons y x ∈ conf _ := by
  have he (i) : y ≠ x i := fun h => window_avoids x hw i (h ▸ hy)
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j => ?_) j
    simp [Points.cons,he]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Points.cons,Ne.symm (he i)]
  simp only [Points.cons, points_apply, Fin.cons_succ]
  exact fun hi => congr_arg Fin.succ ((show Injective x.ofLp from hx) hi)

/-- Every compact separated test eventually fits these windows (no
condition `2 ≤ n`). -/
lemma compact_fits {K : Set (Points n)} (hK : IsCompact K) (hk : K ⊆ conf n) :
    ∀ᶠ R : ℝ in atTop, K ⊆ Scaling.window R n := by
  have hp (i j : Fin n) : ∀ᶠ R : ℝ in atTop, ∀ x ∈ K, i ≠ j → R⁻¹ ≤ cubedist (x i) (x j) := by
    by_cases e : i = j
    · subst j; simp
    let f := fun x : Points n => cubedist (x i) (x j)
    have hf : Continuous f := by
      exact continuous_cubedist.comp (show Continuous (fun x : Points n => (x i,x j)) by fun_prop)
    have hx (x) (h : x ∈ K) : 0 < f x :=
      dist_pos.mpr (fun he => e ((hk h) ((WithLp.ofLp_injective 2) he)))
    obtain ⟨A,hA⟩ := (hK.image_of_continuousOn (hf.continuousOn.inv₀ (fun x h => (hx x h).ne'))).bddAbove
    filter_upwards [eventually_ge_atTop A] with r hr x hx' _
    exact inv_le_of_inv_le₀ (hx x hx') ((hA (mem_image_of_mem _ hx')).trans hr)
  obtain ⟨A,hA⟩ := (hK.image continuous_norm).bddAbove
  have hh : ∀ᶠ R : ℝ in atTop, ∀ (i j : Fin n), ∀ x ∈ K, i ≠ j → R⁻¹ ≤ cubedist (x i) (x j) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => hp i j
  filter_upwards [hh,eventually_ge_atTop A] with r hs hv x hx
  exact ⟨fun i j => hs i j x hx,(hA (mem_image_of_mem _ hx)).trans hv⟩

lemma shell_fits {x : Points (n+1)} (hx : x ∈ conf (n+1)) {χ : E4 → ℝ} (hw : Window x χ) :
    ∀ᶠ R : ℝ in atTop, ∀ y ∈ tsupport (fderiv ℝ χ), Points.cons y x ∈ Scaling.window R _ := by
  let f (y : E4) := Points.cons y x
  have hf : Continuous f := by
    have hp : Continuous (fun w : E4 => Fin.cons (α := fun _ : Fin (n+2) => E4) w x.ofLp) :=
      continuous_pi fun k => Fin.cases (by simp; exact continuous_id) (fun j => by simp; exact continuous_const) k
    exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.comp hp
  let E := tsupport (fderiv ℝ χ)
  have hc : IsCompact E := hw.2.1.fderiv ℝ
  have ht : f '' E ⊆ conf _ := by
    rintro _ ⟨y,hy,rfl⟩; exact window_cons_conf hx hw hy
  filter_upwards [compact_fits (hc.image hf) ht] with r he y hy
  exact he ⟨y,hy,rfl⟩

/-- Send χ on weak-coordinate space to physical space. -/
def stretch (r : ℝ) (χ : E4 → ℝ) (y : E4) := χ (r⁻¹ • y)

lemma window_stretch {r : ℝ} (hr : 0 < r) {x : Points (n+1)} {χ : E4 → ℝ} (hw : Window x χ) :
    Window (r • x) (stretch r χ) := by
  let l (y : E4) := r⁻¹ • y
  have hl : ContDiff ℝ ∞ l := by
    unfold l; fun_prop
  have ht (i : Fin (n+1)) : Tendsto l (𝓝 ((r • x) i)) (𝓝 (x i)) := by
    have he : l ((r • x) i) = x i := inv_smul_smul₀ hr.ne' _
    exact he ▸ hl.continuous.continuousAt.tendsto
  refine ⟨hw.1.comp hl, hw.2.1.comp_smul (inv_ne_zero hr.ne'), hw.2.2.1.comp_tendsto (ht 0),?_⟩
  intro i
  exact notMem_tsupport_iff_eventuallyEq.mpr
    ((notMem_tsupport_iff_eventuallyEq.mp (hw.2.2.2 i)).comp_tendsto (ht i.succ))

lemma D_stretch {r : ℝ} (hr : 0 < r) {χ : E4 → ℝ} (hc : ContDiff ℝ ∞ χ) (a : Axis) (y : E4) :
    Analysis.D (basis a) (stretch r χ) (r • y) = r⁻¹ * Analysis.D (basis a) χ y := by
  let l : E4 →L[ℝ] E4 := r⁻¹ • ContinuousLinearMap.id ℝ E4
  change fderiv ℝ (χ ∘ l) (r • y) (basis a) = _
  rw [fderiv_comp (r • y) (hc.differentiable (by simp) _) l.differentiableAt, l.fderiv]
  change fderiv ℝ χ (r⁻¹ • (r • y)) (r⁻¹ • basis a) = _
  rw [inv_smul_smul₀ hr.ne',map_smul]; rfl

def weight (χ : E4 → ℝ) (a : Axis) (W : E4 → ℝ) (y : E4) : ℂ :=
  (Analysis.D (basis a) χ y * W y : ℝ)

lemma integrable_weight {χ W : E4 → ℝ} (hc : ContDiff ℝ ∞ χ) (hx : HasCompactSupport χ)
    (a : Axis) (hW : Continuous W) : Integrable (weight χ a W) := by
  let f := Analysis.D (basis a) χ
  have hf : Continuous f := (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hF : HasCompactSupport f := hx.fderiv_apply ℝ (basis a)
  exact (Complex.continuous_ofReal.comp (hf.mul hW)).integrable_of_hasCompactSupport
    ((hF.mul_right (f' := W)).comp_left (show Complex.ofReal 0 = 0 by simp))

variable {G : Gauge} {L : Register G} {S : Table L}

def sheet (r : ℝ) (χ : E4 → ℝ) (a : Axis) (W : E4 → ℝ) (x : Points (n+1)) (q : Fin (n+2) → S.Tag)
    (y : E4) : ℂ := weight χ a W y * disc q (r • Points.cons y x)

lemma sheet_scaled {r : ℝ} (hr : 0 < r) (x : Points (n+1)) (q : Fin (n+2) → S.Tag) {χ : E4 → ℝ}
    (hc : ContDiff ℝ ∞ χ) (a : Axis) (W : E4 → ℝ) (y : E4) :
    sheet 1 (stretch r χ) a (stretch r W) (r • x) q (r • y) =
      (r : ℂ)⁻¹ * sheet r χ a W x q y := by
  simp only [sheet, one_smul, weight, ← smul_cons, D_stretch hr hc, stretch, inv_smul_smul₀ hr.ne',
    Complex.ofReal_mul, Complex.ofReal_inv, mul_assoc]

lemma integrable_sheet {r : ℝ} (hr : 0 < r) (x : Points (n+1)) (hx : x ∈ conf _)
    (H : S.Smooth) (q : Fin (n+2) → S.Tag) {χ W : E4 → ℝ} (hw : Window x χ) (a : Axis) (hW : Continuous W) :
    Integrable (sheet r χ a W x q) := by
  let P := sheet 1 (stretch r χ) a (stretch r W) (r • x) q
  have hp : Continuous (stretch r W) := hW.comp (show Continuous (fun x : E4 => r⁻¹ • x) by fun_prop)
  have hP : Integrable P := by
    have hu := integrableShell (smul_conf hr hx) (window_stretch hr hw) H q a
      (Complex.ofReal ∘ stretch r W) (Complex.continuous_ofReal.comp hp)
    change Integrable (fun y => sheet 1 (stretch r χ) a (stretch r W) (r • x) q y)
    simpa only [sheet,one_smul,weight, Complex.ofReal_mul,comp_apply,disc] using hu
  have he : sheet r χ a W x q = fun y => (r : ℂ) * P (r • y) := by
    funext y; dsimp only [P]; rw [sheet_scaled hr _ q hw.1,mul_inv_cancel_left₀ (by exact_mod_cast hr.ne')]
  rw [he]; exact (hP.comp_smul hr.ne').const_mul (r : ℂ)

lemma integrate_sheet_scale {r : ℝ} (hr : 0 < r) (x : Points (n+1)) (q : Fin (n+2) → S.Tag)
    {χ : E4 → ℝ} (hc : ContDiff ℝ ∞ χ) (a : Axis) (W : E4 → ℝ) :
    ∫ z, sheet 1 (stretch r χ) a (stretch r W) (r • x) q z =
      (r : ℂ)^3 * ∫ y, sheet r χ a W x q y := by
  let P := sheet 1 (stretch r χ) a (stretch r W) (r • x) q
  have hp (y : E4) : P (r • y) = (r : ℂ)⁻¹ * sheet r χ a W x q y := sheet_scaled hr x q hc a W y
  have ht := Measure.integral_comp_smul_of_nonneg volume P r (hR := hr.le)
  simp_rw [hp] at ht
  rw [integral_const_mul,show Module.finrank ℝ E4 = 4 from finrank_euclideanSpace_fin,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow] at ht
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  change (∫ z, P z) = _
  calc
    _ = (r : ℂ)^4 * (((r : ℂ)^4)⁻¹ * ∫ z, P z) := (mul_inv_cancel_left₀ (pow_ne_zero _ hn) _).symm
    _ = _ := by rw [← ht]; field_simp

def arm (x : Points (n+1)) (g : Ortho.Skew) (b : Axis) (z : E4) := M4.move g.val (z - x 0) b

lemma arm_continuous (x : Points (n+1)) (g : Ortho.Skew) (b : Axis) : Continuous (arm x g b) := by
  change Continuous (fun z => arm x g b z)
  simp only [arm, M4.at_coord]; fun_prop

lemma arm_scaled {r : ℝ} (hr : 0 < r) (x : Points (n+1)) (g : Ortho.Skew) (b : Axis) (z : E4) :
    arm (r • x) g b z = r * stretch r (arm x g b) z := by
  have he : z - (r • x) 0 = r • (r⁻¹ • z - x 0) := by
    rw [smul_sub, smul_inv_smul₀ hr.ne']; rfl
  unfold stretch arm
  rw [he]; unfold M4.move; rw [map_smul]; rfl
end YM.Work.A05
