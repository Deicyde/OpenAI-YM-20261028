import YM.Euclid.Stress

/-!
# No totalization in centered flux equations

The integrand of shell charges vanishes outside a compact set and is continuous
including at insertion positions (with value zero there), no extension theorem needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Table
open Function Set Filter MeasureTheory Analysis
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L} {n : ℕ}
variable {χ : E4 → ℝ}

/-- Any continuous multiplier can be included. -/
theorem integrableShell {x : Points (n+1)} (hx : x ∈ conf (n+1)) (h : Window x χ) (H : T.Smooth)
    (q : Fin (n+2) → S.Tag) (a : Axis) (W : E4 → ℂ) (Hw : Continuous W) :
    Integrable (fun y => (((Analysis.D (basis a) χ y : ℝ) : ℂ) * W y) * S.useAt T (Points.cons y x) q) := by
  rcases h with ⟨hc, hk, hp,hT⟩
  let A (y : E4) := (((Analysis.D (basis a) χ y : ℝ) : ℂ) * W y) * S.useAt T (Points.cons y x) q
  have hu := hk.fderiv ℝ
  have ht (y) : fderiv ℝ χ y = 0 → A y=0 := by intro hh; simp [A,D,hh]
  have hh : HasCompactSupport A := hu.of_isClosed_subset (isClosed_tsupport _)
    (closure_mono fun y hy => show fderiv ℝ χ y ≠ 0 from fun e => hy (ht y e))
  change Integrable A
  refine Continuous.integrable_of_hasCompactSupport ?_ hh
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases he : Points.cons y x ∈ conf (n+2)
  · have hv : ContinuousAt (fun w : E4 => S.useAt T (Points.cons w x) q) y := by
      have hm := (((S.class_smooth T H q _ he).contDiffAt ((conf_open _).mem_nhds he)).continuousAt)
      have ht : ContinuousAt (fun w : E4 => Points.cons w x) y := by
        have H1 : Continuous (fun w : E4 => (Fin.cons (α := fun _ : Fin (n+2) => E4) w x.ofLp)) :=
          continuous_pi fun k => Fin.cases (by simp; exact continuous_id) (fun j => by simp; exact continuous_const) k
        exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.continuousAt.comp H1.continuousAt
      exact hm.comp (f := fun w : E4 => Points.cons w x) ht
    unfold A
    exact ((Complex.continuous_ofReal.continuousAt.comp
      ((dSmooth (hc.contDiffAt (x := y)) (basis a) (m := ∞) (by simp)).continuousAt)).mul Hw.continuousAt).mul hv
  have hl : ∃ i, y = x i := by
    by_contra! hv
    apply he
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases (fun _ => rfl) (fun j' => ?_) j
      simp [Points.cons,hv]
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Points.cons,Ne.symm (hv i)]
    simp only [Points.cons, points_apply, Fin.cons_succ]
    exact fun hi => congr_arg Fin.succ ((show Injective x.ofLp from hx) hi)
  obtain ⟨i,rfl⟩ := hl
  refine Fin.cases ?_ (fun i => ?_) i
  · exact continuousAt_const.congr (show A =ᶠ[𝓝 (x 0)] (fun _ => (0:ℂ)) from ht0 hp).symm
  exact continuousAt_const.congr (show A =ᶠ[𝓝 (x i.succ)] (fun _ => (0:ℂ)) from ht1 i (hT i)).symm
where
  ht0 (P : χ =ᶠ[𝓝 (x 0)] (fun _ => 1)) :
      (fun y => (((Analysis.D (basis a) χ y : ℝ) : ℂ) * W y) * S.useAt T (Points.cons y x) q) =ᶠ[𝓝 (x 0)] (fun _ => 0) := by
    filter_upwards [P.fderiv (𝕜 := ℝ)] with y hy
    simp [D,hy]
  ht1 (i : Fin n) (B : x i.succ ∉ tsupport χ) :
      (fun y => (((Analysis.D (basis a) χ y : ℝ) : ℂ) * W y) * S.useAt T (Points.cons y x) q) =ᶠ[𝓝 (x i.succ)] (fun _ => 0) := by
    have H : χ =ᶠ[𝓝 (x i.succ)] fun _ => 0 := by
      filter_upwards [isOpen_compl_iff.mpr (isClosed_tsupport χ) |>.mem_nhds
        (show x i.succ ∈ (tsupport χ)ᶜ from B)] with y hy
      exact by_contra fun w => hy (subset_closure w)
    filter_upwards [H.fderiv (𝕜 := ℝ)] with y hy
    simp [D,hy]
end YM.Table
