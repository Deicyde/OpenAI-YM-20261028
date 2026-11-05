import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Recite

/-! # Request a true additional portrait on the bare tree shift ON THIS calendar

Used to move the *absolute* size of the log displacement at a no-hole
query to a gauge about the individual link. Still recenter to one
coherent station at test sets for the other physical inputs (replicated
field, plaquette/noise thresholds). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Lattice Wilson RG Precision Next Pressure Tree Bid Next.SectorChange
    AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussianLaws Heir
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {k : S.Choices} {n : ℕ} {x r Q t C : ℝ}

abbrev Signal (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (k : S.Choices) := expandBare F x ∘ forecast T x F k
abbrev Harp (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (k : S.Choices) (n : ℕ) (r Q : ℝ) := Portrait (Signal T F x k) (treeMap T F) n (temp x) r Q

lemma lessen (h : Act T F x k n t C) (ht : r ≤ t) (hC : C ≤ Q) : Act T F x k n r Q :=
  ⟨h.toTour.weaker ht hC,h.calibrated.relax ht hC (Work.E04.temp_nonneg _),fun p hp => h.visits p (hp.trans ht)⟩

private theorem resonance (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) (hn : 2 ≤ n) :
    ∃ r Q : ℝ, 0<r ∧ 0<Q ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Lift.Booth Pt S T → 100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (k : S.Choices), Harp T F x k n r Q := by
  obtain ⟨r,C,hr,hC,H⟩ := survey G P Pt hp n
  obtain ⟨u,hu,h⟩ := budget_expandBare G
  refine ⟨r,(u+1)*(C+1),hr,by positivity,?_⟩
  filter_upwards [H,dissent G P Pt hp] with x H hd c f S T hS hT hc F k
  have h0 := Work.E04.temp_nonneg x
  let L := expandBare (G:=G) F x; let g := forecast T x F k
  obtain ⟨h',h₁⟩ := hd S T hS hT hc F k; have hv := H S T hS hT.1 hc F k
  have he : DifferentiableAt ℝ g 0 := ((hv 0 (by simpa only [norm_zero] using hr.le)).smooth).differentiableAt (by exact_mod_cast (by omega : n ≠ 0))
  have h₂ : L.comp (first T F x)=treeMap T F := ContinuousLinearMap.ext (fun z => expandBare_pick T F x z)
  refine ⟨fun z hz => ((linear_through _ (hv z hz) (h S F x)).mono (by nlinarith only [hu,hC])), ?_, ?_⟩
  · change L (g 0) = _; rw [show g 0=0 from (sub_eq_zero.mp h').trans (map_zero ..),map_zero]
  rw [show fderiv ℝ (Signal T F x k) 0=L.comp (fderiv ℝ g 0) from (L.hasFDerivAt.comp 0 he.hasFDerivAt).fderiv, ← h₂, ← L.comp_sub]
  have hh : fderiv ℝ (difference T F x k) 0=fderiv ℝ g 0-first T F x := (he.hasFDerivAt.sub (first T F x).hasFDerivAt).fderiv
  refine (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul (h S F x) (hh ▸ h₁) (norm_nonneg _) hu).trans ?_)
  exact mul_le_mul_of_nonneg_right (by nlinarith only [hu,hC]) h0

theorem harmony (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) (hn : 2 ≤ n) :
    ∃ r Q : ℝ, 0<r ∧ 1≤Q ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Lift.Booth Pt S T → 100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (k : S.Choices), Act T F x k n r Q ∧ Harp T F x k n r Q := by
  obtain ⟨r,Q,hr,hQ,h⟩ := recital G P Pt hp n hn
  obtain ⟨s,C,hs,-,hC⟩ := resonance G P Pt hp n hn
  refine ⟨min r s,max Q C,lt_min hr hs,hQ.trans (le_max_left ..),?_⟩
  filter_upwards [h,hC] with x h hC c f S T hS hT hc F k
  exact ⟨lessen (h S T hS hT hc F k) (min_le_left ..) (le_max_left ..), (hC S T hS hT hc F k).relax (min_le_right ..) (le_max_right ..) (Work.E04.temp_nonneg _)⟩
end YM.PhysicalNext.JointLoad.Psalm
