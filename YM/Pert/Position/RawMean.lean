import YM.Pert.FirstTarget
import YM.Pert.Lattice.Lifts
/-! Weak limit on arbitrary compact-profile tapes along the *same* extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Position
open Function Filter Set MeasureTheory Measure Analysis RawLabels Table Org Maxwell Next.UVStress Climb Spec Ward
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}
variable {d r : ℕ}

def bundle (p : Fin r → (freeTable C.labels).Field d) (t : Points r→ℂ) := ∫ x : Points r, t x * disc (fun i => (⟨d,p i⟩:(freeTable C.labels).Tag)) x

def swivel (X : Climb.Scaling S) (k : ℕ) (p : Fin r → (freeTable C.labels).Field d) (x : Points r) :=
   disc (fun i => (⟨d,(X.U k d) (p i)⟩:S.Tag)) ((X.r k : ℝ) • x)
lemma swivel_smooth (hS : S.Smooth) (X : Climb.Scaling S) (k : ℕ) (v : Fin r → (freeTable C.labels).Field d) : ContinuousOn (swivel X k v) (conf r) :=
  (S.class_smooth S hS (fun i => (⟨d,(X.U k d) (v i)⟩:S.Tag))).continuousOn.comp (g:=fun x => disc (fun i => (⟨d,(X.U k d) (v i)⟩:S.Tag)) x) (f:=fun x => (X.r k:ℝ) • x) (ContinuousOn.const_smul (show ContinuousOn id (conf r) from continuousOn_id) (X.r k)) (fun _ hx _ _ he => (hx : Injective _ ) (smul_right_injective E4 (X.positive k).ne' he))

def exactMean (X : Climb.Scaling S) (k : ℕ) (p : Fin r → (freeTable C.labels).Field d) (t : Points r→ℂ) := ∫ x : Points r, t x * swivel X k p x

lemma paired_limit (t : Test r) {F : ℕ → Points r → ℂ} {G : Points r → ℂ} (hf : ∀ i, ContinuousOn (F i) (conf r)) (hg : ContinuousOn G (conf r))
  (h : ∀ δ : ℝ, 0<δ → ∀ᶠ i in atTop, ∀ x∈ tsupport t, ‖(F i-G) x‖ ≤ δ) : Tendsto (fun i=>t.applyTo (F i)) atTop (𝓝 (t.applyTo G)) := by
  have hi : Integrable (fun x => ‖t x‖) := (t.continuous.integrable_of_hasCompactSupport t.hasCompactSupport).norm
  refine Metric.tendsto_nhds.mpr fun ε he => ?_
  let N := ∫ x, ‖t x‖
  have nn : 0≤N := integral_nonneg (fun _=> norm_nonneg _)
  let δ := ε/(N+1)
  have hd : 0<δ := div_pos he (by linarith)
  refine (h _ hd).mono fun i hi' => ?_
  have hv : ∀ x, ‖t x * (F i-G) x‖ ≤ ‖t x‖ * δ := fun x=> by
    by_cases hx : x∈ tsupport t
    · grw [norm_mul_le _ _,hi' _ hx]
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [dist_eq_norm,← Next.UVStress.test_sub _ _ (hf i) hg]
  have h' := (norm_integral_le_integral_norm (fun x=> t x*(F i-G) x)).trans (integral_mono (t.smearing ((hf i).sub hg) |>.norm) (hi.mul_const δ) hv)
  rw [integral_mul_const] at h'
  refine h'.trans_lt ?_; dsimp [Test.applyTo,δ]; calc
     N * (ε/(N+1)) = (N/(N+1))*ε := by ring
     _ < 1*ε := mul_lt_mul_of_pos_right ((div_lt_one (by positivity)).mpr (by linarith)) he
     _ = _ := one_mul _

lemma exact_tape {b : Final C F S} (X : Climb.Scaling S) (h : FirstExtension b X) (p : Fin r → (freeTable C.labels).Field d) (t : Test r) : Tendsto (fun k=>exactMean X k p t) atTop (𝓝 (bundle p t)) := by
  have he := paired_limit t (fun k => swivel_smooth b.room.kernel.smooth X k p) ((freeTable C.labels).class_smooth _ (table_smooth _) (fun i => (⟨d,p i⟩:(freeTable C.labels).Tag)) |>.continuousOn)
  refine he (fun e he => ?_)
  let q := fun i => (⟨d,p i⟩:(freeTable C.labels).Tag)
  have h1 : freeWithStress C.labels q (fun _ => false) (fun _ : Fin r => (⟨0,0⟩:Axis × Axis)) = q := funext fun i=> by simp [freeWithStress]
  have h2 k : scaledPhysical X b.sector.energy k q (fun _ => false) (fun _ : Fin r => (⟨0,0⟩:Axis × Axis)) = fun i=> (⟨d,(X.U k d) (p i)⟩:S.Tag) := funext fun i=> by simp [scaledPhysical,q]
  filter_upwards [h.jets r 0 q (fun _=>false) (fun _=> ⟨0,0⟩) t.hasCompactSupport t.tsupport_subset he] with k hk x hx
  have ht := hk x hx
  rw [h1,h2] at ht
  let u := fun x : Points r => swivel X k p x - disc q x
  convert! (show ‖iteratedFDeriv ℝ 0 u x‖ = ‖u x‖ from norm_iteratedFDeriv_zero (𝕜:=ℝ)) ▸ (show ‖iteratedFDeriv ℝ 0 u x‖ ≤ e from ?_) using 1
  rw [show iteratedFDeriv ℝ 0 u x = iteratedFDeriv ℝ 0 (swivel X k p) x - iteratedFDeriv ℝ 0 (disc q) x by ext1 v; rfl]; exact ht
end YM.Pert.Position
