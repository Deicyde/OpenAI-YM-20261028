import YM.Work.A05.Read
import YM.Work.A05.Window


/-!
Pass the shell integrals *on the same Track*. First hold the stress slot
open, obtaining convergence of linear maps, then plug in the *normalized*
stress (metered in weak coordinates). We only need order zero of the
uniform-on-window jet bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A05
open Set Function Filter Analysis MeasureTheory Table Ward Climb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

/-- Curried in the stress slot. In these lemmas `v` is the whole remaining
word, including the insertion at `x 0`. -/
def reader (r : ℝ) (hr : 0 < r) (x : Points (n+1)) (hx : x ∈ conf _) (H : S.Smooth)
    {χ W : E4 → ℝ} (hw : Window x χ) (a : Axis) (hW : Continuous W) (v : Fin (n+1) → S.Tag) :
    S.Field 4 →ₗ[ℂ] ℂ where
  toFun u := ∫ y, sheet r χ a W x (Fin.cons ⟨4,u⟩ v) y
  map_add' p q := by
    have he y : sheet r χ a W x (Fin.cons ⟨4,p+q⟩ v) y =
        sheet r χ a W x (Fin.cons ⟨4,p⟩ v) y + sheet r χ a W x (Fin.cons ⟨4,q⟩ v) y := by
      unfold sheet
      simp_rw [← frontRead_at, map_add, mul_add]
    simp_rw [he]; exact integral_add (integrable_sheet hr x hx H _ hw a hW)
      (integrable_sheet hr x hx H _ hw a hW)
  map_smul' c p := by
    have he y : sheet r χ a W x (Fin.cons ⟨4,c • p⟩ v) y =
        c * sheet r χ a W x (Fin.cons ⟨4,p⟩ v) y := by
      unfold sheet
      simp_rw [← frontRead_at,map_smul,smul_eq_mul]; ring
    simp_rw [he]; exact integral_const_mul c _

lemma tendsto_sheet (X : Scaling S) (H : S.Smooth) (H' : (Bel L).Smooth)
    (x : Points (n+1)) (hx : x ∈ conf _) {χ W : E4 → ℝ} (hw : Window x χ) (a : Axis) (hW : Continuous W)
    {N D m : ℕ} {R : ℝ} (hh : X.jets N D m R) (hn : n+2 ≤ N)
    (ht : ∀ y ∈ tsupport (fderiv ℝ χ), Points.cons y x ∈ Scaling.window R _)
    (v : Fin (n+2) → (Bel L).Tag) (hv : ∀ i, (v i).1 ≤ D) :
    Tendsto (fun k => ∫ y, sheet (X.r k) χ a W x (X.pins k ∘ v) y) atTop
      (𝓝 (∫ y, sheet 1 χ a W x v y)) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  let f (y : E4) := ‖weight χ a W y‖
  let T := ∫ y : E4, f y
  have hF : Integrable f := (integrable_weight hw.1 hw.2.1 a hW).norm
  have hT : 0 ≤ T := integral_nonneg (fun y => norm_nonneg _)
  let δ := ε / (T + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [value_bound X hh hn v hv hδ] with k hk
  let B := sheet (X.r k) χ a W x (X.pins k ∘ v)
  let C := sheet 1 χ a W x v
  have hB : Integrable B := integrable_sheet (X.positive k) x hx H _ hw a hW
  have hC : Integrable C := integrable_sheet one_pos x hx H' _ hw a hW
  have hz (y : E4) : ‖B y - C y‖ ≤ f y * δ := by
    by_cases h : y ∈ tsupport (fderiv ℝ χ)
    · dsimp only [B,C,sheet,f]; rw [one_smul,← mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (hk _ (ht y h)) (norm_nonneg _)
    have he : weight χ a W y=0 := by simp [weight,Analysis.D,image_eq_zero_of_notMem_tsupport h]
    simp [B,C,sheet,f,he]
  rw [dist_eq_norm]
  change ‖(∫ y, B y)-(∫ y, C y)‖ < ε
  rw [← integral_sub hB hC]
  calc
    _ ≤ ∫ y, ‖B y - C y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, f y * δ := integral_mono (hB.sub hC).norm (hF.mul_const _) hz
    _ = T * δ := integral_mul_const ..
    _ < (T+1)*δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by dsimp only [δ]; field_simp

/-- One normalized integral entry, with a multiplier given in the weak
coordinate variables. -/
lemma reaches_stress (X : Scaling S) (H : S.Smooth) (H' : (Bel L).Smooth)
    {J : S.Stress} {T : (Bel L).Stress} (hc : X.meter J T)
    (x : Points (n+1)) (hx : x ∈ conf _) {χ W : E4 → ℝ} (hw : Window x χ) (a b : Axis) (hW : Continuous W)
    {N D m : ℕ} {R : ℝ} (hh : X.jets N D m R) (hn : n+2 ≤ N) (hd : 4 ≤ D)
    (ht : ∀ y ∈ tsupport (fderiv ℝ χ), Points.cons y x ∈ Scaling.window R _)
    (v : Fin (n+1) → (Bel L).Tag) (hv : ∀ i, (v i).1 ≤ D) :
    Tendsto (fun k => (↑(X.r k / X.xi k) : ℂ) *
      ∫ z, sheet 1 (stretch (X.r k) χ) a (stretch (X.r k) W) (X.r k • x)
        (Fin.cons ⟨4,J a b⟩ (X.pins k ∘ v)) z) atTop
      (𝓝 (∫ y, sheet 1 χ a W x (Fin.cons ⟨4,T a b⟩ v) y)) := by
  let B (k : ℕ) := reader _ (X.positive k) x hx H hw a hW (X.pins k ∘ v)
  let A (k : ℕ) := (B k).comp (X.U k 4).toLinearMap
  let F := reader 1 one_pos x hx H' hw a hW v
  have he (u) : Tendsto (fun k => A k u) atTop (𝓝 (F u)) := by
    have hz := tendsto_sheet X H H' x hx hw a hW hh hn ht (Fin.cons ⟨4,u⟩ v) (caps_cons_le u v hd hv)
    simp_rw [pins_cons] at hz; exact hz
  have hA := Dash.arcing (Dash.fit_plane A F he) (hc a b)
  refine hA.congr (fun k => ?_)
  let r := X.r k
  let c := X.xi k
  change B k (X.U k 4 ((X.U k 4).symm ((↑(c⁻¹*r^4):ℂ) • J a b))) = _
  rw [LinearEquiv.apply_symm_apply,map_smul, smul_eq_mul]
  rw [integrate_sheet_scale (X.positive k) _ _ hw.1]
  change (↑(c⁻¹*r^4):ℂ) * (∫ y, sheet r χ a W x (Fin.cons ⟨4,J a b⟩ (X.pins k ∘ v)) y) =
    (↑(r/c):ℂ) * ((r:ℂ)^3 * _)
  push_cast; ring

lemma reaches_grad (X : Scaling S) (H : S.Smooth) (H' : (Bel L).Smooth)
    {J : S.Stress} {T : (Bel L).Stress} (hc : X.meter J T)
    (x : Points (n+1)) (hx : x ∈ conf _) {χ : E4 → ℝ} (hw : Window x χ) (b : Axis)
    {N D m : ℕ} {R : ℝ} (hh : X.jets N D m R) (hn : n+2 ≤ N) (hd : 4 ≤ D)
    (ht : ∀ y ∈ tsupport (fderiv ℝ χ), Points.cons y x ∈ Scaling.window R _)
    (v : Fin n → (Bel L).Tag) (hv : ∀ i, (v i).1 ≤ D)
    (d : ℕ) (u : (Bel L).Field d) (hu : d ≤ D) :
    Tendsto (fun k => (↑(X.r k / X.xi k) : ℂ) *
      shellGrad S J (stretch (X.r k) χ) b (X.r k • x) (X.pins k ∘ v) (X.U k d u)) atTop
      (𝓝 (shellGrad (Bel L) T χ b x v u)) := by
  unfold shellGrad
  simp only [mul_neg,Finset.mul_sum]
  apply Tendsto.neg
  apply tendsto_finsetSum
  intro a _
  have he := reaches_stress X H H' hc x hx hw a b (W := fun _ => 1) continuous_const hh hn hd ht
    (Fin.cons ⟨d,u⟩ v) (caps_cons_le u v hu hv)
  simpa only [pins_cons,sheet,weight,stretch,one_smul,mul_one,disc] using he

lemma reaches_spin (X : Scaling S) (H : S.Smooth) (H' : (Bel L).Smooth)
    {J : S.Stress} {T : (Bel L).Stress} (hc : X.meter J T)
    (x : Points (n+1)) (hx : x ∈ conf _) {χ : E4 → ℝ} (hw : Window x χ) (g : Ortho.Skew)
    {N D m : ℕ} {R : ℝ} (hh : X.jets N D m R) (hn : n+2 ≤ N) (hd : 4 ≤ D)
    (ht : ∀ y ∈ tsupport (fderiv ℝ χ), Points.cons y x ∈ Scaling.window R _)
    (v : Fin n → (Bel L).Tag) (hv : ∀ i, (v i).1 ≤ D)
    (d : ℕ) (u : (Bel L).Field d) (hu : d ≤ D) :
    Tendsto (fun k => (↑((X.xi k)⁻¹) : ℂ) *
      shellSpin S J (stretch (X.r k) χ) g (X.r k • x) (X.pins k ∘ v) (X.U k d u)) atTop
      (𝓝 (shellSpin (Bel L) T χ g x v u)) := by
  unfold shellSpin
  simp only [mul_neg,Finset.mul_sum]
  apply Tendsto.neg
  apply tendsto_finsetSum; intro a _
  apply tendsto_finsetSum; intro b _
  let q : Fin (n+1) → (Bel L).Tag := Fin.cons ⟨d,u⟩ v
  have he := reaches_stress X H H' hc x hx hw a b (arm_continuous x g b) hh hn hd ht q (caps_cons_le u v hu hv)
  have hz : Tendsto (fun k => (↑((X.xi k)⁻¹) : ℂ) *
      ∫ z, sheet 1 (stretch (X.r k) χ) a (arm (X.r k • x) g b) (X.r k • x)
        (Fin.cons ⟨4,J a b⟩ (X.pins k ∘ q)) z) atTop
      (𝓝 (∫ y, sheet 1 χ a (arm x g b) x (Fin.cons ⟨4,T a b⟩ q) y)) := by
    refine he.congr (fun k => ?_)
    let r := X.r k
    let t := (Fin.cons (α := fun _ => S.Tag) ⟨4,J a b⟩ (X.pins k ∘ q))
    let W := arm x g b
    have hq z : sheet 1 (stretch r χ) a (arm (r • x) g b) (r • x) t z =
        (r:ℂ) * sheet 1 (stretch r χ) a (stretch r W) (r • x) t z := by
      dsimp only [W,sheet,weight]; rw [arm_scaled (X.positive k)]; push_cast; ring
    change (↑(r/X.xi k):ℂ) * _ = (↑((X.xi k)⁻¹):ℂ) * ∫ z, sheet _ (stretch r χ) a (arm (r • x) g b) (r • x) t z
    simp_rw [hq,integral_const_mul]; push_cast; ring
  simpa only [q,pins_cons,sheet,one_smul,weight,disc,arm] using hz
end YM.Work.A05
