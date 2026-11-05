import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Diags
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Dye

/-!
# Local log differences

Attach X and blank X with the same B under F for the scalar correction,
χ etc normalization. Do not fork a second k. Real invoice BOTH near and
far. `scraps` cost independent. Reassembly will choose Mayer labels. Use
θ from Shoots; no proof schedule wrapped beyond thresholds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η r Q Y : ℝ} {L : Side} (X : Coat T F)
open Pulse Pulse.Batch

def condensation (v : Bond f) := (joint X.blank.plate X.shutter v-joint X.plate X.shutter v)/2
lemma postedBase (θ : Rotator P L η r Q Y X) (hb : Rotator P L η r Q Y X.blank) (v : Bond f) :
    |X.condensation v| ≤ Fintype.card G.ColorIndex * ((Q+1)*payE η r Q (tubularPrice G L)) := by
  unfold condensation; rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  refine (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr ?_
  exact (abs_sub _ _).trans (((add_le_add (nearBase X.shutter θ.full hb.scale v) (nearBase X.shutter θ.full θ.scale v))).trans_eq
    (by ring))

lemma rotation_at (z : Site c→G.El) (θ : Rotator P L η r Q Y X) (he : Rotator P L η r Q Y (X.rinse z)) (v : Bond f) :
    joint (X.rinse z).plate X.shutter v=joint X.plate X.shutter v := by
  let F := colorwise (z∘atEdge S)
  have hf := θ.full
  rw [joint_coil _ X.shutter he.scale hf,joint_coil _ X.shutter θ.scale hf]
  refine intervalIntegral.integral_congr ?_; intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact Batch.rinse_at v s _ (X.rinse_invar z θ.room.accepted)
    (inverse_up _) (θ.scale.glide hf.hv hf.hQ _ hs) (he.scale.glide hf.hv hf.hQ _ hs) (fun _ _ H => Rotation.off _ _ _ H) rfl

/-- Effective local diagnostics, ready to attach. `forall z` can be
supplied without any sector choices via uniform `shoots` eventual (flags
remain). -/
theorem condenses (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (η r Q Y : ℝ) :
    ∃ E, Rate G L (-(1/2)) E ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
    (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Rotator P L η r Q Y X → X.manifest →
    (∀ z, Rotator P L η r Q Y (X.rinse z)) → Rotator P L η r Q Y X.blank →
    0 ≤ E x ∧ ∀ i : Bond f, ¬ Inside (atEdge S i) X.seeds (30*X.B) → |X.condensation i| ≤ E x := by
  obtain ⟨C,hC,hX⟩ := bounded_stencils P D hd
  obtain ⟨Z,t,hZ,ht,hW⟩ := chord_chart_cost G
  obtain ⟨w,H,h⟩ := flattening P L
  let P₀ x := Z*w x
  let A x := repair G C (P₀ x) Y (radiusB x)
  let m := tubularPrice G L
  let F₀ x := pulseHead η r Q (A x) m (radiusB x)
  let X x := (Fintype.card G.ColorIndex:ℝ)*F₀ x
  have hf : Rate G L (-(1/2)) A := by
    have he := ((((((((Rate.radius_price.add (Rate.const 1)).mul_left (2*G.colorScale)).mul (H.mul_left Z)).mul_right 1).mul_left C).mul_left scale).mul_right Y).mul_left 2)
    simpa only [zero_add] using! he
  have hx : Rate G L (-(1/2)) X := by
    have he := Census.width_rate G L 1 2; simp only [one_mul] at he
    have hp := ((((he.mul_right (m:ℝ)).mul hf).mul_left (payE η r Q m + (Q+1)*(payE η r Q m)^2)).mul_left
      (Fintype.card G.ColorIndex:ℝ))
    simpa only [zero_add] using! hp
  refine ⟨X,hx,?_⟩
  filter_upwards [H.below (by norm_num) _ ht,h] with x HX h c f S T F K hu hS hL hk he h₁ h₂
  subst x; obtain ⟨h₀,h⟩ := h
  have hh := hk.room
  have hB : 100 ≤ K.B := hh.sight.1
  have hz : 0 ≤ P₀ K.x := by unfold P₀; positivity
  have ha : 0≤ A K.x := by
    unfold A repair swell; have := scale_pos; have := G.colorScale_pos; have := hk.signs; positivity
  have hP : 0 ≤ payE η r Q m := hk.scale.disc
  have hum : 0 ≤ X K.x := by
    unfold X F₀ pulseHead; have := hk.scale.fuel; positivity
  refine ⟨hum,fun i hi => ?_⟩; let o := atEdge S i
  have ht := clean_far K.seeds K.V he hi
  obtain ⟨z,b,hg,hb⟩ := h c f S T hL hh K.V o (6*K.B) (by unfold Coat.B; omega)
    (ht.shrink (v:=o) (by unfold o; rw [separation_self]; omega))
  have hx j (hs : separation o (Prod.fst j) ≤ 6*K.B) : G.chord (gauge z K.V j) ≤ P₀ K.x := by
    rw [hg j hs,Work.F03.represent_link]; have hh := (norm_le_pi_norm b (pole j)).trans hb
    exact (hW _ ((hh.trans (le_abs_self _)).trans HX)).trans (mul_le_mul_of_nonneg_left hh hZ.le)
  have hv := Batch.patch_cost K.shutter hk.full (h₁ z).scale h₂.scale i (A K.x) ha (fun x j hj a hh' =>
    K.dye hh o (h₁ z) h₂ hi j a ((separation_comm ..).trans_le (K.shutter.high j (i,x) hj))
      ((separation_comm ..).trans_le (K.shutter.high a (i,x) hh')) hC (hX c f S T hS hk.room.accepted) hz hx)
  unfold condensation; rw [abs_div, ← K.rotation_at z hk (h₁ z),abs_sub_comm]; exact (div_le_iff₀ (by norm_num :
    0 < |(2:ℝ)|)).mpr (hv.trans (le_mul_of_one_le_right hum (by norm_num)))
end YM.ConnectedActivityE6.Coat
