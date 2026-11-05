import YM.Push.FREE_RESOLVENT.Envelope
import YM.Push.STATIONARY_UNIFORM.Beacons
import YM.Push.STATIONARY_UNIFORM.FrameScore
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion




/-!
# Left coordinates for the sector covariance estimates

We will work all along in `PriceCoords G c`, *per color*, holding the base field
V (which need NOT be globally small) fixed in taking ordinary coordinate
derivatives. Norm for a coordinate-neighborhood radius here is the max over
edges AND color components. These coordinates give `G.Color` vectors in exactly
the `Next.SectorChange` convention. Parameters on varying volumes never have
to be measured in `volume`-dependent charts; radii here are real radii,
not complex neighborhoods nor order-uniform budgets.

This file allows differentiating the full pair `(output perturbation, common
fine a)` at the needed points; in particular after actual signed pull, without
regarding that as pulling back a independent of the base field.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Lattice Wilson RG Precision Pressure
open YM.Next.SectorChange YM.Next.SectorChange.Motion
open YM.Push.Uniform
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}

abbrev Coord (G : Gauge) (c : Side) := Bond c × G.ColorIndex

/-- Real parameter sup-normed on its *scalar* components. -/
abbrev PriceCoords (G : Gauge) (c : Side) := Prices G (Bond c)

def field (V : Config G c) (B : PriceCoords G c) := increment V (tape B)

lemma field_zero (V : Config G c) : field V 0 = V := by
  rw [field, show tape (0:PriceCoords G c) = 0 from gaugeCount.map_zero]
  exact increment_zero _

abbrev FieldPair (G : Gauge) (c f : Side) := PriceCoords G c × Directions G f

def sceneField (S : StepData c f) (V : Config G c) (s : Signed) (z : FieldPair G c f) :=
  facade S s (field V z.1) z.2

lemma mat_paid (g : G.El) : ‖G.mat g‖ = G.colorScale := Gauge.unitary_frob (G.mat_mul_star g)

section allows
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {n : ℕ} {x : E} {C : ℝ}

lemma pre_short {f : F → H} (L : E →L[ℝ] F) (h : Allows n f (L x) C)
    (hL : ‖L‖ ≤ 1) : Allows n (f ∘ L) x C := by
  constructor
  · exact h.analytic.comp x L.contDiff.contDiffAt
  intro k hk
  rw [iter_lin_at (h.analytic.of_le le_top)]
  calc
    _ ≤ _ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..
    _ ≤ C := by
      apply le_trans _ (h.norm_le k hk)
      exact mul_le_of_le_one_right (norm_nonneg _) ((Finset.prod_le_prod
        (fun _ _ => norm_nonneg _) (fun _ _ => hL)).trans_eq (by simp))

lemma allows_first_var {p : E × F} {f : E → H} (h : Allows n f p.1 C) :
    Allows n (fun z : E × F => f z.1) p C := by
  let L := ContinuousLinearMap.fst ℝ E F
  exact pre_short L h (L.opNorm_le_bound zero_le_one (fun y => by simp only [one_mul]; exact norm_fst_le y))

lemma allows_first_slice {f : E × F → H} (h : Allows n f (x,0) C) :
    Allows n (fun y : E => f (y,0)) x C := by
  let L := ContinuousLinearMap.inl ℝ E F
  exact pre_short L h (L.opNorm_le_bound zero_le_one (fun y => by simp [L]))

/-- Price applications of an actual partial `fderiv`, without changing the
frame at each derivative. Works in a germ: not taking a uniform continuation
lemma about the measures/flags as a consequence. -/
lemma priced_partial {f : E × F → H} (h : Allows (n+1) f (x,0) C) (a : F) (ha : ‖a‖ ≤ 1) :
    Allows n (fun y : E => fderiv ℝ (fun v => f (y,v)) 0 a) x C := by
  let L : F →L[ℝ] E × F := ContinuousLinearMap.inr ..
  have he : Allows n (fderiv ℝ f) (x,0) C := by
    refine ⟨h.analytic.fderiv_right (by simp), fun k hk => ?_⟩
    rw [norm_iteratedFDeriv_fderiv]; exact h.norm_le _ (Nat.succ_le_succ hk)
  let J := ContinuousLinearMap.apply ℝ H (L a)
  have hp : ‖J‖ ≤ 1 := J.opNorm_le_bound zero_le_one (fun y => by
    change ‖y (L a)‖ ≤ _
    rw [one_mul]
    exact (y.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (by simpa [L] using ha)))
  have hh := allows_first_slice (he.linear J hp); rw [one_mul] at hh
  apply hh.germ
  have hL : ContinuousAt (fun y : E => ((y,(0:F)):E × F)) x :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [hL.tendsto.eventually (h.analytic.eventually (by simp))] with y hy
  have h0 : HasFDerivAt (fun v : F => ((y,v):E × F)) L 0 :=
    (hasFDerivAt_const y _).prodMk (hasFDerivAt_id _)
  have hv := ((show ContDiffAt ℝ ω f (y,0) from hy).differentiableAt (by simp)).hasFDerivAt.comp (0:F) h0
  change J _ = fderiv ℝ (f ∘ (fun v : F => (y,v))) 0 a
  rw [hv.fderiv]; rfl

end allows

/-- Projection onto the vector on an edge. -/
def edgeVec (G : Gauge) {n : Side} (e : Bond n) : PriceCoords G n →L[ℝ] G.Color :=
  (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond n => G.Color) e).comp gaugeCount.toContinuousLinearMap

lemma norm_edgeVec_le (G : Gauge) {n : Side} (e : Bond n) : ‖edgeVec G e‖ ≤ FreeResolvent.Affine.filePrice G := by
  have hp : (1:ℝ) ≤ _ := FreeResolvent.Affine.file_pos G
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hp)
  intro B
  let L : (G.ColorIndex → ℝ) →L[ℝ] G.Color := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : G.ColorIndex => ℝ)).symm
  let y := fun j : G.ColorIndex => B (e,j)
  change ‖L y‖ ≤ _
  refine (L.le_opNorm _).trans (mul_le_mul (le_add_of_nonneg_right (b:=1) zero_le_one) ?_
    (norm_nonneg _) (zero_le_one.trans hp))
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg B)).mpr fun j => norm_le_pi_norm B (e,j)

/-- Costs of the fields for the covariance jets. No path/tag hypotheses or
restrictions on V. -/
theorem coordinates (G : Gauge) (n : ℕ) : ∃ r C : ℝ, 0<r ∧ 0<C ∧
    ∀ {c : Side} (B : PriceCoords G c), ‖B‖ ≤ r → ∀ V : Config G c,
    (∀ i : Bond c, Allows n (fun y => G.mat (field V y i)) B C) ∧
    ∀ {f : Side} (S : StepData c f) (s : Signed),
      ∀ i : Bond f, Allows n (fun z : FieldPair G c f => G.mat (sceneField S V s z i)) (B,0) C := by
  obtain ⟨K,hK,H⟩ := exp_receipt G n
  let X := FreeResolvent.Affine.filePrice G
  have hX : 1 ≤ X := FreeResolvent.Affine.file_pos _
  have hx : 0<X := by linarith
  let r := X⁻¹
  let W := composeCost n K X
  let M := 2^n * W * G.colorScale
  let M₁ := max M G.colorScale
  let D := 2^n * composeCost n K 1 * M₁
  let C := max M₁ D
  have hm' : 0 < M₁ := G.colorScale_pos.trans_le (le_max_right ..)
  refine ⟨r,C,inv_pos.mpr hx,hm'.trans_le (le_max_left ..),?_⟩
  intro c B hr V
  have H₁ (i : Bond c) : Allows n (fun y => G.mat (field V y i)) B M := by
    let L := edgeVec G i
    have hL : ‖L‖ ≤ X := norm_edgeVec_le G i
    have hu : ‖L B‖ ≤ 1 := (L.le_opNorm B).trans (by
      calc ‖L‖ * ‖B‖ ≤ X * r := mul_le_mul hL hr (norm_nonneg _) hx.le
           _ = 1 := mul_inv_cancel₀ hx.ne')
    have h : Allows n (fun y => G.mat (G.lieExp (L y))) B W :=
      (H (L B) hu).comp (f:=L) (allows_linear hL (hu.trans hX))
    exact h.times (g:=fun _ => V i) (allows_const _ (mat_paid (V i)).le)
  have hW : M ≤ M₁ := le_max_left ..
  refine ⟨fun _ => (H₁ _).mono (hW.trans (le_max_left ..)),?_⟩
  intro f S s i
  let u : FieldPair G c f := (B,0)
  have hc (e : Bond f) : Allows n (fun y => G.mat (replica S.ratio (field V y) e)) B M₁ := by
    unfold replica
    split
    · exact allows_const _ ((mat_paid _).le.trans (le_max_right ..))
    exact (H₁ _).mono hW
  have hg (e : Bond f) : Allows n (fun z : FieldPair G c f => G.mat (increment
      (replica S.ratio (field V z.1)) z.2 e)) u D := by
    let L : FieldPair G c f →L[ℝ] G.Color :=
      (ContinuousLinearMap.proj e).comp (ContinuousLinearMap.snd ℝ _ _)
    have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun y => by
      change ‖y.2 e‖ ≤ _
      rw [one_mul]; exact (norm_le_pi_norm y.2 _).trans (norm_snd_le _))
    have hu : L u=0 := rfl
    have hl : ‖L u‖ ≤ 1 := by rw [hu,norm_zero]; norm_num
    have hm := (H _ hl).comp (f:=L) (allows_linear hL hl)
    have hp := allows_first_var (p:=u) (hc e)
    exact hm.times (f:=fun z => G.lieExp (L z)) (g:=fun z => replica S.ratio (field V z.1) e) hp
  unfold sceneField facade
  simp_rw [turn_read]
  split
  · exact ((hg _).inverse (f:=fun z : FieldPair G c f => increment
      (replica S.ratio (field V z.1)) z.2 (sendEdge s 0 i))).mono (le_max_right ..)
  exact (hg _).mono (le_max_right ..)

end YM.AnalyticBridge.SectorAffine
