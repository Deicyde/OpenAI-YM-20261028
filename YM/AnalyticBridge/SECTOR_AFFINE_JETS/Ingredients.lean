import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Branch
import YM.Push.SECTOR_MEASURE.Output

/-!
# Bounds on individual jet components for D, before spatial estimates

No clipping on the coarse V input in the precision. All of the stencils
that actually need the fine predictor call use the sector selection.
Account also for path transports on `bar V` in D, with costs uniform in
V. Do not price those assuming all path interiors in a common small-field
gauge. Real Taylor jets.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine
open Filter Function Lattice Wilson RG Precision Pressure Tree
open YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.Push.SectorMeasure.Oriented
open YM.Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {P : Patch} {c f : Side} {S : StepData c f}

section curvature
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def curvatureL (G : Gauge) : G.Mat →L[ℝ] G.Color :=
  G.projectColor.toContinuousLinearMap ∘L ((1/2:ℝ) •
    (ContinuousLinearMap.id ℝ G.Mat - (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).toContinuousLinearMap))

-- expose the cost in the same Frobenius norm

private def opPrice {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) := ‖L‖
private lemma opPrice_nn {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) : 0 ≤ opPrice L := norm_nonneg L

def curvatureCost (G : Gauge) : ℝ := opPrice (E:=G.Mat) (F:=G.Color) (curvatureL G)
lemma curvature_nn (G : Gauge) : 0 ≤ curvatureCost G := opPrice_nn (E:=G.Mat) (F:=G.Color) _

lemma curvature_price {U : E → G.El} {x : E} {M : ℝ} {n : ℕ} (h : Allows n (fun z => G.mat (U z)) x M) :
    Allows n (fun z => G.curvature (U z)) x (curvatureCost G * M) := h.linear (curvatureL G) le_rfl
end curvature

def facePlot (S : StepData c f) (V : Config G c) (s : Signed) (i : Cell f) (p : FieldPair G c f) :=
  G.curvature (faceValue (sceneField S V s p) i)

def blockPlot (S : StepData c f) (V : Config G c) (s : Signed) (i : Bond c) (k : S.Choices)
    (p : FieldPair G c f) :=
  G.curvature (predictorTurn (field V p.1) k s i p.2)

lemma face_paid (G : Gauge) (n : ℕ) : ∃ r C : ℝ, 0<r ∧ 0<C ∧
    ∀ {c f : Side} (S : StepData c f) (V : Config G c) (B : PriceCoords G c), ‖B‖≤r →
      ∀ (s : Signed) (i : Cell f), Allows (n+1) (facePlot S V s i) (B,0) C ∧
      ∀ a : Directions G f, ‖a‖ ≤ 1 →
        Allows n (fun y => plaquetteJet S (field V y) s i a) B C := by
  obtain ⟨r,C,hr,-,H⟩ := coordinates G (n+1)
  let M := max 1 (curvatureCost G * travelCost G (n+1) 4 C)
  refine ⟨r,M,hr,zero_lt_one.trans_le (le_max_left ..),?_⟩
  intro c f S V B hb s i
  have hL : Allows (n+1) (facePlot S V s i) (B,0) M := by
    apply Allows.mono (C:=curvatureCost G * travelCost G (n+1) 4 C) _ (le_max_right ..)
    unfold facePlot
    apply curvature_price (U:=fun p => faceValue (sceneField S V s p) i)
    exact travel_jets (fun e => (H B hb V).2 S s e) i.1 (le_refl (4:ℕ))
  exact ⟨hL, fun a ha => priced_partial hL a ha⟩

lemma block_paid (G : Gauge) (P : Patch) (K : KernelChoices) (hk : P.Branches K G) (n : ℕ) :
    ∃ r M : ℝ, 0<r ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    100*(1+radiusB x) ≤ c.val → ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (s : Signed) (i : Bond c) (B : PriceCoords G c),
      curb (shots S x) A F x s (.inr i) → ‖B‖ ≤ r →
      ∀ k : S.Choices, Allows (n+1) (blockPlot S V s i k) (B,0) M ∧
      ∀ a : Directions G f, ‖a‖ ≤ 1 →
        Allows n (fun y => blockJet (field V y) k s i a) B M := by
  obtain ⟨r,M,hr,-,h⟩ := chosen_branch G P K hk (n+1)
  let D := 2^(n+1)*M*M
  let W := max 1 (curvatureCost G * D)
  refine ⟨r,W,hr,zero_lt_one.trans_le (le_max_left ..),?_⟩
  filter_upwards [h] with x hx
  intro c f S hP hK hf F A V hA s i B ht hB k
  let U := fun y : FieldPair G c f => predictGroup (field V y.1) k s i y.2
  have he : Allows (n+1) (fun y => G.mat (U y)) (B,0) M :=
    (hx S hP hK hf F A V hA s i B ht hB).1 (choice s k)
  have hL : Allows (n+1) (blockPlot S V s i k) (B,0) W := by
    let p : FieldPair G c f := (B,0)
    have hm' := allows_first_slice (f:=fun y => G.mat (U y)) he
    have hp : Allows (n+1) (fun y : FieldPair G c f => G.mat (U (y.1,0))) p M := allows_first_var (p:=p) (f:=fun z => G.mat (U (z,0))) hm'
    have hw := he.times (hp.inverse (f:=fun y : FieldPair G c f => U (y.1,0)))
    exact (curvature_price (U:=fun y => U y * (U (y.1,0))⁻¹) hw).mono (le_max_right ..)
  exact ⟨hL,fun a ha => priced_partial hL a ha⟩

section transport
variable {σ : ℝ}

/-- Pay the true length polynomial. Consume *only* an assigned δ
of exponential rate, then carry the rest to the marked entries. -/
lemma travel_coupon (G : Gauge) (n : ℕ) (C : ℝ) (hC : 0 ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0<K ∧ ∀ d : ℕ, travelCost G n d C ≤ K * Real.exp (δ*d) := by
  let M : ℝ := (n.factorial:ℝ)*(Real.exp 1 * ‖(1:G.Mat)‖)*(1+C)^n
  let W : ℝ := 2^n
  let A := (1+W)^n
  let K := M*A*FreeResolvent.Mark.polynomial δ n
  refine ⟨max 1 K, zero_lt_one.trans_le (le_max_left ..),fun d => ?_⟩
  calc
    _ = M * (1+W*(1+d))^n := by unfold travelCost composeCost M W; ring
    _ ≤ M * ((1+W)*(1+d))^n := by
      gcongr
      nlinarith only [show 0 ≤ (d:ℝ) by positivity]
    _ ≤ K * Real.exp (δ*d) := by
      rw [mul_pow, ← mul_assoc]
      unfold K
      rw [mul_assoc (M*A)]
      exact mul_le_mul_of_nonneg_left (FreeResolvent.Mark.poly_weight n hδ (Nat.cast_nonneg _))
        (by unfold M; positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _).le

/-- One genuine transported operator application on vectors.
Kept in terms of the same mat jets as the two elementary blocks. -/
lemma adjoint_cost {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : E → G.El} {w : E → G.Color} {x : E} {M C : ℝ} {n : ℕ}
    (hU : Allows n (fun z => G.mat (U z)) x M) (hw : Allows n w x C) :
    Allows n (fun z => G.adjoint (U z) (w z)) x
      (G.colorScale⁻¹*(2^n*(2^n*M*(G.colorScale*C))*M)) := by
  let L := G.projectColor.toContinuousLinearMap
  have hL : opPrice (E:=G.Mat) (F:=G.Color) L ≤ G.colorScale⁻¹ := by
    refine L.opNorm_le_bound (inv_nonneg.mpr G.colorScale_pos.le) fun u => ?_
    rw [mul_comm,← div_eq_mul_inv]; exact G.project_norm u
  let J := G.colorMat.toContinuousLinearMap
  have hJ : opPrice (E:=G.Color) (F:=G.Mat) J ≤ G.colorScale := J.opNorm_le_bound G.colorScale_pos.le (fun v => (G.colorMat_norm v).le)
  have hb {X Y : E → G.Mat} {A B : ℝ} (h : Allows n X x A) (hp : Allows n Y x B) :
      Allows n (fun z => X z * Y z) x (2^n*A*B) := by
    simpa only [mul_one,ContinuousLinearMap.mul_apply'] using h.bilinear _ hp
      (ContinuousLinearMap.opNorm_mul_le ℝ G.Mat)
  have hh := (hb (hb hU (hw.linear J hJ)) hU.inverse).linear L hL
  exact hh

/-- One cut-stack entry vector, before multiplying by its paid
coefficient and applying a color output. -/
def piece (S : StepData c f) (V : Config G c) (s : Signed) (a : Directions G f) (o : Cell f)
    (l : RG.Slot) (y : PriceCoords G c) :=
  G.adjoint (travel (facade S s (field V y) 0) o.1 l.walk)
    (plaquetteJet S (field V y) s (YM.Work.F03.slotFace l o.1) a)

lemma path_paid (G : Gauge) (hσ : 0 < σ) (n : ℕ) : ∃ r C : ℝ, 0<r ∧ 0<C ∧
    ∀ {c f : Side} (S : StepData c f) (V : Config G c) (s : Signed) (a : Directions G f), ‖a‖≤1 →
    ∀ (o : Cell f) (l : RG.Slot) (B : PriceCoords G c), ‖B‖≤r →
      Allows n (piece S V s a o l) B (C*Real.exp (σ*l.length)) := by
  obtain ⟨r,C,hr,hC,H⟩ := coordinates G n
  obtain ⟨β,M,hβ,hM,H'⟩ := face_paid G n
  let δ := σ/2
  have hd : 0 < δ := half_pos hσ
  obtain ⟨K,hK,hk⟩ := travel_coupon G n C hC.le hd
  let L := G.colorScale⁻¹*(2^n*(2^n*K*(G.colorScale*M))*K)
  refine ⟨min r β,L,lt_min hr hβ, by unfold L; have := G.colorScale_pos; positivity,?_⟩
  intro c f S V s a ha o l B hB
  let U (y : PriceCoords G c) := facade S s (field V y) 0
  let v := YM.Work.F03.slotFace l o.1
  have hT (i : Bond f) : Allows n (fun z => G.mat (U z i)) B C :=
    allows_first_slice ((H B (hB.trans (min_le_left ..)) V).2 S s i)
  let R := Real.exp (δ*l.length)
  have hu : Allows n (fun z => G.mat (travel (U z) o.1 l.walk)) B (K*R) :=
    (travel_jets hT _ (show l.walk.length ≤ l.length by unfold Slot.length; omega)).mono (hk _)
  have hw := adjoint_cost (U:=fun z => travel (U z) o.1 l.walk) hu
    ((H' S V B (hB.trans (min_le_right ..)) s v).2 a ha)
  have he : Real.exp (σ*l.length)=R*R := by unfold R δ; rw [← Real.exp_add]; congr 1; ring
  rw [he]; exact hw.mono (le_of_eq (by unfold L; ring))
end transport
end YM.AnalyticBridge.SectorAffine
