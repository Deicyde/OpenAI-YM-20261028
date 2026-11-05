import YM.PhysicalNext.ORDERED_AFFINE_2B.Journeys
import YM.Push.RELAY_DIFFERENCE.Birth

/-!
# Arriving the ordered letter calculations at the literal matrices

Keep C the window covariance throughout. `Tracks.Record` is to be
used off-anchor too, for every ordered Run. Compare to ActualScalar's
Page arrays over a neighborhood in V where the frozen geometry has legit
principal inverses (polar threshold equality is fine). Costs/read sets
about complete labels in later files. No extending validity of decisions
claims to any contributing events across the neighborhood.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree AnalyticBridge AnalyticBridge.Covariance Terrain
open AnalyticBridge.ResetIncome SectorTools.ActualScalar SectorNext.Vacuum
open Next Next.Fluctuations Next.SectorChange Completion
open Further Further.CurvedGaussianJets Jets ChangeV Tracks
open Push.SectorMeasure Matrix Receipts Progress.StationaryScenes
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {x σ : ℝ} {A : Stores S} {F : Forest S.ratio} {T : Tube G S} {k : S.Choices}
  {J : Tab} {q n : ℕ} {V : Config G c}

def stack (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) : Bool → Jets.Field G c (Thing G f)
  | true => charter T x A F k
  | false => fun _=> flat T x F k
namespace Tab.Ships
variable (h : J.Ships q n σ T F A k x V)
include h
lemma street_cost (y : Bool) (o : Site f) {z : ℝ} (hz : 0 ≤ z) : ∀ᶠ U in 𝓝 V, J.carries q n o hz S U (stack T x A F k y) :=
  (h.near o hz).mono fun _ h=>by cases y; exact h.2; exact h.1

lemma receiving (y : Bool) (o : Site f) {z : ℝ} (hz : 0 ≤ z) : let W:= windows S G x h.tall
    ∀ᶠ U in 𝓝 V, Tracks.Record W J.v (J.fee G f q o hz) n (rail x) J.K U (stack T x A F k y) (Due S.ratio.embed o q z) :=
    let hw := spent S G x h.tall
    (h.street_cost y o hz).eventually_nhds.mono fun _ h' => (h.port o hz).read h' hw.1


end Tab.Ships

-- actual kernel entries on active basis, from full completion even
-- through V germs in the paired pricing.
abbrev enterAt (G : Gauge) (x : ℝ) (A : Stores S) (F : Forest S.ratio) : Rows.In x A F (G:=G) ↪ Thing G f :=
  Function.Embedding.inl.trans (Completion.sorted A F).toEmbedding
section put
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
omit [DecidableEq α] [DecidableEq γ] [Fintype α] [Fintype β] [Fintype γ] in
private lemma picked_from (p : α⊕β ≃ γ) (C : Gaussian.Table α) : let E := Function.Embedding.inl.trans p.toEmbedding
    (Joint.place p (wide C 1)).submatrix E E = C := by
  intro E; ext i j; change wide C 1 (p.symm (p (.inl i))) (p.symm (p (.inl j)))=_
  rw [p.symm_apply_apply,p.symm_apply_apply]; rfl
private lemma inverse_put (p : α⊕β ≃ γ) (C : Gaussian.Table α) (h : C.PosDef) :
    (Joint.place p (wide C 1))⁻¹=Joint.place p (wide C⁻¹ 1) := by
  unfold Joint.place; rw [inv_submatrix_equiv, Completion.wide_id_inv C (isUnit_iff_ne_zero.mpr h.det_pos.ne')]
end put
lemma active_part (C : Gaussian.Table (Rows.In x A F (G:=G))) : let E := enterAt G x A F
    (identityPut x A F C).submatrix E E = C := picked_from (sorted A F) C
lemma front_gap (h : Fits (initial G f) J.v (charter T x A F k V)) :
    Schur.Gapped (Fixed.precision T x A F k V) J.v.gap := by
  intro v; rw [Schur.sumSq_dot]; have he := h.restrict (enterAt G x A F)
  rw [plinth,active_part] at he
  exact he.floor v

-- covariance inverse calculation genuine on this kernel. Needs its
-- POSITIVITY not just the gap on A (and both extend to pricing near
-- U). Not claiming any total/angular symmetry of ordered derivatives.
def kept (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (k : S.Choices) (x : ℝ) (V : Config G c) (W : CurvedGaussianJets.Windows (Thing G f)) :=
    let C := Jets.covariance W (charter T x A F k) V; let B := Fixed.covariance T x A F k V
    C=identityPut x A F B ∧ C⁻¹=identityPut x A F B⁻¹ ∧ B.PosDef
lemma Tab.Ships.retained (h : J.Ships q n σ T F A k x V) : let W := windows S G x h.tall
    ∀ᶠ U in 𝓝 V, kept T F A k x U W := by
  intro W; let Q := charter T x A F k
  filter_upwards [h.receiving true 0 zero_le_one] with U hU
  let C:= Fixed.covariance T x A F k U
  have ht : Jets.covariance W Q U=identityPut x A F C := actual_cloud T x A F k U h.tall J.v.gap_pos (front_gap (J:=J) hU.full)
  have hPos : (identityPut x A F C).PosDef := ht ▸ (show (Jets.covariance W Q U).PosDef from hU.positive)
  let E:=enterAt G x A F
  have hp : C.PosDef := active_part C ▸ hPos.submatrix E.injective
  refine ⟨ht,?_,hp⟩
  change (Jets.covariance W Q U)⁻¹=identityPut _ _ _ C⁻¹
  rw [ht]; exact inverse_put (sorted A F) C hp

lemma price_reference {e : Plate G S} (hd : Delivery J q n σ e) (he : Doors e) (k : S.Choices) :
    (flat e.tube e.x e.forest k).det=e.Flat.det := by
  unfold flat; rw [across e he noHole k 1 (Y:=1), hd.flat he k,Joint.place_det,det_one,mul_one]
end YM.PhysicalNext.OrderedAffine2B.Whole
