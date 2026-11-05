import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.ActiveColumns
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Market
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorData

/-!
# The `market` restricted to either active set IS the true Gram germ

All-coordinate formulation (indexed on positive fine slots) too.
IDENTITY completion, not the zero extension and not dropping harmonic
modes. Same forest for all k, same boundary selection. Neither claims
mask differentiability nor identifies this with the infinite operator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Bloch Next.SectorChange Next.Fluctuations
  Rows YM.Pressure YM.Pressure.Stores FreeResolvent Affine TestD Push.Uniform Matrix
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {n : ℕ} {C σ M : ℝ}
  {x : ℝ} {A : Stores S} {T U : Forest S.ratio} {k : S.Choices} {V : Config G c}
  {W : PathData G} {s : Signed} {B : Vec G c 1}

def faceIx (G : Gauge) (f : Side) : (Cell f × G.ColorIndex) ≃ tile G f where
  toFun i := inFace i.1 i.2
  invFun j := ((j.1,plaqEquiv.symm j.2.1),j.2.2)
  left_inv _ := by simp only [inFace,Equiv.symm_apply_apply]
  right_inv _ := by simp [inFace]

def edgeIx (G : Gauge) (f : Side) : (Bond f × G.ColorIndex) ≃ raw G f where
  toFun i := hue i.1 i.2
  invFun j := (edge j,j.2.2)
  left_inv _ := by simp only [edge_hue]; rfl
  right_inv _ := hue_edge ..

lemma sumFace (F : tile G f → ℝ) : ∑ i : Cell f, ∑ j : G.ColorIndex, F (inFace i j) = ∑ i, F i :=
  (Fintype.sum_prod_type (f:=fun i => F (faceIx G f i))).symm.trans ((faceIx G f).sum_comp F)
lemma sumEdge (F : raw G c → ℝ) : ∑ i : Bond c, ∑ j : G.ColorIndex, F (hue i j) = ∑ i, F i :=
  (Fintype.sum_prod_type (f:=fun i => F (edgeIx G c i))).symm.trans ((edgeIx G c).sum_comp F)

variable {H : Tube G S} (hS : S.patch.Branches S.kernel G) (hp : DifferentiableAt ℝ (petals S V s) (B,0))
  (hn : DifferentiableAt ℝ (contacts x A T U k V s) (B,0)) (hs : 0 ≤ σ) (hW : Sheet H.up σ M)
include hS hp hn hs hW

omit hS hp hn hs hW in
lemma slip_sq : slip^2 = (Fintype.card Signed:ℝ)⁻¹ := by
  unfold slip; rw [inv_pow,Real.sq_sqrt (by positivity)]

lemma per_orientation (i j : In (G:=G) x A T) :
    let Q := Rows.move H x (increment V (paint G c B)) k (shots S x) A T
    ((∑ p : Twin f, ∑ b : G.ColorIndex, Q ((s,.inl p),b) i * Q ((s,.inl p),b) j) +
        ∑ e : Bond c, ∑ b : G.ColorIndex, Q ((s,.inr e),b) i * Q ((s,.inr e),b) j) =
      slip^2 * outlet x A T U k V s H.high H.up (shorter (till x)) B (attach A T i) (attach A T j) := by
  intro Q; let i' := attach A T i; let j' := attach A T j; let P := matrix (petals S V s) B
  let F := over (NoHole.pathRows S s H.up (shorter (till x))) V B * P
  let N := matrix (contacts x A T U k V s) B
  have h1 : ∀ p b, Q ((s,.inl (p,true)),b) i * Q ((s,.inl (p,true)),b) j = slip^2*(F.transpose i' (inFace p b) * F (inFace p b) j') := by
    intro p b; unfold Q; rw [barrel_column hS hp hs _ _ _ hW,barrel_column hS hp hs _ _ _ hW]; change (slip*F _ i')*(slip*F _ j')=_; simp only [Matrix.transpose_apply]; ring
  have h2 : ∀ p b, Q ((s,.inl (p,false)),b) i * Q ((s,.inl (p,false)),b) j = slip^2*(H.high.direct*(P.transpose i' (inFace p b)*P (inFace p b) j')) := by
    intro p b; unfold Q; rw [face_column hS hp,face_column hS hp]; change (slip*(Real.sqrt _*P _ i'))*(slip*(Real.sqrt _*P _ j'))=_
    nth_rw 3 [← Real.sq_sqrt H.high.quadratic_pos.le]; simp only [Matrix.transpose_apply]; ring
  have h3 : ∀ e b, Q ((s,.inr e),b) i * Q ((s,.inr e),b) j = slip^2*(S.kernel.penalty*(N.transpose i' (hue e b)*N (hue e b) j')) := by
    intro e b; unfold Q; rw [noise_column hS hn,noise_column hS hn]; change (slip*(-Real.sqrt _*N _ i'))*(slip*(-Real.sqrt _*N _ j'))=_
    nth_rw 3 [← Real.sq_sqrt S.kernel.penalty_pos.le]; simp only [Matrix.transpose_apply]; ring
  change _ = slip^2*(((H.high.direct • squareQ P + squareQ F) + S.kernel.penalty • squareQ N) i' j')
  rw [Fintype.sum_prod_type (f:=fun p : Twin f => ∑ b, _)]
  simp_rw [Fintype.sum_bool, h1,h2,h3,Finset.sum_add_distrib,squareQ,Matrix.add_apply,Matrix.smul_apply,Matrix.mul_apply,
    smul_eq_mul,mul_add,Finset.mul_sum]
  rw [sumFace (fun e => slip^2*(F.transpose i' e*F e j')),sumFace (fun e => slip^2*(H.high.direct*(P.transpose i' e*P e j'))),
    sumEdge (fun e => slip^2*(S.kernel.penalty*(N.transpose i' e*N e j')))]
  abel

omit hn hp
lemma market_chart (h : Sharing x A T U k V n C) :
    over (Sector.form H x A T k) V =ᶠ[𝓝 0] fun B => (market x A T U k V H.high H.up (shorter (till x)) B).submatrix (attach A T) (attach A T) := by
  have ht : Tendsto (fun B => (B,(0:Vec G f 1))) (𝓝 (0:Vec G c 1)) (𝓝 0) := (continuous_id.prodMk (continuous_const (y:=0))).continuousAt
  have he (s : Signed) := (contDiffAt_pi.mpr (fun i => (h.faces s i).analytic)).eventually (by simp)
  have hh (s : Signed) := (contDiffAt_pi.mpr (fun i => (h.noise s i).analytic)).eventually (by simp)
  filter_upwards [ht.eventually (eventually_all.mpr he),ht.eventually (eventually_all.mpr hh)] with B hb hB
  ext i j
  change ((Rows.move H x (increment V (paint G c B)) k (shots S x) A T).transpose * Rows.move H x (increment V (paint G c B)) k (shots S x) A T) i j = _
  rw [Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type, Matrix.transpose_apply, submatrix_apply, market,Matrix.smul_apply,Matrix.sum_apply,
    smul_eq_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => slip_sq ▸ per_orientation hS ((hb s).differentiableAt (by simp)) ((hB s).differentiableAt (by simp)) hs hW i j

omit hS hs hW
variable (x A T G) in
def plug : In (G:=G) x A T ↪ raw G f := ⟨attach A T, attach_inj G A T⟩

def finished (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (V : Config G c) :=
  let e := plug G x A T
  insertion e * Sector.form H x A T k V * (insertion e).transpose + Shell.off e
include hS hs hW


end YM.SelectedOrderedKernels.Selected
