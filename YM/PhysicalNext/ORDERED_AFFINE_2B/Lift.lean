import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Extra.MULTISOURCE_TRAJECTORIES.Gather
import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Taylor
import YM.Further.CURVED_GAUSSIAN_JETS.Mapping
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Balance
import YM.Next.MAXWELL.Silt
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.Eqs
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Issue
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.CORRECTED_COLUMNS.Recover
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STRESS_FLUX.Ward
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current


/-!
# Reconciling the two row alphabets on the true sector.

`Further.CurvedGaussianJets.Mapping.table`'s NOISE ROW space is
**smaller** than in SC and in E. It has one canonical (positive orientation
link, color) copy. Faces already in signed channels. There's no `F0`
in `Mapping.table`. Thus comparing the affine maps cannot mean a change
of index by an equivalence. The coefficient identity below uses the
necessary isometric IMBEDDING. Copy the canonical Q relative *tangent*
into every noise channel with the pay on the signed copy, MINUS AND
-Q-inverse ADJOINT conventions as in SC/E (formula: Ad(Q⁻¹) with a
minus for orientation reversal, not V-adjoint). Keep residual/constant
rows in the actual LARGER space. No branch probability in the lift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Mapper
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.ResetIncome 
open Further Further.CurvedGaussianJets
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f}

abbrev Address (G : Gauge) (c f : Side) := Mapping.Domain G c f
private abbrev ReceiptVec (G : Gauge) (S : StepData c f) := Receipt G S → ℝ
abbrev SourceVec (G : Gauge) (c f : Side) := Address G c f → ℝ

def faceAddr (s : Signed) (i : Cell f) (b : Bool) (j : G.ColorIndex) : Address G c f :=
  if b then Sum.inr (.inl (s,(Cut.turn f i,j))) else Sum.inl (s,(Cut.turn f i,j))

def noiseAddr (i : Bond c) (j : G.ColorIndex) : Address G c f :=
    Sum.inr (.inr (SectorNext.Vacuum.FlatTree.wheel c i,j))

def solo (v : SourceVec G c f) : Directions G c := fun i => WithLp.toLp 2 fun j => v (noiseAddr i j)
lemma solo_add (u v : SourceVec G c f) : solo (u+v)=solo u+solo v := rfl
lemma solo_smul (u : SourceVec G c f) (b : ℝ) : solo (b•u)=b•solo u := rfl

variable (k : S.Choices) (V : Config G c)

/-- Pointwise Q evaluation (shared actual tags, no clipping forecast). -/
abbrev Q := S.prediction (replica S.ratio V) k

def distribute (u : SourceVec G c f) (i : Receipt G S) : ℝ :=
  match i with
  | ⟨(s,.inl (p,b)),j⟩ => u (faceAddr s p b j)
  | ⟨(s,.inr p),j⟩ => slip * ((Motion.inChannel s (Q k V) (solo u)) p) j

def distributor : SourceVec G c f →ₗ[ℝ] ReceiptVec G S := {
  toFun := distribute k V
  map_add' := fun u v => by
    funext i; rcases i with ⟨⟨s,p|p⟩,j⟩
    · rfl
    change slip*Motion.inChannel s (Q k V) (solo (u+v)) p j=_+_
    rw [solo_add,map_add]; change slip*(_+_)=_; rw [mul_add]; rfl
  map_smul' := fun b u=>by
    funext i; rcases i with ⟨⟨s,p|p⟩,j⟩
    · rfl
    change slip*Motion.inChannel s (Q k V) (solo (b • u)) p j=b*_
    rw [solo_smul,map_smul]; change slip*(b*_) = b*(slip*_); rw [mul_left_comm]; rfl }

def lift := LinearMap.toMatrix' (distributor k V)

lemma delivers (u : SourceVec G c f) : lift k V *ᵥ u = distribute k V u := LinearMap.toMatrix'_mulVec ..

lemma distribution_budget (s : Signed) (u : SourceVec G c f) :
    ∑ p : Bond c, ∑ j, (distribute k V u ((s,.inr p),j))^2 = slip^2 * ∑ i : Shape.Page G c 1, (u (.inr (.inr i)))^2 := by
  let H := Motion.inChannel s (Q k V) (solo u)
  change ∑ p, ∑ j, (slip*H p j)^2=_
  simp_rw [mul_pow,←Finset.mul_sum]; congr 1
  have he : ∀ p, (∑ j, (H p j)^2)=∑ j, (solo u (sendEdge s 0 p) j)^2 := by
    intro p
    rw [show (∑ j, (H p j)^2)=‖H p‖^2 by rw [EuclideanSpace.real_norm_sq_eq],Motion.in_size,EuclideanSpace.real_norm_sq_eq]
  simp_rw [he]; conv_rhs => rw [Fintype.sum_prod_type]
  -- Definitional reindex through the actual bond permutation
  let r := (RG.StepData.sendBonds s (0:Site c))
  let E := SectorNext.Vacuum.FlatTree.wheel c
  exact Equiv.sum_comp (r.trans E) (fun i => ∑ j : G.ColorIndex, (u (.inr (.inr (i,j))))^2)

lemma distributor_sq (u : SourceVec G c f) :
    ∑ i : Receipt G S, ((lift k V *ᵥ u) i)^2 = ∑ i, (u i)^2 := by
  rw [delivers]
  -- pair-by-channel; sum exact independent count
  let R (s : Signed) (b : Bool) := ∑ i : Cell f,∑ j, (u (faceAddr s i b j))^2
  let L := ∑ i : Shape.Page G c 1, (u (Sum.inr (.inr i)))^2
  have he (s : Signed) : ∑ p : Twin f,∑ j : G.ColorIndex,(distribute k V u ((s,.inl p),j))^2=R s false + R s true := by
    unfold R; rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    congr with p
    rw [Fintype.sum_bool]; exact add_comm ..
  have hr₁ s : ∑ i : Shape.Page G f 2, (u (.inl (s,i)))^2 = R s false := by
    rw [Fintype.sum_prod_type,←Equiv.sum_comp (Cut.turn f)]; rfl
  have hr₂ s : ∑ i : Shape.Page G f 2, (u (.inr (.inl (s,i))))^2 = R s true := by
    rw [Fintype.sum_prod_type,←Equiv.sum_comp (Cut.turn f)]; rfl
  rw [Fintype.sum_prod_type]; -- outer slots x j
  rw [Fintype.sum_prod_type]; -- Slots
  change _ = ∑ i : Mapping.Domain G c f, _
  conv_lhs => arg 2; intro s; rw [Fintype.sum_sum_type,he,distribution_budget]
  conv_rhs => rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; arg 1; rw [Fintype.sum_prod_type]
  conv_rhs => arg 2; arg 1; rw [Fintype.sum_prod_type]
  simp_rw [hr₁,hr₂,Finset.sum_add_distrib]
  have hj : 0 < (Fintype.card Signed:ℝ) := by exact_mod_cast (Fintype.card_pos (α:=Signed))
  rw [show slip^2 = (Fintype.card Signed:ℝ)⁻¹ by rw [slip,inv_pow,Real.sq_sqrt hj.le],Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_inv_cancel_left₀ hj.ne']; abel

lemma lift_dot (u v : SourceVec G c f) :
    (lift k V *ᵥ u) ⬝ᵥ (lift k V *ᵥ v)=u ⬝ᵥ v := by
  let L := lift k V
  have he (u : SourceVec G c f) : (L *ᵥ u) ⬝ᵥ (L *ᵥ u) = u ⬝ᵥ u := by
    simpa only [dotProduct, pow_two] using distributor_sq k V u
  have hv := he (u+v)
  simp_rw [mulVec_add, dotProduct_add,add_dotProduct] at hv
  rw [he u,he v,dotProduct_comm (L *ᵥ v) (L *ᵥ u),dotProduct_comm v u] at hv
  change (L *ᵥ u) ⬝ᵥ (L *ᵥ v)=_; linarith only [hv]

lemma isometric : (lift k V).transpose * lift k V=1 := by
  let L := lift k V
  have he (u v : SourceVec G c f) : u ⬝ᵥ ((L.transpose*L) *ᵥ v) = u ⬝ᵥ v := by
    rw [←mulVec_mulVec, dotProduct_transpose_mulVec,dotProduct_comm]; exact lift_dot k V _ _
  ext i j; have h := he (Pi.single i 1) (Pi.single j 1)
  simp only [single_dotProduct,one_mul, Matrix.mulVec_single, Matrix.one_apply] at h ⊢
  simp only [MulOpposite.op_one,one_smul, Pi.single_apply,L] at h; exact h



end YM.PhysicalNext.OrderedAffine2B.Mapper
