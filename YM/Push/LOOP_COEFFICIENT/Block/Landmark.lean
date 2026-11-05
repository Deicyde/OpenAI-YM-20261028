import YM.Push.LOOP_COEFFICIENT.Block.Direct
import YM.Push.LOOP_COEFFICIENT.Block.Spire

/-!
# The aggregate free reference
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Filter Lattice Laurent Bloch RG Precision Exterior Wilson Complex Portal Fine
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {L c f : Side} {G : Gauge} {e g η σ A C : ℝ} {p : Clip} {W : PathData G} {Y : Lights G L}


def front (G : Gauge) (L : Side) : Vertex (Axes G) (VectorBlock G L) (JointType G L) := Vertex.const fun _ => inlet ℂ _ _
def rear (G : Gauge) (L : Side) : Vertex (Axes G) G.ColorIndex (JointType G L) := Vertex.const fun _ => attic ℂ _ _
def mounted (M : Vertex (Axes G) (VectorBlock G L) (VectorBlock G L)) := (((front G L).transpose.mul M).mul (front G L))
def torch (Y : Lights G L) := (mill Y).mul (front G L)
def roof (G : Gauge) (L : Side) := (rear G L).transpose.mul (rear G L)
def station (Y : Lights G L) (W : PathData G) (p : Clip) := (((mounted (slab Y W p)).add ((torch Y).transpose.mul (torch Y))).add (mounted (ash Y))).add (roof G L)
















variable {r : Ratio c f} {B : Matrix (BondKey G f) (BondKey G c) ℝ} {T : Lights G r.count}
def projectCoarse (G : Gauge) (c f : Side) := (attic ℝ (BondKey G f) (SiteKey G c)).submatrix id (Equiv.sumProdDistrib ..)
lemma project_inlet (G : Gauge) (c f : Side) : projectFine G c f = (inlet ℝ (BondKey G f) (SiteKey G c)).submatrix id (Equiv.sumProdDistrib ..) := by ext i ⟨j|j,k⟩ <;> simp [inlet,projectFine,LinearMap.toMatrix'_apply,Pi.single_apply,eq_comm,Prod.ext_iff]
lemma project_enlarge (M : Matrix (BondKey G f) (BondKey G f) ℝ) : enlarge c M = (projectFine G c f).transpose * M * projectFine G c f + (projectCoarse G c f).transpose * projectCoarse G c f := by
  rw [enlarge,project_inlet,projectCoarse,← direct_sum,Matrix.submatrix_add,Pi.add_apply,Pi.add_apply, Matrix.mul_one,transpose_submatrix,transpose_submatrix,Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id M];

lemma project_routed (G : Gauge) (r : Ratio c f) (k : Site c) : Routed (coarseLinks G r) (jointGrid G r) k k (cmat (projectFine G c f)) (inlet ℂ _ _) ∧ Routed (nodesGrid G c) (jointGrid G r) k k (cmat (projectCoarse G c f)) (attic ℂ _ _) := by
  rw [project_inlet,projectCoarse]
  have he (i : BondKey G f) : (cmat ((inlet ℝ (BondKey G f) (SiteKey G c)).submatrix id (Equiv.sumProdDistrib ..))) i = Pi.single (.inl i.1,i.2) 1 := by ext ⟨j|j,a⟩ <;> simp [cmat_apply,Bloch.approached,inlet, apply_ite (fun x : ℝ => (x:ℂ)), Pi.single_apply,Prod.ext_iff,eq_comm]
  have ht (i : SiteKey G c) : (cmat ((attic ℝ (BondKey G f) (SiteKey G c)).submatrix id (Equiv.sumProdDistrib ..))) i = Pi.single (.inr i.1,i.2) 1 := by ext ⟨j|j,a⟩ <;> simp [cmat_apply,Bloch.approached,attic, apply_ite (fun x : ℝ => (x:ℂ)), Pi.single_apply,Prod.ext_iff,eq_comm]
  constructor <;> apply Routed.of_vector <;> intro v
  · ext1 i; rw [show ∀ M : Matrix (BondKey G f) (JointKey G c f) ℂ, ∀ w,(M *ᵥ w) i = M i ⬝ᵥ w from fun _ _ => rfl,he,single_dotProduct,one_mul,plane_apply,plane_apply,inlet_eval]; rfl
  ext1 i; rw [show ∀ M : Matrix (SiteKey G c) (JointKey G c f) ℂ, ∀ w,(M *ᵥ w) i = M i ⬝ᵥ w from fun _ _ => rfl,ht,single_dotProduct,one_mul,plane_apply,plane_apply,attic_eval]; rfl
open scoped Matrix.Norms.Frobenius
lemma front_models (G : Gauge) (r : Ratio c f) : Models (linksGrid G c) (coarseLinks G r) (jointGrid G r) (fun _ => projectFine G c f) (front G r.count) := Models.const fun i _ _ => (project_routed G r i).1
lemma rear_models (G : Gauge) (r : Ratio c f) : Models (linksGrid G c) (nodesGrid G c) (jointGrid G r) (fun _ => projectCoarse G c f) (rear G r.count) := Models.const fun i _ _ => (project_routed G r i).2
lemma station_models (hY : Projects r (linksGrid G f) (linksGrid G c) (cmat B) T) (h : W.Bounds p σ A e) : Models (linksGrid G c) (jointGrid G r) (jointGrid G r) (fun z => enlarge c (reference (r.count.val:ℝ)⁻¹ p W (vary 1 (B *ᵥ z)))) (station T W p) := by
  have hf := front_models G r; have hg := rear_models G r; have he := (mill_models hY).mul hf
  convert! (((((hf.transpose.mul (slab_models hY h)).mul hf).add (he.transpose.mul he)).add ((hf.transpose.mul (ash_models hY)).mul hf)).add (hg.transpose.mul hg)) using 1
  funext z; rw [project_enlarge,reference, pow_two]; simp [Matrix.mul_add,Matrix.add_mul,transpose_mul,Matrix.mul_assoc,regulation_symm]
end YM.Push.Loops.Block
