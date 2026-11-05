import YM.Push.LOOP_COEFFICIENT.Block.Basis
import YM.Push.LOOP_COEFFICIENT.Block.Induce

/-!
# Exact matrix tests in dephased distributed-weight coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Filter Lattice Laurent RG Bloch Complex Portal 
open scoped Topology BigOperators Matrix.Norms.L2Operator ContDiff
variable {L : Side} {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]  [Fintype d]

def versor (L : Side) (a : Type) [DecidableEq a] [Fintype a] := distributed L a (fun _ _ => 1) fun _ _ => zero_lt_one

def beam {a : Type} (l : Site L) (x : CSpace (Co L a)) : CSpace a := fun i => x (l,i)
variable (v u : Weight L) (hv : ∀ q i,0<v q i) (hu : ∀ q i,0<u q i) (X : Vertex c a b) (Y : Profiles L c d) (q p s : Momentum)

lemma channel_pair (i j : Site L) (x y) (M : Matrix a b ℂ) :
    x ⬝ᵥ reduce (distributed L a v hv).dual (distributed L b u hu) q p (channel q p i j M) *ᵥ y = ((v (-q) (-i) * u p j : ℝ):ℂ)* (beam (-i) x ⬝ᵥ M *ᵥ beam j y) := by
  rw [reduce_apply,dual_inv]; change x ⬝ᵥ (((pane L a v (-q)).transpose * (place a q i * M * select b p j)) * pane L b u p) *ᵥ y = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (select b p j),← mulVec_mulVec,dotProduct_mulVec,← vecMul_vecMul, pane_place, ← mulVec_mulVec,select_pane, dotProduct_smul, smul_vecMul,smul_dotProduct,dotProduct_mulVec]
  unfold beam; push_cast; simp only [smul_eq_mul]; field_simp [side_ne L]
lemma base_pair (x y) : x ⬝ᵥ (weigh (distributed L a v hv).dual (distributed L b u hu) (induce X Y)).base q *ᵥ y = ∑ i, ((v (-q) (-i) * u q i : ℝ):ℂ)* (beam (-i) x ⬝ᵥ X.base (aliasAt q i) *ᵥ beam i y) := by simp only [weigh,induce,map_sum, Matrix.sum_mulVec,dotProduct_sum, channel_pair]
lemma one_pair (z x y) : x ⬝ᵥ (weigh (distributed L a v hv).dual (distributed L b u hu) (induce X Y)).one q p z *ᵥ y = ∑ j,∑ i, ((v (-(q+p)) (-(i+j))*u q i:ℝ):ℂ)*(beam (-(i+j)) x ⬝ᵥ X.one (aliasAt q i) (aliasAt p j) (Y p j *ᵥ z) *ᵥ beam i y) := by simp only [weigh,induce,map_sum, LinearMap.comp_apply, Matrix.mulVecLin_apply,LinearMap.sum_apply, Matrix.sum_mulVec,dotProduct_sum, channel_pair]
lemma two_pair (z w x y) : x ⬝ᵥ (weigh (distributed L a v hv).dual (distributed L b u hu) (induce X Y)).two q p s z w *ᵥ y = ∑ j,∑ l,∑ i, ((v (-(q+p+s)) (-(i+(j+l)))*u q i:ℝ):ℂ)*(beam (-(i+(j+l))) x ⬝ᵥ X.two (aliasAt q i) (aliasAt p j) (aliasAt s l) (Y p j *ᵥ z) (Y s l *ᵥ w) *ᵥ beam i y) := by simp only [weigh,induce,map_sum, LinearMap.compr₂_apply,LinearMap.compl₁₂_apply,Matrix.mulVecLin_apply,LinearMap.sum_apply, Matrix.sum_mulVec,dotProduct_sum,channel_pair]
lemma base_action (i : Site L) (x) : beam (-i) ((weigh (distributed L a v hv).dual (distributed L b u hu) (induce X Y)).base q *ᵥ x) = ((v (-q) (-i)*u q i:ℝ):ℂ) • (X.base (aliasAt q i) *ᵥ beam i x) := by
  ext1 k; let y : CSpace (Co L a) := Pi.single (-i,k) 1
  have he (l : Site L) : beam (-l) y = if i=l then Pi.single k 1 else 0 := by ext; unfold beam y; simp [Pi.single_apply,ite_apply, ite_and]; split_ifs <;> simp_all
  simpa only [y,beam,single_dotProduct,one_mul,he,show ∀ i j (z : CSpace a), (if i=j then Pi.single k (1:ℂ) else 0) ⬝ᵥ z = _ from fun (i j : Site L) z => apply_ite (· ⬝ᵥ z) ..,zero_dotProduct,mul_ite,mul_zero, Finset.sum_ite_eq, Finset.mem_univ, reduceIte] using! base_pair v u hv hu X Y q y x


end YM.Push.Loops.Block
