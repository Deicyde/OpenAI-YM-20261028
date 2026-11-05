import YM.Push.LOOP_COEFFICIENT.Block.Columns
import YM.Push.LOOP_COEFFICIENT.ContinuumTrace

/-!
# Coarsening a translation vertex along a projected external column
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Lattice Laurent Bloch RG Precision Wilson  Complex
open scoped BigOperators
variable {a b c d e : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [DecidableEq a] [DecidableEq b] [DecidableEq d] [DecidableEq e]
  {L s f : Side}

def channel (q p : Momentum) (r l : Site L) : Matrix a b ℂ →ₗ[ℂ] Matrix (Co L a) (Co L b) ℂ := ((matrixMulLinear _ _ _ _).flip (select b p l)).comp (matrixMulLinear _ _ _ ℂ (place a q r))

def induce (V : Vertex d a b) (Y : Loops.Profiles L d e) : Vertex e (Co L a) (Co L b) where
  base q := ∑ i, channel q q i i (V.base (aliasAt q (L:=L) i))
  one q p := ∑ j,∑ i, ((channel (q+p) q (i+j) i).comp (V.one (aliasAt q i) (aliasAt p j))).comp (Y p j).mulVecLin
  two q p s := ∑ j, ∑ l, ∑ i, ((V.two (aliasAt q i) (aliasAt p j) (aliasAt s l)).compr₂ (channel (q+p+s) q (i+(j+l)) i)).compl₁₂ (Y p j).mulVecLin (Y s l).mulVecLin

variable {J E F H : Type} [Fintype J] [Fintype E] [Fintype F] [Fintype H] [DecidableEq J] [DecidableEq E] [DecidableEq F] [DecidableEq H]
  {g : Ratio s f} {A : Grid s J e} {B : Grid f H d} {M : Grid f E a} {N : Grid f F b}
  {X : Jet H (Matrix E F ℂ)} {P : Matrix H J ℂ} {V : Vertex d a b} {Y : Loops.Profiles g.count d e}

omit [DecidableEq J] [DecidableEq E] [DecidableEq F] [DecidableEq H] [Fintype E] [Fintype H] in
lemma induce_synced (hX : Synced B M N X V) (hP : Projects g B A P Y) : Synced A (M.trans (splitCo g a)) (N.trans (splitCo g b)) (X.pre P.mulVecLin) (induce V Y) := by
  have h (z) (v : CSpace e) : P.mulVecLin (plane A (wrap s z) *ᵥ v) = ∑ i, plane B (aliasSite g z i) *ᵥ (Y (quant s z) i *ᵥ v) := by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,hP, Matrix.sum_mulVec]; simp only [mulVec_mulVec]
  constructor
  · rintro q k ⟨z,rfl,rfl⟩; simpa only [add_zero] using! eliminate (l:=0) (W:=fun i => V.base (aliasAt (quant s z) i)) (g:=g) (q:=z) (p:=z) (fun i => by simpa only [add_zero] using! hX.base (alias_match g z i))
  · rintro q p k i ⟨z,rfl,rfl⟩ ⟨t,rfl,rfl⟩ v
    simp only [induce,Jet.pre,LinearMap.comp_apply,h,map_sum,LinearMap.sum_apply,Routed,Matrix.mul_sum,Matrix.sum_mul]; apply Finset.sum_congr rfl fun i _ => ?_
    simp_rw [← Matrix.mul_sum]
    have he := eliminate (q:=z) (p:=z+t) (l:=i) (A:=M) (B:=N) (M:=X.lin (plane B (aliasSite g t i) *ᵥ (Y (quant s t) i *ᵥ v))) (W:=fun j => V.one (aliasAt (quant s z) j) (aliasAt (quant s t) i) (Y (quant s t) i *ᵥ v)) (fun j => by rw [aliasSite_add]; exact hX.one (alias_match g z j) (alias_match g t i) _)
    rw [map_add,quant_add] at he; exact he
  rintro q p r k i j ⟨z,rfl,rfl⟩ ⟨t,rfl,rfl⟩ ⟨u,rfl,rfl⟩ v w
  simp only [induce,Jet.pre,LinearMap.compl₁₂_apply,h,map_sum,LinearMap.sum_apply,LinearMap.compr₂_apply,Routed,Matrix.mul_sum,Matrix.sum_mul]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.mul_sum]; have he := eliminate (q:=z) (p:=z+t+u) (l:=(i+j)) (M:=X.quad (plane B (aliasSite g t i) *ᵥ (Y (quant s t) i *ᵥ v)) (plane B (aliasSite g u j) *ᵥ (Y (quant s u) j *ᵥ w))) (W:=fun l => V.two (aliasAt (quant s z) l) (aliasAt (quant s t) i) (aliasAt (quant s u) j) (Y (quant s t) i *ᵥ v) (Y (quant s u) j *ᵥ w)) (fun l => ?_) (A:=M) (B:=N)
  · rw [map_add,map_add,quant_add,quant_add] at he; exact he
  rw [← add_assoc,aliasSite_add,aliasSite_add]; exact hX.two (alias_match g z l) (alias_match g t i) (alias_match g u j) _ _
end YM.Push.Loops.Block
