import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Services
import YM.Push.COMMON_WITNESSES.Fields
import YM.UVNext.PRICED_KERNELS.Echo

set_option warningAsError false

/-!
# Naturality of the entire principal-window calculation

Windows in both conventions are whole colors, even though centers are link
addresses. This is essential: arbitrary orthogonal mixing of keys need not
intertwine principal cut readings. Pays attention to distinction between
reindexing and actual blockwise change of basis (e.g., the left-trivialized
fine input upon edge reversal at replica V).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Orthogonal
open Filter Function Set Matrix MeasureTheory ProbabilityTheory Next.SectorChange Gaussian Schur
open scoped Topology BigOperators Classical InnerProductSpace
variable {α β k : Type} [Fintype α] [Fintype β] [Fintype k] [DecidableEq α] [DecidableEq β] [DecidableEq k]

local notation "Mat" a => Gaussian.Table a

section block
variable (L R : α → Mat k)
def blocks : Mat (α × k) := Matrix.of fun i j => if i.1=j.1 then L i.1 i.2 j.2 else 0

def dressed (Q : Mat (α × k)) := blocks L * Q * (blocks L).transpose

def Ortho (L : α → Mat k) := ∀ i, (L i).transpose * L i = 1

omit [DecidableEq k] in
lemma mul_blocks (i j : α) (a b : k) (Q : Mat (α×k)) : (blocks L * Q) (i,a) (j,b) = ∑ c : k, L i a c * Q (i,c) (j,b) := by
  simp [Matrix.mul_apply,Fintype.sum_prod_type,blocks,ite_mul]

omit [DecidableEq k] in
lemma dressed_apply (Q : Mat (α×k)) (i j : α) (a b : k) :
    dressed L Q (i,a) (j,b) = ∑ c, (∑ d, L i a d * Q (i,d) (j,c))*L j b c := by
  unfold dressed; rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp only [transpose_apply,blocks,Matrix.of_apply,mul_ite,mul_zero]
  rw [Finset.sum_eq_single j (by intros; simp [Ne.symm ‹_›]) (by simp)]; simp only [ite_true]
  simp only [← mul_blocks L]; rfl

omit [Fintype α] [DecidableEq k] in
lemma blocks_transpose : (blocks L).transpose = blocks (fun i => (L i).transpose) := by
  ext ⟨i,a⟩ ⟨j,b⟩; by_cases h : i=j <;> simp [blocks,h, Ne.symm]

omit [DecidableEq k] in
lemma blocks_mul : blocks L * blocks R = blocks (fun i => L i * R i) := by
  ext ⟨i,a⟩ ⟨j,b⟩; rw [mul_blocks]
  by_cases h : i=j <;> simp [blocks,h,Matrix.mul_apply]

omit [Fintype α] in
lemma blocks_one : blocks (fun _ : α => (1:Mat k)) = 1 := by
  ext ⟨i,a⟩ ⟨j,b⟩; simp [blocks, Matrix.one_apply,ite_and]

lemma orth (h : Ortho L) : (blocks L).transpose * blocks L = 1 := by
  rw [blocks_transpose,blocks_mul,funext h,blocks_one]

lemma dressed_inv (h : Ortho L) (Q : Mat (α × k)) : (dressed L Q)⁻¹ = dressed L Q⁻¹ := by
  let X := blocks L
  have he : Xᵀ⁻¹ = X := Matrix.inv_eq_right_inv (orth L h)
  have hh : X⁻¹ = Xᵀ := Matrix.inv_eq_left_inv (orth L h)
  unfold dressed; change (X*Q*Xᵀ)⁻¹=X*Q⁻¹*Xᵀ; rw [Matrix.mul_inv_rev,he,Matrix.mul_inv_rev,hh,Matrix.mul_assoc]

omit [DecidableEq k] in
lemma transpose_dressed (Q : Mat (α × k)) : (dressed L Q).transpose=dressed L Q.transpose := by
  unfold dressed; rw [transpose_mul,transpose_transpose,transpose_mul,Matrix.mul_assoc]

-- Whole-color window equations

def together (k : Type) (P : α → Set α) (i : α × k) : Set (α × k) := Prod.fst ⁻¹' P i.1

def atWindow (s : Set α) : s × k ↪ α × k where
  toFun x := (x.1,x.2)
  inj' := by rintro ⟨⟨i,h⟩,k⟩ ⟨⟨j,h'⟩,l⟩ he; obtain ⟨rfl,rfl⟩ := Prod.mk.inj he; rfl

def indexWindow (s : Set α) : s × k ≃ ↥(Prod.fst ⁻¹' s : Set (α×k)) where
  toFun x := ⟨atWindow s x,x.1.property⟩
  invFun x := (⟨x.val.1,x.property⟩,x.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq k] in
lemma dressed_submatrix (s : Set α) (Q : Mat (α × k)) :
    (dressed L Q).submatrix (atWindow s) (atWindow s) = dressed (fun i : s => L i) (Q.submatrix (atWindow s) (atWindow s)) := by
  ext ⟨i,a⟩ ⟨j,b⟩; change dressed L Q (i,a) (j,b) = _; rw [dressed_apply,dressed_apply]; rfl

lemma per_at (W : α → Set α) (Q : Mat (α × k)) {i j : α} (hi : i∈W j) (hj : j∈W j) (a b : k) :
    let e := atWindow (W j) (k:=k)
    per (together k W) Q (i,a) (j,b) = ((Q.submatrix e e)⁻¹) (⟨i,hi⟩,a) (⟨j,hj⟩,b) := by
  intro e
  rw [per_read _ _ (show (j,b) ∈ together k W (j,b) from hj) hi]
  let t := indexWindow (W j) (k:=k)
  let A := principal Q (together k W (j,b))
  change A⁻¹.submatrix t t (⟨i,hi⟩,a) (⟨j,hj⟩,b) = _
  have H := Matrix.inv_submatrix_equiv A (show _ ≃ ↥(together k W (j,b)) from t) t
  exact congr_fun (congr_fun H.symm (⟨i,hi⟩,a)) (⟨j,hj⟩,b)

lemma per_off (W : α → Set α) (Q : Mat (α × k)) {i j : α} (h : ¬(i∈W j ∧ j∈W j)) (a b : k) :
    per (together k W) Q (i,a) (j,b)=0 := by
  by_cases hx : i ∈ W j
  · unfold per; exact dif_neg (mt (And.intro hx) h)
  exact per_zero _ _ hx

lemma per_ortho (W : α → Set α) (Q : Mat (α × k)) (h : Ortho L) :
    per (together k W) (dressed L Q)=dressed L (per (together k W) Q) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rw [dressed_apply]
  by_cases he : i∈W j ∧ j∈W j
  · let H : Ortho (fun i : W j => L i) := fun i => h i
    simp_rw [per_at W _ he.1 he.2]; rw [dressed_submatrix,dressed_inv _ H,dressed_apply]
  simp [per_off W _ he]
end block

def ColorOrtho (G : Gauge) (α : Type) := α → (G.Color →ₗᵢ[ℝ] G.Color)

variable {G : Gauge} (O : ColorOrtho G α)
def asMatrix : α → Mat G.ColorIndex := fun i => Matrix.of fun j k => (O i (EuclideanSpace.basisFun _ ℝ k)) j

def prices : Mat (α × G.ColorIndex) := blocks (asMatrix O)
lemma asMatrix_apply (i : α) (a : G.Color) : (asMatrix O i *ᵥ a.ofLp) = (O i a).ofLp := by
  funext j
  have he (i : G.Color) : ∑ k, i k • (EuclideanSpace.basisFun G.ColorIndex ℝ k) = i := (EuclideanSpace.basisFun _ _).sum_repr i
  nth_rw 2 [← he a]; simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,mulVec,dotProduct]; refine Finset.sum_congr rfl fun k _ => ?_; exact mul_comm (asMatrix O i j k) (a k)

lemma matrix_orth : Ortho (asMatrix O) := by
  intro i
  let L := asMatrix O i
  have hh (a b : Vec G.ColorIndex) : a ⬝ᵥ ((Lᵀ*L) *ᵥ b)=a ⬝ᵥ ((1:Mat _) *ᵥ b) := by
    let A := WithLp.toLp 2 a; let B := WithLp.toLp 2 b
    rw [one_mulVec, ← mulVec_mulVec,dotProduct_transpose_mulVec,asMatrix_apply O i A,asMatrix_apply O i B]
    rw [← dotProduct_comm,FreeResolvent.color_dot]; exact ((O i).inner_map_map A B).trans (FreeResolvent.color_dot A B).symm
  ext j k
  simpa using hh (Pi.single j 1) (Pi.single k 1)

lemma price_tape (a : Prices G α) (i : α) : tape (prices O *ᵥ a) i = O i (tape a i) := by
  ext j; rw [tape_ap]; rw [mulVec,dotProduct,Fintype.sum_prod_type]
  simp only [prices,blocks,of_apply,ite_mul,zero_mul]; rw [Finset.sum_eq_single i (by intros; simp_all [eq_comm]) (by simp)]
  simpa only [if_pos rfl,ite_true,mulVec,dotProduct,tape_ap] using! congr_fun (asMatrix_apply O i (tape a i)) j

lemma priced_orth : (prices O)ᵀ * prices O = 1 := orth _ (matrix_orth O)

lemma priced_reverse : prices O * (prices O)ᵀ=1 := mul_eq_one_comm.mp (priced_orth O)
lemma priced_surjective : Surjective (prices O *ᵥ ·) := fun v => ⟨(prices O)ᵀ *ᵥ v,by dsimp only; rw [Matrix.mulVec_mulVec v, priced_reverse, Matrix.one_mulVec]⟩

variable (e : α ≃ β)
-- acts FROM β-world to α-world

def addr (e : α ≃ β) (k : Type) := Equiv.prodCongr e (Equiv.refl k)

def move (b : Prices G β) := prices O *ᵥ (b ∘ addr e _)

def warp (A : Mat (β × G.ColorIndex)) := dressed (asMatrix O) (A.submatrix (addr e _) (addr e _))

lemma move_tape (a : Prices G β) (i : α) : tape (move O e a) i = O i (tape a (e i)) := price_tape O _ i
lemma move_surj : Surjective (move O e) := by
  intro v
  obtain ⟨w,rfl⟩ := priced_surjective O v
  exact ⟨w ∘ (addr e G.ColorIndex).symm,by unfold move; rw [show (w ∘ (addr e G.ColorIndex).symm) ∘ addr e _ = w by ext; simp]⟩

lemma move_dot (a b : Prices G β) : move O e a ⬝ᵥ move O e b = a ⬝ᵥ b := by
  unfold move
  rw [show _ ⬝ᵥ (_ *ᵥ _) = _ from (dotProduct_transpose_mulVec (prices O) _ _).symm, mulVec_mulVec, priced_orth, one_mulVec]
  rw [dotProduct_comm]; exact (addr e G.ColorIndex).sum_comp (fun i => a i * b i)

lemma warp_mv (A : Mat (β × G.ColorIndex)) (a : Prices G β) :
    warp O e A *ᵥ move O e a = move O e (A *ᵥ a) := by
  unfold warp dressed move; change (prices O * _ * (prices O)ᵀ)*ᵥ _=_
  rw [mulVec_mulVec,Matrix.mul_assoc _ _ (prices O),priced_orth, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1; funext i; exact (addr e G.ColorIndex).sum_comp (fun j => A (addr e _ i) j * a j)

lemma warp_qf (A : Mat (β × G.ColorIndex)) (a b : Prices G β) :
    move O e a ⬝ᵥ (warp O e A *ᵥ move O e b) = a ⬝ᵥ (A *ᵥ b) := by rw [warp_mv,move_dot]

lemma warp_of {A : Mat (β × G.ColorIndex)} {B : Mat (α × G.ColorIndex)}
    (H : ∀ a b : Prices G β, move O e a ⬝ᵥ (B *ᵥ move O e b) = a ⬝ᵥ (A *ᵥ b)) : B = warp O e A := by
  have h (a b : Prices G α) : a ⬝ᵥ (B *ᵥ b)=a ⬝ᵥ (warp O e A *ᵥ b) := by
    obtain ⟨x,rfl⟩ := move_surj O e a; obtain ⟨y,rfl⟩ := move_surj O e b
    rw [H,warp_qf]
  ext i j; simpa using h (Pi.single i 1) (Pi.single j 1)

lemma warp_pos (A : Mat (β × G.ColorIndex)) (ha : A.PosDef) : (warp O e A).PosDef := by
  unfold warp dressed
  have H := (ha.submatrix (addr e _).injective)
  refine H.mul_mul_conjTranspose_same (B:=prices O) ?_
  intro x y he
  have ht (x : Prices G α) : (x ᵥ* (prices O)) ᵥ* (prices O)ᵀ = x := by rw [Matrix.vecMul_vecMul,priced_reverse,Matrix.vecMul_one]
  exact (ht _).symm.trans ((congr_arg ((prices O)ᵀ.vecMul) he).trans (ht _))

lemma warp_sym (A : Mat (β × G.ColorIndex)) : Relative.symPart (warp O e A) = warp O e (Relative.symPart A) := by
  unfold Relative.symPart warp; rw [transpose_dressed]; unfold dressed; rw [transpose_submatrix, ← Matrix.add_mul,← Matrix.mul_add,← Matrix.smul_mul, ← Matrix.mul_smul]; rfl

lemma warp_inv (A : Mat (β × G.ColorIndex)) : (warp O e A)⁻¹=warp O e A⁻¹ := by rw [warp,dressed_inv _ (matrix_orth O),inv_submatrix_equiv]; rfl

lemma warp_det (A : Mat (β × G.ColorIndex)) : (warp O e A).det=A.det := by
  have h := congr_arg Matrix.det (priced_orth O)
  unfold warp dressed; unfold prices at h
  simp only [det_mul,det_submatrix_equiv_self,det_transpose,det_one] at h ⊢
  linear_combination A.det*h

lemma warp_force (A : Mat (β × G.ColorIndex)) (z : Prices G β) : Gaussian.force (warp O e A) (move O e z) = Gaussian.force A z := by
  unfold Gaussian.force; rw [warp_inv,warp_qf]

lemma warp_per (A : Mat (β × G.ColorIndex)) {W : β × G.ColorIndex → Set (β × G.ColorIndex)} {w : α → Set α}
    (he : ∀ i, addr e _ ⁻¹' W (addr e _ i) = together _ w i) :
    per (together G.ColorIndex w) (warp O e A) = warp O e (per W A) := by unfold warp; rw [per_ortho _ _ _ (matrix_orth O),per_relabel, funext he]





end YM.AnalyticBridge.GaussianFieldAlignment.Orthogonal
