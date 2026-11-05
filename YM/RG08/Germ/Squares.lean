import YM.RG08.Germ.Patches
import YM.RG08.Gaussian.Mean

/-! # Equality of full and cover leading operators, finite true periods

Log conventions at Link/Body include color. True Hessian
and log germ, factor TWO. No rotating/capture/mixed field horizon. The
covariance used is the unperturbed K from parts I-III. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree Bid
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {c f L : Side} (S : StepData c f) {G : Gauge}
variable {C V : FreeResolvent.FaceRow} {U : Matrix (Body 1 f) (Body 1 c) ℝ}

-- residual is literal noise kernel operand. dotProduct neck
private def palette (x : Link G c × Link G f) := x.1-patron G (probe S)*ᵥ x.2
lemma palette_fog (x : Link G c × Link G f) : palette S x= FreeResolvent.flatten
    (Work.F03.residual S (arm G c 1 x.1,arm G f 1 x.2)) := by
  funext i; rcases i with ⟨i,j,v⟩; unfold Work.F03.residual palette
  rw [Pi.sub_apply,tensor_same]; change _-FreeResolvent.component (FreeResolvent.tensor G (probe S) *ᵥ x.2) v (i,j)=_
  rw [FreeResolvent.component_mul]; rfl

theorem jasper (t : S.Choices) (i : G.ColorIndex) (hp : S.patch.Branches S.kernel G) :
    let V:=noiseLaw S t (G:=G)
    let X (x : Alley G S.ratio) := palette S (coarseL G S.ratio x,fineL G S.ratio x)
    V 0=0 ∧ fderiv ℝ V 0=0 ∧ ∀ x y,iteratedFDeriv ℝ 2 V 0 ![x,y]= S.kernel.penalty * dotProduct (X x) (X y) := by
  intro V X
  apply Work.F03.hessian_of_limit (f:=V) (blot_true S t i hp 2).1.contDiffAt
  · intro x
    unfold X; rw [palette_fog, FreeResolvent.flat_dot];
    unfold V noiseLaw input; simp_rw [map_smul]; exact Work.F03.noise_limit hp t (arm G c 1 (coarseL G S.ratio x),arm G f 1 (fineL G S.ratio x))
  · intro x y z
    rw [show X (x+y)= X x + X y by simp only [X,map_add,palette, Matrix.mulVec_add]; abel,add_dotProduct,mul_add]
  · intro x y; exact congr_arg (S.kernel.penalty*·) (dotProduct_comm ..)

lemma price_stanza (G : Gauge) {V : FreeResolvent.FaceRow} (h : Whole V) (hp : ∀ c, (V.acts c)ᵀ=V.acts c) (m : Side) :
    let K := quad G (hessian V)
    Tunable K ∧ Glows K ∧ ∀ v : Link G m, stanza K m v=(1/2:ℝ)*dotProduct v (patron G (Precision.K (V.acts m))*ᵥ v) := by
  intro R
  obtain ⟨w,A,hv,H⟩ := hessian_whole h; let M := colored G (hessian V)
  have he m : (M.acts m)ᵀ=M.acts m := by unfold M; rw [colored_acts,hessian_acts h,FreeResolvent.tensor_transpose, k_symmetric (hp m)]
  obtain ⟨hx,hH,H⟩:= clipQ_tunable M (colored_price G H) hv.le he
  refine ⟨hH,⟨_,_,hv,hx⟩,fun v=>?_⟩
  change recital (clipQ M) _ _=_; rw [H]; unfold M; rw [colored_acts,hessian_acts h,tensor_same]

lemma ticket_stanza (t : S.Choices) (i : G.ColorIndex) (hp : S.patch.Branches S.kernel G) (v : Alley G S.ratio) :
    stanza (blot i S.patch S.kernel.penalty 2) c v= (1/2:ℝ)*(S.kernel.penalty * dotProduct (palette S (coarseL G S.ratio v,fineL G S.ratio v)) (palette S (coarseL G S.ratio v,fineL G S.ratio v))) := by
  unfold stanza Tensor.diagonal; rw [← (blot_true S t i hp 2).2];
  rw [show (fun _ : Fin 2=> v)=![v,v] from funext fun j=> by fin_cases j <;> rfl,Tensor.coeff]; change ((2:ℕ).factorial:ℝ)⁻¹ * iteratedFDeriv ℝ 2 (noiseLaw S t) 0 ![v,v]=_; rw [(jasper S t i hp).2.2]; norm_num [Nat.factorial]

-- Taylor quadratic not exp action yet. linear cross c and complete.
def bedOper (C : FreeResolvent.FaceRow) (u : Link G f) (x : Link G c) := dotProduct u (patron G (K (C.acts f)) *ᵥ u)+ S.kernel.penalty * dotProduct (palette S (x,u)) (palette S (x,u))
def riseM (G : Gauge) (T : Forest S.ratio) (U : Matrix (Body 1 f) (Body 1 c) ℝ) := patron G (extracted S T U)
lemma bed_value (h : Inputs S U (C.acts f) (V.acts c)) (T : Forest S.ratio) (v : Link G c) :
    bedOper S C (riseM S G T U *ᵥ v) v= dotProduct v (patron G (K (V.acts c)) *ᵥ v) := by
  calc
    _ = ∑ i:G.ColorIndex,
       FreeResolvent.component v i ⬝ᵥ ((Precision.K (V.acts c))*ᵥ FreeResolvent.component v i) := ?_
    _ = _ := by rw [FreeResolvent.component_dot,tensor_same]; apply Finset.sum_congr rfl; intro i _; rw [FreeResolvent.component_mul]
  let y := riseM S G T U*ᵥ v
  rw [bedOper,FreeResolvent.component_dot,FreeResolvent.component_dot,Finset.mul_sum,← sum_add_distrib]; apply sum_congr rfl; intro i _
  rw [tensor_same,FreeResolvent.component_mul, riseM,tensor_same,FreeResolvent.component_mul]
  let L := extracted S T U; let M := K (C.acts f); let P:=1-probe S* L
  let Q:= FreeResolvent.component v i
  have hx : FreeResolvent.component (palette S (v, FreeResolvent.tensor G L *ᵥ v)) i=P *ᵥ Q := by
    unfold palette P; rw [sub_mulVec, Matrix.one_mulVec, ← mulVec_mulVec,tensor_same]
    change Q-FreeResolvent.component (FreeResolvent.tensor G (probe S) *ᵥ (FreeResolvent.tensor G L *ᵥ v)) i=_; rw [FreeResolvent.component_mul,FreeResolvent.component_mul]
  rw [hx, ← Precision.action T U (C.acts f) (V.acts c) h, add_mulVec, dotProduct_add, Matrix.smul_mulVec,dotProduct_smul];
  change L *ᵥ Q ⬝ᵥ (M *ᵥ (L *ᵥ Q)) + S.kernel.penalty*(P *ᵥ Q ⬝ᵥ (P *ᵥ Q))= _ -- precedence
  simp only [Matrix.mul_assoc,← Matrix.mulVec_mulVec]; conv_rhs => rw [Matrix.dotProduct_mulVec,vecMul_transpose,Matrix.dotProduct_mulVec _ ((1 - probe S * extracted S T U)ᵀ),vecMul_transpose]
  rfl
lemma color_bed_cross (S : StepData c f) (C : FreeResolvent.FaceRow) (v : Link G f) :
    bedOper S C v 0= v ⬝ᵥ (FreeResolvent.fullMatrix G S C *ᵥ v) := by
  let M:= K (C.acts f); let T:= patron G (probe S)
  have he : FreeResolvent.fullMatrix G S C=patron G M+S.kernel.penalty • (Tᵀ*T) := by
    unfold FreeResolvent.fullMatrix FreeResolvent.baseMatrix; rw [← tensor_same,patron_add,patron_scale,patron_mul,patron_star]
  have ht : v ⬝ᵥ ((Tᵀ*T)*ᵥ v)= (T *ᵥ v) ⬝ᵥ (T *ᵥ v) := by rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,vecMul_transpose]
  rw [bedOper,he,Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,ht]; simp only [palette, zero_sub, neg_dotProduct, dotProduct_neg,neg_neg]; rfl
lemma bed_as (S : StepData c f) (C : FreeResolvent.FaceRow) (u : Link G f) (x : Link G c) :
    bedOper S C u x= bedOper S C u 0 + S.kernel.penalty*(x ⬝ᵥ x)-2*S.kernel.penalty*(u ⬝ᵥ ((patron G (probe S))ᵀ *ᵥ x)) := by
  unfold bedOper palette; dsimp only
  let Q := patron G (probe S)
  have he : (patron G (probe S)*ᵥ u) ⬝ᵥ x=u ⬝ᵥ (Qᵀ*ᵥ x) := by rw [Matrix.dotProduct_mulVec, vecMul_transpose]
  rw [zero_sub]; simp only [sub_dotProduct,dotProduct_sub, neg_dotProduct,dotProduct_neg,neg_neg,he];
  rw [dotProduct_comm _ (patron G (probe S)*ᵥ u),he]; unfold Q; ring

theorem bed_gather (h : Inputs S U (C.acts f) (V.acts c)) (hs : (C.acts f)ᵀ=C.acts f) (T : Forest S.ratio)
    (x : FreeResolvent.Active G T→ℝ) (v : Link G c) :
    bedOper S C ((riseM S G T U*ᵥ v)+(sprig S T G*ᵥ x)) v = dotProduct v (patron G (K (V.acts c)) *ᵥ v)+ dotProduct x (FreeResolvent.treeMatrix G S T C *ᵥ x) := by
  let I := sprig S T G; let P := riseM S G T U; let Q := P*ᵥ v; let N:=FreeResolvent.fullMatrix G S C; let z:=I *ᵥ x
  let R:= patron G (probe S); let l:= S.kernel.penalty
  have hs : Nᵀ=N := FreeResolvent.full_symmetric C hs
  have hn : N*P=l • Rᵀ := by
    unfold N R P l riseM FreeResolvent.fullMatrix; rw [← tensor_same, ← patron_mul, determinant_weight S h T, patron_scale,patron_star]
  have hz : N*ᵥ Q=l • (Rᵀ*ᵥ v) := by unfold Q; rw [mulVec_mulVec, hn, Matrix.smul_mulVec]
  have hW : Q ⬝ᵥ (N *ᵥ z)=z ⬝ᵥ (N *ᵥ Q) := by rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,hs,dotProduct_comm]
  have hF : z ⬝ᵥ (N*ᵥ z)= dotProduct x (FreeResolvent.treeMatrix G S T C*ᵥ x) := FreeResolvent.insertion.dot_compress (FreeResolvent.plant T) N x x
  rw [← bed_value S h T v,bed_as S C (_+_) _,bed_as S C (riseM S G T U*ᵥ v) v,color_bed_cross,color_bed_cross]
  -- polarization
  change (Q+z) ⬝ᵥ (N*ᵥ(Q+z)) + l*(v ⬝ᵥ v) - 2*l*((Q+z) ⬝ᵥ (Rᵀ*ᵥ v))=(Q ⬝ᵥ (N*ᵥ Q)+l*(v ⬝ᵥ v)-2*l*(Q ⬝ᵥ (Rᵀ*ᵥ v)))+_
  rw [Matrix.mulVec_add]; simp_rw [dotProduct_add,add_dotProduct,hW,hF,hz,dotProduct_smul]; simp only [smul_eq_mul]; ring
end YM.RG08
