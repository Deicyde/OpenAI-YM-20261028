import YM.Push.LOOP_COEFFICIENT.KineticReal
import YM.Push.LOOP_COEFFICIENT.LoopRow

/-!
# Actual quadratic path evaluation in real coordinates

No direct use of an off-mesh kernel in differentiating a path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Lattice RG Wilson Precision Exterior Bloch Laurent
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {W : PathData G} {σ C : ℝ}

def curlColored (G : Gauge) (n : Side) : Matrix (FaceKey G n) (BondKey G n) ℝ := LinearMap.toMatrix' (LinearMap.pi fun i : FaceKey G n =>
   (LinearMap.proj (i.1.1,plaquette i.1.2)).comp ((d 1 n).mulVecLin.comp (layer G n i.2)))
lemma curl_apply (x : Loops.Links G n) (b) (i : G.ColorIndex) :
    (curlColored G n *ᵥ x) (b,i) = Work.F03.faceCurl b (chartEquiv G n x) i := by
  rw [curlColored,LinearMap.toMatrix'_mulVec]; change (d 1 n *ᵥ layer G n i x) _ = _; rw [layer_eq]; rfl

def loopFaces (W : PathData G) (n : Side) : Matrix (FaceKey G n) (FaceKey G n) ℝ := ((loopRow W).acts n).submatrix (faceGrid G n) (faceGrid G n)

private lemma restrict_abs (i j : Sides G) (k) : |atomRow W i j k| ≤ (W.loop k).magnitude := by
  unfold atomRow PathData.loop_coeff; split
  · exact Finset.single_le_sum (fun i _ => abs_nonneg ((W.loop k).coeff i)) (Finset.mem_univ _)
  rw [abs_zero]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

variable (hs : 0<σ) (hb : SumBudget (fun i => (W.loop i).budget σ) C)
include hs hb
lemma atomRow_terms (i j : Sides G) : Summable (atomRow W i j) := Summable.of_norm_bounded hb.2.1 (fun k => (restrict_abs i j k).trans ((W.loop k).lower_budget σ hs))
lemma loopFaces_entry (x y : Site n) (i j : Sides G) : loopFaces W n ((x,i.1),i.2) ((y,j.1),j.2) = ∑' k,
    if y=x+wrap n (deltaPos W k) then atomRow W i j k else 0 := packed_period (deltaPos W) (atomRow_terms hs hb i j) (fun z => y=x+wrap n z)

private def segment (W : PathData G) (v : FaceKey G n → ℝ) (i j : FaceKey G n) (k : ℕ) := v i * ((if j.1.1 = i.1.1 + wrap n (deltaPos W k) then atomRow W (faceGrid G n i).2 (faceGrid G n j).2 k else 0)*v j)
private lemma seg_terms (v : FaceKey G n → ℝ) (i j) : Summable (segment W v i j) := by
  refine Summable.mul_left (v i) (Summable.mul_right (v j) (Summable.of_norm_bounded hb.2.1 fun k => ?_))
  split
  · exact (restrict_abs ..).trans ((W.loop k).lower_budget σ hs)
  rw [norm_zero]; exact hb.1 k

omit hs hb in
private lemma sum_tsum₂ {a b c : Type} [Fintype a] [Fintype b] {f : a → b → c → ℝ} (hf : ∀ x y, Summable (f x y)) :
    ∑ x, ∑ y, ∑' i, f x y i = ∑' i, ∑ x, ∑ y, f x y i := by
  simp_rw [← Summable.tsum_finsetSum (fun y _ => hf _ y)]; exact (Summable.tsum_finsetSum (fun x _ => summable_sum (fun y (_:y∈Finset.univ) => hf x y))).symm

omit hs hb in
private lemma segment_at (v : FaceKey G n → ℝ) (k : ℕ) (x : Site n) :
    ∑ i : Sides G, ∑ b : FaceKey G n, segment W v ((wrap n (((W.loop k).leg 0).offset)+x,i.1),i.2) b k =
      (W.loop k).poly (fun j => paint G (Face (Per n)) v (Work.F03.slotFace ((W.loop k).leg j) x)) := by
  let A := W.loop k
  let z₀ := wrap n ((A.leg 0).offset)+x; let z₁ := wrap n ((A.leg 1).offset)+x
  have he : wrap n ((A.leg 0).offset) + x + wrap n (deltaPos W k) = z₁ := by dsimp [deltaPos,z₁,A]; rw [map_sub]; abel
  have hm (a b : PlaqAxes) : (fun j => (A.leg j).plaq) = ![a,b] ↔ (A.leg 0).plaq = a ∧ (A.leg 1).plaq = b := by simp only [funext_iff,Fin.forall_fin_two]; rfl
  change _ = A.poly _
  simp only [segment, Atom.poly, Fintype.sum_prod_type,atomRow, PathData.loop_coeff,faceGrid,Equiv.prodAssoc_apply, ← show A = W.loop k from rfl,he, hm, Fin.prod_univ_two,Work.F03.slotFace,paint_apply,ite_mul, mul_ite,mul_zero,zero_mul]
  simp only [ite_and, Finset.sum_ite_eq',Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq, Finset.mem_univ,if_true]
  rw [← Equiv.sum_comp (finTwoArrowEquiv G.ColorIndex).symm (fun b => A.coeff b * _),Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have ht : (finTwoArrowEquiv G.ColorIndex).symm (i,j) = ![i,j] := by ext k; fin_cases k <;> rfl
  rw [ht]; dsimp [z₁]; ring

lemma loopFaces_pair (v : FaceKey G n → ℝ) : v ⬝ᵥ (loopFaces W n *ᵥ v) =
    ∑ x : Site n,∑' k, (W.loop k).poly (fun j => paint G _ v (Work.F03.slotFace ((W.loop k).leg j) x)) := by
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  calc
    _ = ∑ i,∑ j,∑' k, segment W v i j k := Finset.sum_congr rfl fun ⟨⟨x,a⟩,i⟩ _ => Finset.sum_congr rfl fun ⟨⟨y,b⟩,j⟩ _ => by
      rw [show loopFaces W n _ _ = _ from loopFaces_entry hs hb x y (a,i) (b,j)]
      rw [← tsum_mul_right,← tsum_mul_left]; rfl
    _ = _ := by
      have ht x : Summable fun k => (W.loop k).poly (fun j => paint G _ v (Work.F03.slotFace ((W.loop k).leg j) x)) :=
        Summable.of_norm_bounded (hb.2.1.mul_right (‖paint G _ v‖^2)) (fun k => (Work.F03.poly_bound _ _ ‖paint G _ v‖ (fun j => norm_le_pi_norm _ _)).trans (mul_le_mul_of_nonneg_right ((W.loop k).lower_budget σ hs) (sq_nonneg _)))
      rw [sum_tsum₂ (seg_terms hs hb v), ← Summable.tsum_finsetSum (fun i _ => ht i)]; refine tsum_congr fun k => ?_
      rw [← Equiv.sum_comp (faceGrid G n).symm, Fintype.sum_prod_type,← Equiv.sum_comp (Equiv.addLeft (wrap n (((W.loop k).leg 0).offset)))]
      exact Finset.sum_congr rfl fun x _ => segment_at v k x

def rawLoop (W : PathData G) (n : Side) := (curlColored G n).transpose * (loopFaces W n + (loopFaces W n).transpose) * curlColored G n
lemma rawLoop_pair (x : Loops.Links G n) : x ⬝ᵥ (rawLoop W n *ᵥ x) / 2 =
    ∑ z : Site n,∑' k, (W.loop k).poly (fun j => Work.F03.faceCurl (Work.F03.slotFace ((W.loop k).leg j) z) (chartEquiv G n x)) := by
  rw [rawLoop,← mulVec_mulVec, ← mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,add_mulVec,dotProduct_add, Matrix.dotProduct_transpose_mulVec,loopFaces_pair hs hb]
  simp_rw [show ∀ b,paint G _ (curlColored G n *ᵥ x) b = _ from fun b => (PiLp.ext fun i => curl_apply x b i)]; ring

def loopPrice (W : PathData G) (n : Side) : Matrix (BondKey G n) (BondKey G n) ℝ := (Fintype.card Signed:ℝ)⁻¹ • ∑ s : Signed,
    (linkSpin s 1).transpose * rawLoop W n * linkSpin s 1
omit hs hb in lemma loopPrice_symm : (loopPrice W n).transpose = loopPrice W n := by simp [loopPrice,rawLoop, Matrix.transpose_sum,Matrix.mul_assoc,add_comm]

lemma loopPrice_limit (x : Loops.Links G n) : Tendsto (fun t : ℝ => loop W (vary 1 (t • x))/t^2) (𝓝[≠] 0) (𝓝 (x ⬝ᵥ (loopPrice W n *ᵥ x) / 2)) := by
  rw [loopPrice,Matrix.smul_mulVec,Matrix.sum_mulVec,dotProduct_smul,dotProduct_sum, smul_eq_mul,mul_div_assoc,Finset.sum_div]
  simp_rw [loop,Patch.average, ← represent_chart, map_smul, Work.F03.represent_pulled, ← chart_pulled,← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,mul_div_assoc,Finset.sum_div]
  simp_rw [← Matrix.dotProduct_mulVec, rawLoop_pair hs hb]
  exact Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => Work.F03.atoms_limit _ W.loop hs hb)

lemma loop_jets_real : (loop W ∘ vary (1:Config G n)) 0 = 0 ∧ fderiv ℝ (loop W ∘ vary (1:Config G n)) 0 = 0 ∧ bilinearAt (loop W ∘ vary 1) 0 = loopPrice W n := by
  have hd : ContDiffAt ℝ ω (loop W ∘ vary (1:Config G n)) 0 := by
    apply contDiffAt_const.mul
    refine ContDiffAt.sum fun s _ => Work.F02.uncut_contDiffAt hs hb (A:=pull s 0 ∘ vary (1:Config G n)) (fun i => ?_)
    dsimp only [Function.comp_apply]; unfold pull Step.read; split <;> first | exact mat_inv_diff (vary_diff _) | exact vary_diff _
  obtain ⟨he,hf,hg⟩ := Work.F03.hessian_of_limit (Q:=fun x y => x ⬝ᵥ (loopPrice W n *ᵥ y)) (hd.of_le le_top) (loopPrice_limit hs hb)
    (fun x y z => add_dotProduct x y _) (fun x y => by rw [← Matrix.dotProduct_transpose_mulVec,loopPrice_symm])
  exact ⟨he,hf,pairing_ext fun x y => (bilinearAt_dotProduct ..).trans (hg x y)⟩
end YM.Push.Loops
