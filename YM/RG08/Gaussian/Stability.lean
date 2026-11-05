import YM.RG08.Gaussian.Mean

/-!
# Variation of the tree covariance and mean

The whole history variation is priced from the ordinary potential Hessian.
Neither mean stability nor inverse stability assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Precision Exterior Bloch Matrix Laurent
open Next.Free Work.F08 Tree Stationary FreeResolvent
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f : Side}

lemma tensor_less {i j : ℕ} (G : Gauge) (A B : Matrix (Body i f) (Body j c) ℝ) :
    tensor G (A-B)=tensor G A-tensor G B := by
  ext i j; unfold tensor; by_cases h : i.2.2=j.2.2 <;> simp [h]

lemma tree_cross (S : StepData c f) (T : Forest S.ratio) (A B : FreeResolvent.FaceRow)
    (hA : (treeMatrix G S T A).PosDef) (hB : (treeMatrix G S T B).PosDef) :
    FreeResolvent.covariance G S T A-FreeResolvent.covariance G S T B =
      FreeResolvent.covariance G S T A *
        tensor G (K (B.acts f)-K (A.acts f)) *
          FreeResolvent.covariance G S T B := by
  let I := sprig S T G; let L := treeMatrix G S T A; let R := treeMatrix G S T B
  let M := tensor G (K (B.acts f)-K (A.acts f))
  have hl : L⁻¹ * L=1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hA.isUnit)
  have hr : R*R⁻¹=1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hp : Iᵀ*M*I=R-L := by
    have he : M= fullMatrix G S B - fullMatrix G S A := by
      unfold fullMatrix baseMatrix M
      rw [← tensor_less,add_sub_add_right_eq_sub]
    rw [he,Matrix.mul_sub,Matrix.sub_mul]; exact congr_arg₂ (·-·) (insertion.compress ..) (insertion.compress ..)
  unfold FreeResolvent.covariance treeInverse resolve reduce
  simp only [zero_smul,add_zero]
  change I*L⁻¹*Iᵀ-I*R⁻¹*Iᵀ=I*L⁻¹*Iᵀ*M*(I*R⁻¹*Iᵀ)
  symm
  calc
    _ = I*L⁻¹*(Iᵀ*M*I)*R⁻¹*Iᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hp, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc (I*L⁻¹),
        hr, Matrix.mul_assoc I L⁻¹ L,hl, Matrix.mul_one,Matrix.mul_one]

section
variable {P : Patch} {k : KernelChoices} (X : Repeated P.L) {u v : Train P.J}
variable (ha : P.Branches k G) {τ σ C Q V : ℝ}

include ha

/-- Resolution uses coefficient powers in fine steps, true `η` pre-block
budget can pass longer chains (σ is an input width, must meet the tuition). -/
lemma covariance_moves (hp : (conditionalCov G X k u).strip τ Q)
    (hp' : (conditionalCov G X k v).strip τ V)
    (hh : (minusRows (hessian (pink k.penalty v)) (hessian (pink k.penalty u))).strip σ C)
    (hw : 0<τ) (ht : τ ≤ P.L.val*σ) :
    let m := (Fintype.card (Co P.L (Loc G 1)):ℝ)
    (minusRows (conditionalCov G X k u) (conditionalCov G X k v)).strip τ
      (m*(m*(Q*(Real.exp (4*τ)*C))*V)) := by
  intro m
  let A := pink k.penalty u; let B := pink k.penalty v
  let L := conditionalCov G X k u; let R := conditionalCov G X k v
  let E := minusRows (hessian B) (hessian A)
  let U := nativeRow P.L (colored G E)
  have hC : U.strip τ (Real.exp (4*τ)*C) := native_price (colored_price G hh) hw.le ht
  have he := strip_compose hw.le (strip_compose hw.le hp hC) hp'
  let D := composeRows (composeRows L U) R
  suffices hx : minusRows L R=D by change Row.strip (minusRows L R) _ _; rw [hx]; exact he
  apply bank_injective (Row.rights _ _ (strip_minus hp hp') hw.le) (Row.rights _ _ he hw.le)
  intro c
  let f := c*P.L; let S:= linked P k c f rfl; let T:= X.forest S.ratio; let p:=unitSplit G S 1
  have hX : L.acts c=_ := (conditional_truth G X k u ha).2 c f rfl
  have hY : R.acts c=_ := (conditional_truth G X k v ha).2 c f rfl
  change (minusRows (conditionalCov G X k u) (conditionalCov G X k v)).acts c = Row.acts D c
  rw [acts_minus hw.le hp hp']
  change L.acts c-R.acts c= _
  have hD : D.acts c=L.acts c * U.acts c * R.acts c := by
    unfold D; rw [acts_compose hw.le (strip_compose hw.le (show L.strip τ Q from hp) hC) hp',
        acts_compose hw.le (show L.strip τ Q from hp) hC]
  rw [hD,hX,hY]
  let M := tensor G (K (B.acts f)-K (A.acts f))
  have hr (w : Train P.J) : Whole (pink k.penalty w) := (heart_saves _ k.penalty_pos P.order_cut (id : Train P.J → _)).1.whole w
  have hA : Whole A := hr _; have hB : Whole B := hr _
  have ht' : U.acts c=repackM p p M :=
    (native_acts S.ratio (colored_whole G ((hessian_whole hB).minus (hessian_whole hA)))).trans (by
        unfold M p
        rw [colored_acts, (hessian_whole hB).less (hessian_whole hA), hessian_acts hB,hessian_acts hA])
  have hO := tree_cross S T A B (forest_precision G k u c f rfl ha T) (forest_precision G k v c f rfl ha T)
  rw [ht']
  change repackM p p (FreeResolvent.covariance G S T A-FreeResolvent.covariance G S T B) =
    repackM p p (FreeResolvent.covariance G S T A) * repackM p p M * repackM p p (FreeResolvent.covariance G S T B)
  rw [hO, repack_multiply _ p, repack_multiply _ p]

omit ha

lemma coarseMean_movement (he : (minusRows (conditionalCov G X k u) (conditionalCov G X k v)).strip τ C)
    (ht : (probeRow G P k).strip τ Q) (hw : 0<τ) :
    (minusRows (coarseMean G X k u) (coarseMean G X k v)).strip τ
      (‖k.penalty‖*(Fintype.card (Co P.L (Loc G 1))*(C*Q))) := by
  unfold coarseMean
  let A := conditionalCov G X k u; let B := conditionalCov G X k v
  let T := transRows (probeRow G P k); let M (w : Row (Co P.L (Loc G 1)) (Co P.L (Loc G 1))) := scaleRows k.penalty (composeRows w T)
  have hi : (M (minusRows A B)).strip _ _ := strip_scale (strip_compose hw.le he (strip_trans ht)) k.penalty
  have ht' : Whole T := ⟨_,_,hw,strip_trans ht⟩
  have hr (v:Train P.J) : Whole (conditionalCov G X k v) := by
    by_cases ha : P.Branches k G
    · exact (conditional_truth G X k v ha).1
    rw [conditionalCov,dif_neg ha]; refine ⟨1,0,one_pos,?_⟩; intro x y; simp [Width,SumBudget]
  have ha : Whole A := hr u; have hb : Whole B := hr v
  change Row.strip (minusRows (M A) (M B)) _ _
  suffices H : minusRows (M A) (M B)=M (minusRows A B) from H.symm ▸ hi
  refine bank_injective ((((ha.prod ht').weight _).minus ((hb.prod ht').weight _)).safe) (Whole.safe ⟨_,_,hw,hi⟩) (fun c => ?_)
  unfold M
  rw [((ha.prod ht').weight _).less ((hb.prod ht').weight _),acts_scale,acts_scale,acts_scale,
      ha.acts ht',hb.acts ht',(ha.minus hb).acts ht',ha.less hb,Matrix.sub_mul,smul_sub]
end
end YM.RG08
