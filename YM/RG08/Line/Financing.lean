import YM.RG08.Line.Stubs

/-!
# Remaining finite stencils of the flat tree projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows
open scoped Matrix BigOperators Topology Classical
variable (P : Patch)(K:KernelChoices)(G:Gauge)

lemma fixPrice : Fund (α:=TypeFace 0) (β:= Co P.L (TypeFace 1)) fun n=>
    repackM (Equiv.refl _) (splitCo (habitat P K n).ratio _) (fixRoot (habitat P K n)) := by
  let M (x y:P.Points)(a:Lattice.Order)(n : Side) : Matrix (Body 0 n) (Body 1 (n*P.L)) ℝ:= LinearMap.toMatrix'
    (LinearMap.pi (fun i:Body 0 n=> integralLink (wrap _ x.val+(habitat P K n).ratio.embed i.1) (route x.val y.val a)))
  let Y (x:P.Points)(n:Side) : Matrix (Body 0 n) (Body 1 (n*P.L)) ℝ:= LinearMap.toMatrix'
    (LinearMap.pi (fun i:Body 0 n=> tau (habitat P K n) i.1 x))
  let B x y a (n:Side):Matrix (Co n (TypeFace 0)) (Co n (Co P.L (TypeFace 1))) ℝ := repackM (Equiv.refl _) (splitCo (habitat P K n).ratio _) (M x y a n)
  let Z x (n:Side):Matrix (Co n (TypeFace 0)) (Co n (Co P.L (TypeFace 1))) ℝ := repackM (Equiv.refl _) (splitCo (habitat P K n).ratio _) (Y x n)
  have hA (x y:P.Points)(a : Lattice.Order): Fund (B x y a):= hike_face P K x.val _
  let s:ℝ:=(Fintype.card P.Points:ℝ)⁻¹
  let t:ℝ:=(Fintype.card Lattice.Order:ℝ)⁻¹
  have ht x n : Y x n= -(s • ∑ y:P.Points, (t • ∑ a:Lattice.Order,M x y a n)):=by
    apply perVec; intro v; funext i
    unfold Y; rw [LinearMap.toMatrix'_mulVec, LinearMap.pi_apply,Matrix.neg_mulVec,Matrix.smul_mulVec]; dsimp only [tau,LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sum_apply]; unfold s t
    simp only [Matrix.sum_mulVec,Matrix.smul_mulVec,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,M,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply]
    change -((s:ℝ) • ((∑ y:P.Points,t • ∑ a:Lattice.Order, integralLink (wrap (n*P.L) x.val+(habitat P K n).ratio.embed i.1) (route x.val y.val a)) v)) = _
    rw [LinearMap.sum_apply]; simp_rw [LinearMap.smul_apply, LinearMap.sum_apply]; rfl
  have hx n : fixRoot (habitat P K n)=Y P.center n -∑ a:P.Points,P.weight a • Y a n:=by
    apply perVec; intro v; funext i
    unfold fixRoot; rw [LinearMap.toMatrix'_mulVec,LinearMap.pi_apply, adjusted]
    simp only [Matrix.sub_mulVec,Matrix.sum_mulVec,Matrix.smul_mulVec,Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Y,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply]
  have he x: Fund (Z x) := by
    have hY (y:P.Points): Fund fun n=>t • ∑ a:Lattice.Order,B x y a n := (Fund.sum univ _ fun a _=>hA x y a).scaled t
    convert (Fund.sum univ (fun (y:P.Points) n=>t • ∑ a:Lattice.Order,B x y a n) fun y _=>hY y).scaled (-s) using 1
    funext n
    unfold Z B; rw [ht,← neg_smul]
    dsimp only [StepData.ratio] -- help?
    ext i j; simp only [repackM,Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply]
  convert (he P.center).minus (Fund.sum univ (fun x n=>P.weight x • Z x n) fun x _=> (he x).scaled _) using 1
  funext n
  change repackM _ _ _= Z _ _ - ∑ x:P.Points,P.weight x • Z x n
  unfold Z; rw [hx]
  ext i j; simp only [repackM,StepData.ratio,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply]; rfl

-- block-component projections, onsite diagonal matrices
lemma back_fund : Fund (α:= Co P.L (Loc G 1)) (β:=ParcelG G P.L) fun n=> let S:=habitat P K n; repackM (unitSplit G S 1) (clothe G S) (butt G n (n*P.L)):= by
  refine onePrice Sum.inl (fun _=>0) _ (fun _=>1) fun n v x=>?_
  let S:=habitat P K n
  erw [repack_test]
  rw [helmet_butt,Stationary.sliceX]; unfold Function.comp
  erw [inflowL S,Equiv.apply_symm_apply,map_zero]; simp; rfl
lemma cap_fund : Fund (α:= Loc G 0) (β:=ParcelG G P.L) fun n=> let S:=habitat P K n; repackM (Equiv.refl _) (clothe G S) (brim G n (n*P.L)):= by
  refine onePrice Sum.inr (fun _=>0) _ (fun _=>1) fun n v x=>?_
  let S:=habitat P K n
  rw [repack_test,helmet_brim,Stationary.sliceY,map_zero]; dsimp; simp; rfl

lemma stencil_projection : Fund (α:=Co P.L (Loc G 1)) (β:=ParcelG G P.L) fun n=> let S:=habitat P K n; repackM (unitSplit G S 1) (clothe G S) (project G S (green S)):= by
  have hB:=back_fund P K G
  have hC:= cap_fund P K G
  have hR := fundFF P K G (hikers P K)
  have hD := fundFF P K G (differ P K)
  have hS := fundCF P K G (fixPrice P K)
  have hH := fundFC P K G (pads P K)
  let A:= hB.minus (hD.times ((hH.times (hC.plus (hS.times hB))).minus (hR.times hB)))
  convert A using 1
  funext n
  unfold project correct
  simp only [Pi.sub_apply,Pi.add_apply]
  let S:=habitat P K n
  let v:=unitSplit G S 1
  let z:=unitSplit G S 0
  -- repack addition defeq; multiplication via middle
  rw [show ∀ (A B:Matrix (Lines G (n*P.L) 1) (Bodies G n (n*P.L)) ℝ), repackM v (clothe G S) (A-B)=repackM v (clothe G S) A - repackM v (clothe G S) B from fun _ _=>rfl,repack_multiply v z (clothe G S)]
  rw [show ∀ (A B:Matrix (Lines G (n*P.L) 0) (Bodies G n (n*P.L)) ℝ), repackM z (clothe G S) (A-B)=repackM z (clothe G S) A - repackM z (clothe G S) B from fun _ _=>rfl]
  rw [repack_multiply z (Equiv.refl (Lines G n 0)), repack_multiply z v]
  rw [show ∀ (A B:Matrix (Lines G n 0) (Bodies G n (n*P.L)) ℝ), repackM (Equiv.refl _) (clothe G S) (A+B)=repackM (Equiv.refl _) (clothe G S) A + repackM (Equiv.refl _) (clothe G S) B from fun _ _=>rfl,repack_multiply (Equiv.refl _) v]
  rfl

end YM.RG08.Line
