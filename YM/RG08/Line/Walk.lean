import YM.RG08.Line.Pattern

/-!
# Hiking/pricing links in centered cell presentations
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows
open scoped Matrix BigOperators Topology Classical
variable {c f:Side} {α : Type} {L : Side}
variable (P : Patch)(K:KernelChoices)

abbrev habitat (c:Side): StepData c (c*P.L):= ⟨P,K,rfl⟩

private lemma assembling (g: Ratio c f)(x:Cover)(a:Site c): wrap f x+g.embed a=g.assemble (a+wrap c (rent g.count x), wrap g.count x):= by
  conv_lhs => lhs; rw [rent_balance g.count x,map_add]
  rw [Ratio.assemble]
  rw [show g.embed (a+wrap c (rent g.count x))=g.embed a+g.embed (wrap c (rent g.count x)) from g.root.map_add .., Ratio.embed_wrap]
  abel

lemma pack_street (S : StepData c f) (x:Cover) (a:Site c) (w:α): splitCo S.ratio α (wrap f x + S.ratio.embed a,w) = (a+wrap c (rent S.patch.L x),wrap S.patch.L x,w) := by
  rw [assembling, split_co]
  simp only [Ratio.assemble_parent,Ratio.assemble_res]; rfl

-- get name split_co
lemma unpack_street (S : StepData c f) (x:Site c) (v:Co S.patch.L α) :
    (splitCo S.ratio α).symm (x,v) = (wrap f (lift v.1)+S.ratio.embed x,v.2) := (splitCo S.ratio α).injective (by rw [pack_street,rent_lift]; simp; rfl)

/-- The scalar entries of a path at a true cover displacement w.r.t. a coarse cell origin. -/
private def along (L:Side)(x:Cover): Walk→ List (Cover × Co L (TypeFace 1) × ℝ)
  | []=>[]
  | i::v=> let a:= (i.used x).1; (rent L a,(wrap L a,coord i.dir),if i.neg then (-1:ℝ) else 1) :: along L (x+i.vec) v

private theorem path_read {n:Side}(v:Walk)(S:StepData n f)(x:Cover)(a:Site n)(T:Corn (Co n (Co S.patch.L (TypeFace 1)))) :
    integralLink (wrap f x+S.ratio.embed a) v (T ∘ (splitCo S.ratio (TypeFace 1))) = ((along S.patch.L x v).map (fun r=> r.2.2 * T (a+wrap n r.1,r.2.1))).sum := by
  induction v generalizing x with
  | nil => rfl
  | cons i l ih =>
    change (if i.neg then -T _ else T _) + integralLink _ l _ = _
    rw [show (wrap f x+S.ratio.embed a + (i.vec:Site f))=(wrap f (x+(i.vec:Cover))+S.ratio.embed a) by rw [map_add,wrap_vec]; abel, ih]
    rw [along,List.map_cons,List.sum_cons]; congr 1
    cases i with
    | mk u b =>
      cases b <;> dsimp only [Step.used] <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul, neg_one_mul] -- used x negative, pack
      · exact congr_arg T (pack_street S x a _)
      · refine congr_arg Neg.neg (congr_arg T ?_)
        rw [show wrap f x+S.ratio.embed a-step u=wrap f (x-step u)+S.ratio.embed a by rw [map_sub,wrap_step]; abel, pack_street]

-- Scalar repacks on each r-form
lemma hikers : Fund (α:=Co P.L (TypeFace 0)) (β:=Co P.L (TypeFace 1)) fun n=>
    let S:= habitat P K n; repackM (splitCo S.ratio (TypeFace 0)) (splitCo S.ratio (TypeFace 1)) (hikeMap S (green S)) := by
  refine readsPrice (fun i=>along P.L (lift i.1) (walkTree (lift i.1))) _ fun n v x=>?_
  let T:=habitat P K n
  change (repackM _ _ _ *ᵥ v) x=stint _ _ v x
  rcases x with ⟨x,y,b⟩
  rw [repack_test, hike_at]; erw [unpack_street T]; dsimp only
  rw [repeat_tree]
  have he:T.ratio.residue (wrap _ (lift y)+T.ratio.embed x)=y:= by rw [assembling,T.ratio.assemble_res]; exact wrap_lift _ --]
  rw [he]
  exact path_read (walkTree _) T (lift y) x v

lemma pads : Fund (α:=Co P.L (TypeFace 0)) (β:=TypeFace 0) fun n=>
    let S:= habitat P K n; repackM (splitCo S.ratio (TypeFace 0)) (Equiv.refl _) (padMap S) := by
  refine onePrice (fun _=>vac) (fun _=>0) _ (fun _=>1) fun n v x=> ?_
  let S:=habitat P K n
  rcases x with ⟨x,y⟩
  change (repackM _ _ _ *ᵥ v) _=_
  rw [repack_test,pad_at]; erw [unpack_street S]; dsimp; rw [assembling,S.ratio.assemble_parent]; erw [rent_lift]; simp

-- fixRoot = linear combos integralLink paths rooted at actual patch.atPoint
lemma hike_face 
    (x : Cover)(w:Walk) :
    let A (n:Side): Matrix (Body 0 n) (Body 1 (n*P.L)) ℝ:= LinearMap.toMatrix' (LinearMap.pi (fun i:Body 0 n=> integralLink (wrap _ x+(habitat P K n).ratio.embed i.1) w))
    Fund (α:=TypeFace 0) (β:= Co P.L (TypeFace 1)) (fun n=> repackM (Equiv.refl _) (splitCo (habitat P K n).ratio _) (A n)):= by
  intro A
  refine readsPrice (fun _=>along P.L x w) _ fun n v i=> ?_
  erw [repack_test]
  unfold A; rw [LinearMap.toMatrix'_mulVec]; apply path_read w (habitat P K n) x i.1 v
end YM.RG08.Line
