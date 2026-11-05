import YM.RG08.Line.Walk

/-!
# Price stubs through prepack; shifts on true origin
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows
open scoped Matrix BigOperators Topology Classical
variable {c f : Side} (P : Patch)(K:KernelChoices)(G:Gauge)

lemma differ : Fund (α:=Co P.L (TypeFace 1)) (β:=Co P.L (TypeFace 0)) fun n=>
    let S:=habitat P K n; repackM (splitCo S.ratio _) (splitCo S.ratio _) (Exterior.d 0 (n*P.L)) := by
  let t (i:Co P.L (TypeFace 1)) := (lift i.1 + step (axisEquiv.symm i.2):Cover)
  let q (i:Co P.L (TypeFace 1)) : Cover := lift i.1
  let V (x:Cover) : Cover × Co P.L (TypeFace 0):= (rent P.L x,wrap P.L x,vac)
  refine readsPrice (fun i=>[( (V (t i)).1, (V (t i)).2,1),((V (q i)).1,(V (q i)).2,-1)]) _ fun n v i=>?_
  rcases i with ⟨x,a,b⟩
  obtain ⟨z,H⟩:= axisEquiv.surjective b; subst b
  let S:=habitat P K n
  change (repackM _ _ _ *ᵥ _) _=_
  erw [repack_test,unpack_street S]; dsimp only
  rw [show axisEquiv z= _ from coord_map z,d_sites]
  dsimp [stint,V,t,q]
  have ht : axisEquiv.symm (coord z)=z := axisEquiv.symm_apply_apply z
  rw [ht]
  have hh : (wrap (n*P.L)) (lift a)+(habitat P K n).ratio.embed x+step z=(wrap (n*P.L)) (lift a+step z)+(habitat P K n).ratio.embed x := by rw [map_add,wrap_step]; abel
  rw [hh]; erw [pack_street,pack_street]; simp [sub_eq_add_neg]

-- lift repacked fund through color. need hasSum product cast and repack binds equality extra alpha reorder.
private def pigment {α β : Type}(R : Pert.Bulk.Kernel α β): Pert.Bulk.Kernel (α × G.ColorIndex) (β×G.ColorIndex) := fun x y=> if x.2.2=y.2.2 then R (x.1,x.2.1) (y.1,y.2.1) else 0

lemma dyed {α β:Type} {A:∀ n:Side,Matrix (Co n α) (Co n β) ℝ}(h:Fund A) : Fund (α:=α×G.ColorIndex) (β:=β×G.ColorIndex) fun n=>Matrix.of fun i j=> if i.2.2=j.2.2 then A n (i.1,i.2.1) (j.1,j.2.1) else 0:= by
  intro σ hs
  obtain ⟨p,R,hr⟩:=h σ hs
  refine ⟨p,pigment G R, ⟨hr.pos,fun x y i=>?_, fun x j=>?_,fun j x=>?_⟩,fun n x y=>?_⟩
  · unfold pigment; dsimp [RG08.Packets.pass]; split
    · exact hr.city (x.1,x.2.1) (y.1,y.2.1) i
    rfl
  · unfold pigment
    dsimp only
    by_cases he:x.2.2=j.2
    · simp_rw [if_pos he]; exact hr.row (x.1,x.2.1) _
    simp [he,Pert.Bulk.bill]
  · unfold pigment; dsimp only
    by_cases he:j.2=x.2.2
    · simp_rw [if_pos he]; exact hr.col _ (x.1,x.2.1)
    simp [he,Pert.Bulk.bill]
  rw [Pert.Bulk.display,Matrix.of_apply]; unfold pigment; dsimp only
  by_cases he:x.2.2=y.2.2
  · simp only [if_pos he]; exact hr.seen n (x.1,x.2.1) (y.1,y.2.1)
  simp [he]

-- Repack already used: colored index convention on coarse/fine. Need transposition (Co P.L Loc) ≃ CoL r × color
private def thread {L:Side}{i:ℕ}: Co L (Loc G i)≃ Co L (TypeFace i)×G.ColorIndex:= (Equiv.prodAssoc _ _ _).symm
lemma fund_along {α β γ δ:Type} {A:∀ n:Side,Matrix (Co n α) (Co n β) ℝ} (h:Fund A)(e:γ≃α)(v:δ≃β) :
    Fund (α:=γ) (β:=δ) (fun n=> (A n).submatrix (Prod.map id e) (Prod.map id v)):= by
  intro σ hs
  obtain ⟨p,R,hr⟩:=h σ hs
  let Y : Pert.Bulk.Kernel γ δ:= fun i j=>R (i.1,e i.2) (j.1,v j.2)
  exact ⟨p,Y,⟨hr.pos,fun x y z=> hr.city (x.1,e x.2) (y.1,v y.2) z,fun x i=>hr.row (x.1,e x.2) (v i), fun i x=>hr.col (e i) (x.1,v x.2)⟩,fun n x y=>hr.seen n (x.1,e x.2) (y.1,v y.2)⟩

-- color through `split` on fine/resolution. Arbitrary layout e.g. coarse uses L=1? distinguish Co L and no split coarse by generic maps carrying site and type; prove standalone.
lemma split_tone {α:Type} (S:StepData c f) (v:Site f×α) : splitCo S.ratio α v = (S.ratio.parent v.1,S.ratio.residue v.1,v.2):=split_co ..

lemma un_tone {α:Type} (S:StepData c f) (v:Site c × Co S.patch.L α) : (splitCo S.ratio α).symm v=(S.ratio.assemble (v.1,v.2.1),v.2.2) := by
  refine (splitCo S.ratio α).injective ?_
  erw [Equiv.apply_symm_apply]
  -- defeq P.L

lemma fundFF {i j:ℕ} {M : ∀ n : Side, Matrix (Body i (n*P.L)) (Body j (n*P.L)) ℝ}
    (h:Fund (α:=Co P.L (TypeFace i)) (β:=Co P.L (TypeFace j)) fun n=> repackM (splitCo (habitat P K n).ratio _) (splitCo (habitat P K n).ratio _) (M n)): Fund (α:=Co P.L (Loc G i)) (β:=Co P.L (Loc G j)) fun n=> let S:=habitat P K n; repackM (unitSplit G S i) (unitSplit G S j) (patron G (M n)) := by
  convert fund_along (dyed G h) (thread G (i:=i) (L:=P.L)) (thread G (i:=j) (L:=P.L)) using 1
  funext n; ext x y
  let S:=habitat P K n
  unfold repackM; dsimp only [Matrix.submatrix_apply,unitSplit, Prod.map,id_eq,Matrix.of_apply, thread]
  exact patron_cell G (M n) (S.ratio.assemble (x.1,x.2.1),x.2.2.1) (S.ratio.assemble (y.1,y.2.1),y.2.2.1) x.2.2.2 y.2.2.2
lemma fundFC {i j:ℕ} {M : ∀ n : Side, Matrix (Body i (n*P.L)) (Body j n) ℝ}
    (h:Fund (α:=Co P.L (TypeFace i)) (β:=TypeFace j) fun n=> repackM (splitCo (habitat P K n).ratio _) (Equiv.refl _) (M n)): Fund (α:=Co P.L (Loc G i)) (β:= Loc G j) fun n=> let S:=habitat P K n; repackM (unitSplit G S i) (Equiv.refl _) (patron G (M n)) := by
  convert fund_along (dyed G h) (thread G (i:=i) (L:=P.L)) (Equiv.refl _) using 1
  funext n; ext x y
  let S:=habitat P K n
  unfold repackM; dsimp only [Matrix.submatrix_apply,unitSplit, Prod.map,id_eq,Matrix.of_apply, thread,Equiv.refl_symm, Equiv.refl_apply]
  exact patron_cell G (M n) (S.ratio.assemble (x.1,x.2.1),x.2.2.1) (y.1,y.2.1) x.2.2.2 y.2.2
lemma fundCF {i j:ℕ} {M : ∀ n : Side, Matrix (Body j n) (Body i (n*P.L)) ℝ}
    (h:Fund (α:=TypeFace j) (β:=Co P.L (TypeFace i)) fun n=> repackM (Equiv.refl _) (splitCo (habitat P K n).ratio _) (M n)): Fund (α:= Loc G j) (β:=Co P.L (Loc G i)) fun n=> let S:=habitat P K n; repackM (Equiv.refl _) (unitSplit G S i) (patron G (M n)) := by
  convert fund_along (dyed G h) (Equiv.refl _) (thread G (i:=i) (L:=P.L)) using 1
  funext n; ext x y
  let S:=habitat P K n
  unfold repackM; dsimp only [Matrix.submatrix_apply,unitSplit, Prod.map,id_eq, Matrix.of_apply, thread, Equiv.refl_symm, Equiv.refl_apply]
  exact patron_cell G (M n) (x.1,x.2.1) (S.ratio.assemble (y.1,y.2.1),y.2.2.1) x.2.2 y.2.2.2
end YM.RG08.Line
