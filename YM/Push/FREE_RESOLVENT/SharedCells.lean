import YM.Push.FREE_RESOLVENT.PatchComparison

/-!
# Producing comparable patches

Irregular tree axes may vary from block to block. Form matched patch required
for arithmetic comparison if for each block in the lifted working box, a
bond is on the tree iff its counterpart is (no choices at faraway roots
needed). This is only an intrinsic comparison WHEN the coefficient indices
are aligned; not an assumption that independently chosen trees have that
property. Also construct repeated-tag forests which realize the alignment at
arbitrary radii and (large enough) periods.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Matrix RG Precision Bloch Laurent Exterior Tree Bid
open scoped BigOperators
namespace Lifted
variable {G : Gauge} {n L c f c' f' : Side} {P : Patch} {K : KernelChoices}
variable {h : f.val = c.val*P.L.val} {h' : f'.val = c'.val*P.L.val}



lemma assemble_test (S : StepData c f) (T : Forest S.ratio) (y : Site c) (p : Site S.patch.L) (i : PAC G 1) :
    ((y,p,i) ∈ Set.range (grid S T)) ↔
      (S.ratio.assemble (y,p),axisEquiv.symm i.1) ∉ T.trunks := by
  constructor
  · rintro ⟨a,ha⟩; rw [grid,split_co] at ha
    have hy : S.ratio.parent a.1.val.1=y := congr_arg Prod.fst ha
    have hp : S.ratio.residue a.1.val.1=p := congr_arg (fun x : Co c _ => x.2.1) ha
    have hi : coord a.1.val.2=i.1 := congr_arg (fun x : Co c _ => x.2.2.1) ha
    rw [← hy, ← hp, Ratio.assemble,S.ratio.unpack_at, ← hi, ← coord_map,axisEquiv.symm_apply_apply]
    exact a.1.property
  intro ha
  refine ⟨(⟨_, ha⟩, i.2),?_⟩
  rw [grid,split_co]
  change (S.ratio.parent _, S.ratio.residue _,coord _, _)=_
  simp only [plant,ix]
  erw [Ratio.assemble_parent,Ratio.assemble_res, ← coord_map, axisEquiv.apply_symm_apply]; rfl

lemma fit_box (z : Cover) (d : ℕ) (hz : z ∈ box d) : size z ≤ 4*d := by
  have he (i) : (z i).natAbs ≤ d := by
    have h := (box_test.mp hz).1 i
    have h' := (box_test.mp hz).2 i
    omega
  calc
    _ ≤ ∑ _ : Axis, d := Finset.sum_le_sum fun i _ => he i
    _ = _ := by simp [Axis]

lemma lift_box (x : Site n) (d : ℕ) (h : pdist x ≤ d) : lift x ∈ box d := by
  rw [box_test]; constructor <;> intro i <;> have hi := component_le x i <;> omega

-- Number ALL comparable slots over a first-period root's patch
abbrev offsets (L : Side) (G : Gauge) (d : ℕ) := ↥(box d) × Co L (PAC G 1)

def retain (S : StepData c f) (T : Forest S.ratio) (G : Gauge) (y : Site c) (d : ℕ) : Finset (offsets S.patch.L G d) := by
  classical
  exact Finset.univ.filter fun i => (y+wrap c i.1.val,i.2) ∈ Set.range (grid S T)

def identifiers {S : StepData c f} {T : Forest S.ratio} {y : Site c} {d : ℕ} (i : retain S T G y d) :=
  ((i.val.1.val : Cover), i.val.2)

lemma retained_iff (S : StepData c f) (T : Forest S.ratio) (y : Site c) (d : ℕ) (i : offsets S.patch.L G d) :
    i ∈ retain S T G y d ↔ (y+wrap c i.1.val,i.2) ∈ Set.range (grid S T) := by classical simp only [retain,
      Finset.mem_filter,Finset.mem_univ,true_and]

lemma fits {S : StepData c f} {T : Forest S.ratio} {y : Site c} (d : ℕ) :
    Small (G:=G) (identifiers (T:=T) (y:=y) (d:=d) (G:=G)) (8*d) := by
  intro i j
  change size (i.val.1.val-j.val.1.val) ≤ _
  rw [sub_eq_add_neg]
  have hz := fit_box i.val.1.val d i.val.1.property
  have hw := fit_box j.val.1.val d j.val.1.property
  have hh := size_add i.val.1.val (-j.val.1.val); rw [size_neg] at hh
  omega



lemma named {S : StepData c f} {T : Forest S.ratio} {y : Site c} {d : ℕ}
    (e : ↥(retain S T G y d) ↪ Active G T) (hc : Copies S T e y identifiers) (a : Active G T)
    (ha : separation (theta S.ratio T a) y ≤ d) : a ∈ Set.range e := by
  let z := lift ((grid S T a).1-y)
  have hz : z ∈ box d := lift_box _ d (by rw [grid_site]; exact ha)
  let j : offsets _ _ d := (⟨z,hz⟩,(grid S T a).2)
  have he : grid S T a = (y+wrap c z,j.2) := Prod.ext (by unfold z; rw [wrap_lift]; simp) rfl
  let i : ↥(retain S T G y d) := ⟨j,(retained_iff ..).mpr ⟨a,he⟩⟩
  exact ⟨i, (grid_inj S T) ((hc i).trans he.symm)⟩



-- Convenience application (anchor-root k exists iff slot supplied).


section construction
variable (X : Forest (data h K).ratio) (t : Site c' → Site c)

-- a block move, on an internal tree step; it has *zero* macro carry
lemma tiny (S : StepData c f) (y : Site f) (w : Step) (hp : 3 ≤ c.val)
    (hw : S.ratio.parent (y+w.vec) = S.ratio.parent y) :
    Work.F08.carry (S.ratio.residue y) w.vec = 0 := by
  let k : Cover := Work.F08.carry (S.ratio.residue y) w.vec
  rw [← wrap_vec f, Work.F08.moves_parent] at hw
  have he : wrap c k=0 := add_left_cancel (hw.trans (add_zero _).symm)
  have hh : size k ≤ 1 := by
    refine (Work.F08.carry_size ..).trans ?_
    have hj (i : Axis) : size (step i:Cover) = 1 := by simp [size, apply_ite Int.natAbs]
    rcases w with ⟨i,b|b⟩
    · exact (hj i).le
    change size (-(step i:Cover)) ≤ 1; rw [size_neg,hj]
  change k = 0; rw [← size_centers _ _ hh (by omega : 2 * 1 < c.val), he]; ext; simp [lift]

/-- Pull one prescribed block choice from source for each target block. -/
def rebuild (hh : 3 ≤ c.val) : Forest (data h' K).ratio := by
  let L := (data h K).ratio
  let L' := (data h' K).ratio
  let y (x : Site f') := L.assemble (t (L'.parent x), L'.residue x)
  let W (x : Site f') := X.up (y x)
  have he (x : Site f') (hx : leaf L' x) : leaf L (y x) := by
    rw [Tree.leaf, ne_eq, L'.root_id] at hx
    change ¬ y x = _; rw [L.root_id]; unfold y; erw [L.assemble_res]; exact hx
  have hi (x : Site f') (hx : leaf L' x) : Work.F08.carry (L'.residue x) (W x).vec = 0 := by
    have hb := tiny (data h K) (y x) (W x) hh (X.stays _ (he x hx))
    erw [show (data h K).ratio.residue (y x)=L'.residue x from L.assemble_res _] at hb
    exact hb
  have ht (x : Site f') (hx : leaf L' x) : L'.parent (x+(W x).vec)=L'.parent x := by
    rw [← wrap_vec f',Work.F08.moves_parent,hi x hx,map_zero,add_zero]
  refine { up := W, height := fun x => X.height (y x), bound := fun x => X.bound _,
           rise := ?_, stays := ht }
  intro x hx
  have hx' : y (x+(W x).vec)=y x+(W x).vec := by
    let z := (W x).vec (R:=ℤ)
    have hw := tiny (data h K) (y x) (W x) hh (X.stays _ (he x hx))
    change Work.F08.carry (L.residue (y x)) z = 0 at hw
    rw [← wrap_vec f, Work.F08.moves_site L (y x)]
    change _ = L.assemble (L.parent _ + wrap c _, Work.F08.arrives (L.residue _) z)
    rw [hw,map_zero,add_zero]
    unfold y
    erw [ht x hx, Ratio.assemble_res, Ratio.assemble_parent]
    rw [← wrap_vec f', Work.F08.moves_residue]; rfl
  change X.height (y (x+(W x).vec)) < X.height (y x)
  rw [hx']; exact X.rise _ (he x hx)

-- trunk membership at a block is determined by its local steps only
lemma sorted (S : StepData c f) (T : Forest S.ratio) (hh : 3 ≤ c.val)
    (y : Site c) (p : Site S.ratio.count) (i : Axis) :
    (S.ratio.assemble (y,p),i) ∈ T.trunks ↔ ∃ v : Site S.ratio.count, v ≠ 0 ∧
      let w := T.up (S.ratio.assemble (y,v))
      w.dir = i ∧ p = if w.neg then Work.F08.arrives v w.vec else v := by
  let L := S.ratio
  have hz (x) : leaf L x ↔ L.residue x ≠ 0 := not_congr (L.root_id x)
  have he (x) (hx : leaf S.ratio x) : (T.up x).used x =
      let w := T.up x
      (L.assemble (L.parent x, if w.neg then Work.F08.arrives (L.residue x) w.vec else L.residue x),w.dir) := by
    dsimp only; let w := T.up x
    have hk : Work.F08.carry (L.residue x) w.vec=0 := tiny _ _ _ hh (T.stays x hx)
    change w.used x = (L.assemble (L.parent x, if w.neg then Work.F08.arrives (L.residue x) w.vec else L.residue x), w.dir)
    unfold Step.used; split <;> rename_i hw
    · rw [← add_zero (L.parent x),← map_zero (wrap c),← hk,
        ← Work.F08.moves_site, wrap_vec,Step.vec,if_pos hw,sub_eq_add_neg]
    rw [show  L.assemble (L.parent x,L.residue x)=x from L.unpack_at x]
  constructor
  · intro hp; obtain ⟨x,hx,ha⟩ := (T.trunk_mem_iff _).mp hp
    refine ⟨L.residue x,(hz x).mp hx,?_⟩
    -- compare canonical decompositions
    rw [he x hx] at ha; dsimp only at ha
    have hP := L.assemble_bijective.1 (congr_arg (fun p : Edge (Site f) => p.1) ha)
    have hy : L.parent x = y := congr_arg Prod.fst hP
    rw [← hy]; erw [show L.assemble (L.parent x,L.residue x)=x from L.unpack_at x]
    exact ⟨congr_arg Prod.snd ha,(congr_arg Prod.snd hP).symm⟩
  rintro ⟨v,hv,H⟩
  let x := L.assemble (y,v)
  have hx : leaf L x := (hz _).mpr (by rw [show L.residue x=v from L.assemble_res _]; exact hv)
  apply (T.trunk_mem_iff _).mpr
  refine ⟨x,hx,?_⟩
  rw [he x hx]; dsimp only
  rw [show L.parent x = y from L.assemble_parent _,show L.residue x=v from L.assemble_res _]
  exact Prod.ext (congr_arg (fun a => L.assemble (y,a)) H.2.symm) H.1

lemma rebuild_at (y : Site c') (hh : 3 ≤ c.val) (he : 3 ≤ c'.val) (p : Site P.L) (i : Axis) :
    ((data h K).ratio.assemble (t y,p),i) ∈ X.trunks ↔
      ((data h' K).ratio.assemble (y,p),i) ∈ (rebuild X t hh (h':=h')).trunks := by
  erw [sorted _ X hh,sorted _ (rebuild X t hh (h':=h')) he]
  let g := (data h' K).ratio
  have hw (u : Site P.L) : (rebuild X t hh (h':=h')).up (g.assemble (y,u)) = X.up ((data h K).ratio.assemble (t y,u)) := by
    change X.up ((data h K).ratio.assemble (t (g.parent (g.assemble (y,u))), g.residue (g.assemble (y,u)))) = _
    erw [Ratio.assemble_res,Ratio.assemble_parent]
  constructor
  · rintro ⟨v,hv,H⟩
    refine ⟨v,hv,?_⟩; erw [hw]; exact H
  rintro ⟨v,hv,H⟩
  refine ⟨v,hv,?_⟩; erw [hw] at H; exact H

omit t

end construction
end Lifted
end YM.FreeResolvent
