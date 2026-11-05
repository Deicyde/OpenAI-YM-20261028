import YM.Work.H03
/-! Fixed permutation budget. For rotations/conjugation on an ENTIRE family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Work.H03.After
open RG Lattice Wilson Function Ovens Ovens.Pipes
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {P : BudgetPoint} {X : Pipes G n} {d : Tap G n} {s : Signed} {b: Site n}
private lemma lefts_map_sum (p q : Equiv.Perm ℕ) (A : Finset Ovens.Label) :
    lefts (A.map (Equiv.sumCongr p q).toEmbedding) = (lefts A).map p.toEmbedding := by
  ext; simp [lefts]

private lemma contains_map (p q : Equiv.Perm ℕ) (e : Equiv.Perm (Site n))
    (hp : ∀ l, X.patch ((Equiv.sumCongr p q) l) = (X.patch l).image e)
    (A : Finset Ovens.Label) (hA : X.contains A) :
    X.contains ((Equiv.sumCongr p q).finsetCongr A) := by
  let v := Equiv.sumCongr p q
  let A' := A.map v.toEmbedding
  have hl : lefts A' = (lefts A).map p.toEmbedding := lefts_map_sum p q A
  obtain ⟨ha, ⟨hb,hc⟩, hd⟩ := hA
  change (lefts A').Nonempty ∧ Ac.Spark X.patch A' ∧ _
  refine ⟨hl.symm ▸ ha.map, ⟨hb.map,?_⟩, ?_⟩
  · intro i hi j hj
    obtain ⟨i,hiA,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j,hjA,rfl⟩ := Finset.mem_map.mp hj
    -- lift a chain because both memberships and all meetings transport
    refine Relation.ReflTransGen.lift (r := Ac.bonds X.patch A) (p := Ac.bonds X.patch A') v
      ?_ i j (hc i hiA j hjA)
    rintro u w ⟨hu,hw,x,hx1,hx2⟩
    change v u ∈ A' ∧ v w ∈ A' ∧ Ac.meets X.patch (v w) (X.patch (v u))
    refine ⟨Finset.mem_map.mpr ⟨u,hu,rfl⟩, Finset.mem_map.mpr ⟨w,hw,rfl⟩, e x, ?_, ?_⟩
    · exact (hp u).symm ▸ Finset.mem_image_of_mem _ hx1
    · exact (hp w).symm ▸ Finset.mem_image_of_mem _ hx2
  intro i hi j hj hn
  change i ∈ lefts A' at hi
  change j ∈ lefts A' at hj
  rw [hl] at hi hj
  obtain ⟨i,hiA,rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨j,hjA,rfl⟩ := Finset.mem_map.mp hj
  have hk (a : ℕ) : (X.kernel (p a)).support = (X.kernel a).support.image e := hp (.inl a)
  change Disjoint (X.kernel (p i)).support (X.kernel (p j)).support
  rw [hk, hk, Finset.disjoint_image e.injective]
  exact hd hiA hjA (fun h ↦ hn (congrArg p h))

private def pelletEquiv (p q : Equiv.Perm ℕ) (e : Equiv.Perm (Site n))
    (hp : ∀ l, X.patch ((Equiv.sumCongr p q) l) = (X.patch l).image e) : Equiv.Perm X.Pellet :=
  Equiv.subtypeEquiv (Equiv.sumCongr p q).finsetCongr (fun A => by
    let v := Equiv.sumCongr p q
    refine ⟨contains_map p q e hp A, fun h => ?_⟩
    have hi (l) : X.patch ((Equiv.sumCongr p.symm q.symm) l) = (X.patch l).image e.symm := by
      change X.patch (v.symm l) = _
      obtain ⟨l,rfl⟩ := v.surjective l
      rw [Equiv.symm_apply_apply, show X.patch (v l) = _ from hp l, Finset.image_image]
      simp
    have he : X.contains (v.finsetCongr.symm (v.finsetCongr A)) :=
      contains_map p.symm q.symm e.symm hi _ h
    rwa [Equiv.symm_apply_apply] at he)

private lemma biUnion_map_image {ι : Type*} (C : ι → Support n) (A : Finset ι)
    (v : Equiv.Perm ι) (g : Site n → Site n) (h : ∀ l, C (v l) = (C l).image g) :
    (A.map v.toEmbedding).biUnion C = (A.biUnion C).image g := by
  ext x; constructor
  · intro hx
    obtain ⟨l, hl, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨l, hlA, rfl⟩ := Finset.mem_map.mp hl
    change x ∈ C (v l) at hx
    rw [h] at hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem g (Finset.mem_biUnion.mpr ⟨l,hlA,hy⟩)
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l,hl,hy⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨v l,Finset.mem_map.mpr ⟨l,hl,rfl⟩,
      (h l).symm ▸ Finset.mem_image_of_mem g hy⟩

def defines (F : ℕ ≃ X.Pellet) (m:(X.pours d).Moves s b) (q: Equiv.Perm ℕ) (hq:∀ i,X.softer (q i)=(X.softer i).image (affine s b)) (hqval:∀ U i,d.logarithm (q i) U=d.logarithm i (pull s b U)): (fused F P d).Moves s b:=by
  let e : Equiv.Perm (Site n) := s.actEquiv.toEquiv.trans (Equiv.addRight b)
  let v := Equiv.sumCongr m.kp q
  have hp (l) : X.patch (v l) = (X.patch l).image e := by
    cases l with
    | inl i => exact m.forced_support i
    | inr i => exact hq i
  let f := pelletEquiv m.kp q e hp
  let k := (F.trans f).trans F.symm -- transport of the fused K labels
  have hk (i) : (F (k i)).val = (F i).val.map v.toEmbedding := by
    change (F (F.symm (f (F i)))).val = _
    rw [Equiv.apply_symm_apply]; rfl
  have hl (i) : lefts (F (k i)).val = (lefts (F i).val).map m.kp.toEmbedding := by
    rw [hk]; exact lefts_map_sum _ _ _
  -- Compare support, inventory, condition, then the product.
  have hs (i) : (addr F P (k i)).support = (addr F P i).support.image (affine s b) := by
    change X.skin (F (k i)).val = (X.skin (F i).val).image _
    rw [hk]; exact biUnion_map_image X.patch _ v e hp
  have hi (i) : (addr F P (k i)).inventory = (addr F P i).inventory.image (affine s b) := by
    change X.plot (F (k i)).val = (X.plot (F i).val).image _
    unfold plot; rw [hl]
    exact biUnion_map_image (fun j => (X.kernel j).inventory) _ m.kp (affine s b) m.forced_inventory
  have ht (i U) : (addr F P (k i)).extraTest U ↔ (addr F P i).extraTest (pull s b U) := by
    change condition F P (k i) U ↔ condition F P i (pull s b U)
    unfold condition; rw [hl]
    have he (j) : (X.kernel (m.kp j)).eligible P.threshold U ↔
        (X.kernel j).eligible P.threshold (pull s b U) :=
      eligible_send s b _ _ _ _ (m.forced_support j) (m.forced_inventory j) (m.forced_tests j U)
    simp only [Finset.forall_mem_map, Equiv.coe_toEmbedding, he]
  refine ⟨m.ep, k, m.reg_site, m.reg_support, hs, hi, ht, m.valuesE, ?_⟩
  intro i U
  change solid F P d (k i) U = solid F P d i (pull s b U)
  have he : (addr F P (k i)).eligible P.threshold U ↔
      (addr F P i).eligible P.threshold (pull s b U) :=
    eligible_send s b _ _ _ _ (hs i) (hi i) (ht i U)
  by_cases h : (addr F P i).eligible P.threshold (pull s b U)
  · simp only [solid,h,he, ↓reduceIte,hk,Finset.prod_map]
    apply Finset.prod_congr rfl
    rintro (l|l) _
    · exact m.valuesK l U
    change Real.exp (d.logarithm (q l) U)-1 = Real.exp (d.logarithm l (pull s b U))-1
    rw [hqval]
  simp only [solid,h,he, ↓reduceIte]

section
variable (F : ℕ≃ X.Pellet){c d:Tap G n}(m:(X.pours d).Moves s b) (u:(X.pours c).Moves s b)
  (q:Equiv.Perm ℕ)(hq:∀ i,X.softer (q i)=(X.softer i).image (affine s b))(hp:∀ U i,d.logarithm (q i) U=d.logarithm i (pull s b U))(hd:∀ U i,c.logarithm (q i) U=c.logarithm i (pull s b U))
lemma written_eq (h:m.kp=u.kp): (defines F m q hq hp (P:=P)).kp=(defines F u q hq hd (P:=P)).kp:=by
  obtain ⟨_,_,_,_,_,_,_,_,_⟩:=m; obtain ⟨_,_,_,_,_,_,_,_,_⟩:=u
  cases h; rfl
lemma issued_eq : (defines F m q hq hp (P:=P)).ep=m.ep:=rfl
end
end YM.Work.H03.After
