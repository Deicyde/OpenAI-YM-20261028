import YM.Bid.Kitchen

/-!
# H03: the forced-family and Moves receipts for fusion at fixed P

Work on the native torus, including degenerate short periods. The predicates
are pointwise, even for zero payloads. Thus we transport actual faces and their
tested sites (including the base shifts), and we permute *all* addresses. On a
fused support the final flags are still read with the `UsesFinal` convention.
This is the structural assertion, not the gas identity or the price bound.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.H03

open RG Wilson Lattice Ovens Ovens.Pipes
open scoped BigOperators
variable {G : Gauge} {n : Side}

/-! First the torus version of the footprint argument in YM.Branch.Channel
    (there on `Cover`). -/

private lemma visits_site_aff (s : Signed) (t x : Site n) (w : Walk) :
    (visits x w).map (affine s t) = visits (affine s t x) (w.map (·.rotate s)) := by
  induction w generalizing x with
  | nil => simp [visits]
  | cons d w ih =>
    simp only [visits, List.map_cons, ih, Step.vec_rotate]
    rw [show affine s t (x+d.vec) = affine s t x+s.act d.vec by
      rw [affine, affine, Signed.act_add]; abel]

private lemma corner_set (x : Site n) (a b : Step) : (visits x (oriented a b)).toFinset =
    {x, x+a.vec, x+b.vec, x+a.vec+b.vec} := by
  simp only [visits, oriented, Step.vec_rev,
    show x+a.vec+b.vec+-a.vec = x+b.vec by abel, add_neg_cancel_right]
  ext
  simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil]; tauto

private lemma corners_positive (x : Site n) (a b : Step) : (visits x (oriented a b)).toFinset =
    (visits (atFace x a b) (square a.dir b.dir)).toFinset := by
  rw [corner_set]
  change _ = (visits _ (oriented (posDir a.dir) (posDir b.dir))).toFinset
  rw [corner_set]; ext y
  simp only [Finset.mem_insert, Finset.mem_singleton]; unfold atFace
  cases ha : a.neg <;> cases hb : b.neg <;>
    simp only [Step.vec, posDir, ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    abel_nf <;> tauto

lemma touched_send (s : Signed) (b : Site n) (p : Face (Per n)) :
    touched (Face.send s b p) = (touched p).image (affine s b) := by
  let i := p.2.val.1
  let j := p.2.val.2
  let u := (posDir i).rotate s
  let v := (posDir j).rotate s
  have hp := visits_site_aff s b p.1 (oriented (posDir i) (posDir j))
  rw [show (oriented (posDir i) (posDir j)).map (·.rotate s) = oriented u v by
    simp [u,v,oriented,← Step.rev_rotate]] at hp
  have hv : (visits (affine s b p.1) (oriented u v)).toFinset = touched (Face.send s b p) := by
    rw [corners_positive]
    rcases lt_or_gt_of_ne (show s.perm i ≠ s.perm j from s.perm.injective.ne p.2.property.ne) with h|h
    · change (visits _ (square (s.perm i) (s.perm j))).toFinset =
        (visits _ (square (min _ _) (max _ _))).toFinset
      rw [min_eq_left h.le, max_eq_right h.le]; rfl
    · change (visits (Face.lower p s b) (oriented (posDir (s.perm i)) (posDir (s.perm j)))).toFinset =
        (visits _ (oriented (posDir (min _ _)) (posDir (max _ _)))).toFinset
      rw [min_eq_right h.le, max_eq_left h.le, corner_set, corner_set,
        add_right_comm (b := (posDir (s.perm i)).vec)]
      ext; simp; tauto
  rw [← hv, ← hp]
  change _ = (visits p.1 (oriented (posDir i) (posDir j))).toFinset.image _
  ext; simp

lemma flags_send (s : Signed) (b : Site n) (t : ℝ) (U : Config G n) :
    (flags t (pull s b U)).image (affine s b) = flags t U := by
  have send_chord (p : Face (Per n)) :=
    Face.send_price U p s b G.chord G.chord_inv fun k g => G.chord_conj g k
  ext x; constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, hgt⟩ := (flags_spec ..).mp hy
    exact (flags_spec ..).mpr ⟨Face.send s b p, by
      rw [touched_send]; exact Finset.mem_image_of_mem _ hp, send_chord p ▸ hgt⟩
  · intro hx
    obtain ⟨p, hp, hgt⟩ := (flags_spec ..).mp hx
    obtain ⟨q,rfl⟩ := (Finite.injective_iff_surjective.mp (Face.injective_send s b)) p
    rw [touched_send] at hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image_of_mem _ ((flags_spec ..).mpr ⟨q, hy, by rw [send_chord]; exact hgt⟩)

/-- The eligible test of a transported address, using actual flags. -/
lemma eligible_send (s : Signed) (b : Site n) (t : ℝ) (U : Config G n)
    (a c : ForcedAddress G n) (hs : c.support = a.support.image (affine s b))
    (hi : c.inventory = a.inventory.image (affine s b))
    (he : c.extraTest U ↔ a.extraTest (pull s b U)) :
    c.eligible t U ↔ a.eligible t (pull s b U) := by
  have hf : Function.Injective (affine s b) := fun x y h => s.act_injective (add_right_cancel h)
  unfold ForcedAddress.eligible
  rw [hs, hi, he, ← flags_send s b t U, ← Finset.image_inter _ _ hf,
    (Finset.image_injective hf).eq_iff]

/-! Gauge invariance, Borel and final-site reads at fixed threshold. -/

lemma eligible_gauge (t : ℝ) (a : ForcedAddress G n) (k : Site n → G.El)
    (U : Config G n) (h : a.extraTest (gauge k U) ↔ a.extraTest U) :
    a.eligible t (gauge k U) ↔ a.eligible t U := by
  rw [ForcedAddress.eligible, ForcedAddress.eligible, gauge_flags, h]

/-- Use `flags_measurable_eq` on the finite torus. -/
lemma eligible_measurable (t : ℝ) (a : ForcedAddress G n)
    (h : MeasurableSet {U | a.extraTest U}) : MeasurableSet {U | a.eligible t U} := by
  have hf : MeasurableSet {U : Config G n | a.support ∩ flags t U = a.inventory} := by
    rw [show {U : Config G n | a.support ∩ flags t U = a.inventory} =
      ⋃ p : {X : Support n // a.support ∩ X = a.inventory}, {U | flags t U = p.val} by
      ext U; simp only [Set.mem_setOf_eq, Set.mem_iUnion]; constructor
      · exact fun H ↦ ⟨⟨flags t U,H⟩,rfl⟩
      rintro ⟨p,hp⟩; rw [hp]; exact p.property]
    exact MeasurableSet.iUnion fun _ ↦ flags_measurable_eq ..
  exact hf.inter h

lemma eligible_reads (t : ℝ) (a : ForcedAddress G n) (h : UsesFinal t a.support a.extraTest) :
    UsesFinal t a.support (a.eligible t) := by
  intro U V hag hf
  rw [ForcedAddress.eligible, ForcedAddress.eligible, hf, h _ _ hag hf]

lemma reads_larger {t : ℝ} {p q : Support n} (hpq : p ⊆ q) {B : Sort*} {f : Config G n → B}
    (h : UsesFinal t p f) : UsesFinal t q f := by
  intro U V ha hf
  refine h U V (agrees_mono ha (fun _ hx => hpq hx)) ?_
  calc
    p ∩ flags t U = p ∩ (q ∩ flags t U) := by
      rw [← Finset.inter_assoc, Finset.inter_eq_left.mpr hpq]
    _ = p ∩ flags t V := by rw [hf, ← Finset.inter_assoc, Finset.inter_eq_left.mpr hpq]

variable {X : Pipes G n} {P : BudgetPoint} {d : Tap G n} {δ u : ℝ}

lemma fused_forcedFamily (F : ℕ ≃ X.Pellet) (H : X.Digests d P δ u) :
    (fused F P d).ForcedFamily P := by
  classical
  -- First the conjunction of old eligibility tests in the new extraTest.
  have tg (i : ℕ) (k : Site n → G.El) (U : Config G n) :
      (addr F P i).extraTest (gauge k U) ↔ (addr F P i).extraTest U := by
    change condition F P i _ ↔ condition F P i _
    have h (j) : (X.kernel j).eligible P.threshold (gauge k U) ↔ (X.kernel j).eligible P.threshold U :=
      eligible_gauge _ _ _ _ (H.stamp.forced.symtest j k U)
    simp only [condition,h]
  have tm (i : ℕ) : MeasurableSet {U | (addr F P i).extraTest U} := by
    change MeasurableSet {U | condition F P i U}
    unfold condition; rw [Set.setOf_forall]
    apply MeasurableSet.iInter; intro j
    by_cases hj : j ∈ lefts (F i).val
    · simp only [hj, true_imp_iff]
      exact eligible_measurable P.threshold _ (H.stamp.forced.meas_test j)
    simp [hj]
  have patch_sub (i : ℕ) (l : Ovens.Label) (hl : l ∈ (F i).val) : X.patch l ⊆ (addr F P i).support :=
    fun x hx => Finset.mem_biUnion.mpr ⟨l,hl,hx⟩
  have tr (i : ℕ) : UsesFinal P.threshold (addr F P i).support (addr F P i).extraTest := by
    intro U V ha hf
    have h (j : ℕ) (hj : j ∈ lefts (F i).val) :
        (X.kernel j).eligible P.threshold U = (X.kernel j).eligible P.threshold V := by
      have hs : (X.kernel j).support ⊆ (addr F P i).support :=
        patch_sub i (.inl j) (by simpa only [lefts, Finset.mem_toLeft] using hj)
      exact reads_larger hs (eligible_reads _ _ (H.stamp.forced.reads_test j)) U V ha hf
    change condition F P i U = condition F P i V
    exact propext ⟨fun HH j hj => (h j hj).mp (HH j hj), fun HH j hj => (h j hj).mpr (HH j hj)⟩
  -- Fuse over the addresses themselves. Left reaches use the old K facts;
  -- right reaches use those of logarithm.
  have rg (l : Ovens.Label) : GaugeInvariant (reach d l) := by
    cases l with
    | inl i => exact H.stamp.forced.sym i
    | inr i =>
      intro k U
      change Real.exp (d.logarithm i _) - 1 = Real.exp (d.logarithm i _) - 1
      rw [H.steady i k U]
  have rm (l : Ovens.Label) : Measurable (reach d l) := by
    cases l with
    | inl i => exact H.stamp.forced.meas i
    | inr i => exact ((Real.continuous_exp.measurable).comp (H.reads i)).sub measurable_const
  have rr (l : Ovens.Label) : UsesFinal P.threshold (X.patch l) (reach d l) := by
    cases l with
    | inl i => exact H.stamp.forced.reads i
    | inr i =>
      intro U V ha hf
      change Real.exp (d.logarithm i _) - 1 = Real.exp (d.logarithm i _) - 1
      rw [H.looks i U V ha hf]
  refine ⟨?_, tg, ?_, tm, ?_, tr, ?_⟩
  · intro i k U
    change solid F P d i (gauge k U) = solid F P d i U
    have he := eligible_gauge P.threshold (addr F P i) k U (tg i k U)
    by_cases h : (addr F P i).eligible P.threshold U
    · simp only [solid, h, he, ↓reduceIte]
      exact Finset.prod_congr rfl fun l _ => rg l k U
    simp only [solid,h,he, ↓reduceIte]
  · intro i
    change Measurable (solid F P d i)
    unfold solid
    exact Measurable.ite (eligible_measurable _ _ (tm _))
      (Finset.measurable_fun_prod _ fun l _ => rm l) measurable_const
  · intro i U V ha hf
    change solid F P d i U = solid F P d i V
    have he := eligible_reads P.threshold (addr F P i) (tr i) U V ha hf
    by_cases h : (addr F P i).eligible P.threshold V
    · simp only [solid,h,he, ↓reduceIte]
      exact Finset.prod_congr rfl fun l hl => reads_larger (patch_sub i l hl) (rr l) U V ha hf
    simp only [solid,h,he, ↓reduceIte]
  intro i U h
  by_contra he
  exact h (show solid F P d i U = 0 from if_neg (c := (addr F P i).eligible P.threshold U) he)

/-!
Lift the two given permutations of addresses. `contains` checks lefts,
connectedness (`Ac.Spark`) and disjoint old forced supports; every one is
preserved and reflected, not just those on a particular occurrence.
-/

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

lemma fused_moves (F : ℕ ≃ X.Pellet) (H : X.Digests d P δ u) (s : Signed) (b : Site n) :
    Nonempty ((fused F P d).Moves s b) := by
  classical
  obtain ⟨m⟩ := H.stamp.moves s b
  obtain ⟨q,hq,hqval⟩ := H.carries s b
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
  refine ⟨⟨m.ep, k, m.reg_site, m.reg_support, hs, hi, ht, m.valuesE, ?_⟩⟩
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

theorem answer : YM.Bid.H03 := by
  intro G n X d F δ u P H
  exact ⟨fused_forcedFamily F H, fused_moves F H⟩

end YM.Work.H03
