import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Aurora

/-!
# Eject/import one coherent dictionary
 Path supports don't depend on β or on reobtaining Cash; canonical
 correspondence on equally-labelled words, and lift of all optional
 moves to *actual* F-average values. The latter still needs an anchor
 discipline on indexed Listing.reg (do separately). This file constructs
 the common-support equivalences. Does not use proof uniqueness of a `Cash`.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Match
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter Pond
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R R' : RG.Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

-- generic bundled relabelling; equiv H Thin/Thick etc when H order exact (use same purchased order across parameters).
section roll
variable {ι κ η : Type}
def batches (p : ι≃κ) : Clusters ι≃ Clusters κ := Equiv.sigmaCongrRight fun _ => Equiv.arrowCongr (Equiv.refl _) p
def tallyVip (p : ι ≃ κ) (x : Finset ι) : ↥x ≃ ↥(p.finsetCongr x) := Equiv.subtypeEquiv p (Turn.given _ _ _|>.1 rfl)
def scrolls (p : ι ≃ κ) : Multiple.Reps ι ≃ Multiple.Reps κ := Equiv.sigmaCongr p.finsetCongr fun x => Equiv.arrowCongr (tallyVip p x) (Equiv.refl _)
lemma periodic (p : ι≃κ) (x : Multiple.Reps ι) : ∀ j,j∈x.1↔ p j ∈ (scrolls p x).1 := (Turn.given p _ _).1 rfl
lemma vol (p : ι ≃ κ) (x : Finset ι) (y : ↥x → ℕ) (i : ↥x) : (scrolls p ⟨x,y⟩).2 (tallyVip p x i)=y i := congr_arg y ((tallyVip p x).symm_apply_apply _)
lemma numbers (p : ι ≃ κ) (c : Multiple.Reps ι) (i : ↥c.1) : (scrolls p c).2 (show ↥(scrolls p c).1 from tallyVip p c.1 i)=c.2 i := by rcases c with ⟨c,k⟩; exact vol ..
lemma cashes (p : ι ≃ κ) (u : ι → ℝ) (v : κ → ℝ) (h : ∀ i,u i=v (p i)) (z : Multiple.Reps ι) : manyW u z=manyW v (scrolls p z) := Fintype.prod_equiv (tallyVip p z.1) _ _ fun i=> by rw [numbers, h]; rfl
lemma accounts {ι' κ' : Type} (p : ι≃κ) (q : ι'≃κ') (t : Reps (ι⊕ι')) (i : ι) :
    i∈t.fst.toLeft ↔ p i∈(scrolls (Equiv.sumCongr p q) t).1.toLeft := by rw [mem_toLeft,mem_toLeft]; exact (Turn.given (Equiv.sumCongr p q) _ _).1 rfl (.inl i)
lemma uncount {ι' κ' : Type} (p : ι≃κ) (q : ι'≃κ') (t : Reps (ι⊕ι')) (i : ι') :
    i∈t.fst.toRight ↔ q i∈(scrolls (Equiv.sumCongr p q) t).1.toRight := by rw [mem_toRight,mem_toRight]; exact (Turn.given (Equiv.sumCongr p q) _ _).1 rfl (.inr i)
lemma stays {ι' κ' : Type} (p : ι≃κ) (q : ι'≃κ') (t : Reps (ι⊕ι')) : Letter.staysOne t ↔ Letter.staysOne (scrolls (Equiv.sumCongr p q) t) := by
  constructor
  · intro h i; obtain ⟨i,rfl⟩:=p.surjective i; intro hx
    have he : Sum.inl i∈ t.1 := mem_toLeft.mp ((accounts p q t i).2 (mem_toLeft.mpr hx)); exact (numbers (Equiv.sumCongr p q) t ⟨.inl i,he⟩).trans (h i he)
  intro h i hx; have ht : Sum.inl (p i) ∈ (scrolls (Equiv.sumCongr p q) t).1 := mem_toLeft.mp ((accounts p q t i).1 (mem_toLeft.mpr hx)); exact (numbers _ _ (show ↥t.1 from ⟨.inl i,hx⟩)).symm.trans (h _ ht)
lemma blocked_bit (p : ι ≃ κ) (e : Equiv.Perm (Site c)) {A : ι → Support c} {D : κ → Support c} (h : ∀ i,D (p i)=(A i).image e) (i j) : blocked A i j↔blocked D (p i) (p j) := by
  refine or_congr p.injective.eq_iff.symm ?_; unfold Ac.meets; conv_rhs=> rw [← e.exists_congr_right];
  simp_rw [h]; simp
lemma spaceApart {R : ι → ι → Prop} {S : κ→ κ→ Prop} (p : ι≃κ) (h : ∀ i j,R i j ↔ S (p i) (p j)) {x : Finset ι} {y : Finset κ} (ht : ∀ i,i∈x↔p i∈y) : separated R x↔separated S y := by
  constructor
  · intro H i; obtain ⟨i,rfl⟩:= p.surjective i; intro hi j; obtain ⟨j,rfl⟩:= p.surjective j; intro hj hk
    exact not_congr (h i j)|>.1 (H _ ((ht i).2 hi) _ ((ht j).2 hj) (p.injective.eq_iff.not.mp hk))
  exact fun H i hi j hj hk=> not_congr (h i j)|>.2 (H _ ((ht i).1 hi) _ ((ht j).1 hj) (p.injective.ne hk))
lemma arena (A : ι→ Support c) (D : κ→ Support c) (p : ι≃κ) (e : Equiv.Perm (Site c)) (h : ∀ i,D (p i)=(A i).image e) (Z : Clusters ι) :
    unionOf D (batches p Z).2=(unionOf A Z.2).image e := Turn.gains (Equiv.refl _) e (A:=univ) (D:=univ) (Y:=A ∘ Z.2) (X:=D ∘ (batches p Z).2) (fun _=> (Turn.display e _ _).1 (h _)) fun _=>Iff.rfl
lemma weighs {R : ι → ι → Prop} {S : κ → κ → Prop} (p : ι ≃ κ) (h : ∀ i j,R i j ↔ S (p i) (p j)) (z : Clusters ι) : coefficient R z.2=coefficient S (batches p z).2 := by
  rcases z with ⟨z,Z⟩; change coefficient R Z=coefficient S (fun i=> p (Z i)); apply congr_arg Graph.mass; ext x
  rw [potential_mem,potential_mem]; simp_rw [h]
lemma sale {R : ι → ι → Prop} {S : κ → κ → Prop} (p : ι ≃ κ) (u : ι →ℝ) (v : κ → ℝ) (h : ∀ i j,R i j ↔ S (p i) (p j))
    (he : ∀ i,u i=v (p i)) (z : Clusters ι) : Gas.term R u z=Gas.term S v (batches p z) := by
  rcases z with ⟨z,Z⟩; unfold Gas.term; rw [weighs p h ⟨z,Z⟩]; simp_rw [he]; rfl
end roll
section parks
variable (H : Cash W α μ L Q o C T R) (J : Cash W α μ L Q o C T R') (s : Signed) (t : Site c)
structure Alliance where
  units : Molecule S≃Molecule S
  terrain i : J.unionP (units i)=(H.unionP i).image (affine s t)
  rosterC i : (roster (units i)).flags=(roster i).flags.image (affine s t)

-- essentially A.New → J.Old
variable {H J s t}
namespace Alliance
variable (K : Alliance H J s t)
include K
def bearing : H.ThinP≃ J.ThinP := Equiv.subtypeEquiv K.units fun i=> by rw [K.terrain,K.rosterC]; simp
def honoring : H.ThickP≃ J.ThickP := Equiv.subtypeEquiv K.units fun i=> by rw [K.terrain,K.rosterC]; simp
lemma young (i : H.ThinP) : J.smallAt (K.bearing i)=(H.smallAt i).image (affine s t) := K.terrain i.val
lemma elder (i : H.ThickP) : J.largeAt (K.honoring i)=(H.largeAt i).image (affine s t) := K.terrain i.val
lemma counted (i : H.ThickP) : (roster (K.honoring i).val).flags=(roster i.val).flags.image (affine s t) := K.rosterC i.val
lemma ne (i j) : blocked H.largeAt i j↔blocked J.largeAt (K.honoring i) (K.honoring j) := blocked_bit K.honoring (StepData.sendSites s t) K.elder i j
lemma sec (i j) : H.seam i j ↔ J.seam (K.bearing i) (K.bearing j) := blocked_bit K.bearing (StepData.sendSites s t) K.young i j
abbrev furrow := batches K.bearing
def editor := Equiv.sumCongr K.honoring K.furrow
abbrev tongs := scrolls K.editor
lemma alcove (i : H.Chapter) : J.bookFoot (K.editor i)=(H.bookFoot i).image (affine s t) := by
  rcases i with i|i
  · exact K.elder i
  exact arena H.smallAt J.smallAt K.bearing (StepData.sendSites s t) K.young i
lemma hearth (i : H.Chainbook) : J.library (K.tongs i)=(H.library i).image (affine s t) := by
  unfold Cash.library
  have hh (j) : j∈i.1↔ K.editor j∈(K.tongs i).1 := periodic _ i j
  exact Turn.gains K.editor (StepData.sendSites s t) (Y:=H.bookFoot) (X:=J.bookFoot) (A:=i.1) (D:=(K.tongs i).1) (fun j=> (Turn.display _ _ _).1 (K.alcove j)) hh
lemma fireplaces (i : H.Chainbook) : J.inventory (K.tongs i).1.toLeft=(H.inventory i.1.toLeft).image (affine s t) :=
    Turn.gains K.honoring (StepData.sendSites s t) (Y:=fun u=>(roster u.val).flags) (X:=fun u=>(roster u.val).flags) (fun j=> (Turn.display _ _ _).1 (K.counted j)) (accounts K.honoring K.furrow i)
lemma splint (i : H.Chainbook) : Ac.Spark H.bookFoot i.1↔ Ac.Spark J.bookFoot (K.tongs i).1 :=
    Turn.seam K.editor (StepData.sendSites s t) (fun j=> (Turn.display _ _ _).1 (K.alcove j)) (periodic K.editor i)
lemma sap (i : H.Chainbook) : H.Fresh i↔J.Fresh (K.tongs i) := by
  unfold Cash.Fresh; apply and_congr (stays K.honoring K.furrow i); apply and_congr (spaceApart K.honoring K.ne (accounts K.honoring K.furrow i));
  conv_rhs=> rw [← K.furrow.forall_congr_right];
  refine forall_congr' fun a=> imp_congr (uncount K.honoring K.furrow i a) (not_congr (Turn.assign_guard (StepData.sendSites s t) ((Turn.display _ _ _).1 ?_) ((Turn.display _ _ _).1 (K.alcove (.inr a)))))
  exact Turn.gains K.honoring (StepData.sendSites s t) (fun y=> (Turn.display _ _ _).1 (K.elder y)) (accounts K.honoring K.furrow i)
lemma festoon (V : Config G c) (i : H.Chainbook) : H.statesPool (pull s t V) i↔ J.statesPool V (K.tongs i) := by
  unfold Cash.statesPool; rw [K.fireplaces,K.hearth,← Work.H03.flags_send s t (Pressure.temp α) V,← Finset.image_inter _ _ (show Injective (affine s t) from (StepData.sendSites s t).injective)]; exact ((Finset.image_injective (StepData.sendSites s t).injective).eq_iff).symm
end Alliance
end parks
end YM.PhysicalNext.Repeat.Match
