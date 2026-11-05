import YM.Further.THRESHOLD_SOURCE_RESTART.Baked
/-!
# Every history in the restarted K moves

Target `Rep.Lawful`. Even though the ultimate marker answer doesn't
require one common Moves for its own lamps here, P must be a complete
unmarked Rep. On *all* permutations of the given form; no assumption of
a coherent underlying group action on old labels. No new winding identifications.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Sluice.Menu
open Function Set Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Work.H03 WilsonStartup Finset Relation
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {α : Type} {n : Side} {H : Rep G n} {q : BudgetPoint} (L : Menu H q α)
variable {s : Signed} {x : Site n} (m : H.activities.Moves s x)
private abbrev spin (p : Support n) (s : Signed) (x : Site n) := p.image (affine s x)
lemma looks (p : Support n) : inspected (p.image (affine s x))=(inspected p).image (affine s x) := by
  change inspected (spin p s x)=spin (inspected p) s x
  have he : ∀ j : WilsonStartup.Cell n, Disjoint (spin p s x) (touched (Face.send s x j)) ↔ Disjoint p (touched j) := by
    intro j; rw [Work.H03.touched_send,spin,Finset.disjoint_image (aff_inj s x)]
  unfold spin inspected; rw [Finset.image_union,Finset.biUnion_image]; congr 1
  ext i; rw [Finset.mem_biUnion,Finset.mem_biUnion]; constructor
  · rintro ⟨r,hr,hx⟩
    obtain ⟨j,rfl⟩ := (Finite.injective_iff_surjective.mp (Face.injective_send (R:=Per n) s x)) r
    split at hx; simp at hx
    next h => exact ⟨j,Finset.mem_univ _,by rw [if_neg (mt (he _).2 h)]; rwa [touched_send] at hx⟩
  rintro ⟨r,hr,hx⟩; split at hx; simp at hx
  next h => exact ⟨Face.send s x r, Finset.mem_univ _,by rw [if_neg (mt (he _).1 h), touched_send]; exact hx⟩

def wheel : Equiv.Perm (Codes n α) := Equiv.sumCongr m.kp (Equiv.sumCongr (Key.perm s x) (L.more.move s x))
private lemma mem_image_of_injective {β γ : Type*} [DecidableEq γ] {f : β → γ} {i} {s : Finset β} (h : Injective f) :
    f i ∈ s.image f ↔ i∈s := by simp [h.eq_iff]
private lemma resale {β : Type*} (f : Equiv.Perm β) {s i} : f i ∈ f.finsetCongr s ↔ i∈s := by simp
private lemma spun_walls (i) : walls q (Key.perm s x i)=spin (walls q i) s x := by
  ext j; obtain ⟨j,hj⟩ := (frameSites s x).surjective j
  subst hj
  have he : Injective (affine s x) := aff_inj s x
  change affine s x j∈ _ ↔ affine s x j∈_
  rw [spin, mem_image_of_injective he]; unfold walls
  simp only [Lattice.halo_spec, Finset.mem_singleton,exists_eq_left]
  change separation (affine s x i.native) _ ≤ _ ↔ _
  rw [affine,affine,separation_translate,separation_signed]
private lemma wheels (i : Codes n α) : L.zone (L.wheel m i)=spin (L.zone i) s x := by
  rcases i with i|i|i
  · change inspected (H.activities.forced (m.kp i)).support=_; rw [m.forced_support]; exact looks _
  · exact spun_walls _
  exact L.more.carries ..
private lemma wheels_set (z : Finset (Codes n α)) : ((L.wheel m).finsetCongr z).toLeft=z.toLeft.image m.kp := by
  ext j; obtain ⟨i,rfl⟩ := m.kp.surjective j
  rw [mem_image_of_injective m.kp.injective, mem_toLeft,mem_toLeft]; exact resale (L.wheel m) (i:=Sum.inl i)
private lemma wheels_paint (z : Finset (Codes n α)) : L.paint ((L.wheel m).finsetCongr z)=(L.paint z).image (Key.perm s x) := by
  ext j; obtain ⟨i,rfl⟩ := (Key.perm s x).surjective j
  unfold paint; rw [mem_image_of_injective (Key.perm s x).injective,mem_toLeft,mem_toLeft,mem_toRight,mem_toRight]
  exact resale (L.wheel m) (i:=Sum.inr (Sum.inl i))

private lemma capstan {β η φ : Type*} (e : Equiv.Perm β) (v : η → φ) [DecidableEq η] [DecidableEq φ]
    (f : β → Finset η) (g : β → Finset φ) (h : ∀ i, g (e i)=(f i).image v) (t : Finset β) :
    (e.finsetCongr t).biUnion g=(t.biUnion f).image v := by
  ext x; constructor
  · intro hi; obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨i,rfl⟩ := e.surjective b; rw [h] at he; obtain ⟨b,hb',rfl⟩ := mem_image.mp he
    exact mem_image_of_mem _ (mem_biUnion.mpr ⟨i,(resale _).mp hb,hb'⟩)
  intro hi; obtain ⟨b,hb,rfl⟩ := mem_image.mp hi; obtain ⟨i,hi,hb⟩ := mem_biUnion.mp hb
  exact mem_biUnion.mpr ⟨e i,(resale _).mpr hi,by rw [h]; exact mem_image_of_mem _ hb⟩
private lemma pins (z) : L.limit ((L.wheel m).finsetCongr z)=spin (L.limit z) s x :=
    capstan _ _ _ _ (L.wheels m) z
private lemma paint_coil (z) : L.inv ((L.wheel m).finsetCongr z)=spin (L.inv z) s x := by
  rw [inv,L.wheels_paint]; simpa only [Equiv.finsetCongr_apply,Finset.map_eq_image] using! capstan (Key.perm s x) _ Key.skin _ (fun i=> Key.spun ..) (L.paint z)

private lemma ignition {β : Type*} (X : β → Support n) (e : Equiv.Perm β) (z : Finset β)
    (h : ∀ i,X (e i)=spin (X i) s x) : Ac.Spark X z ↔ Ac.Spark X (e.finsetCongr z) := by
  let f := e.finsetCongr
  have he (i) : e i ∈ f z ↔ i∈z := resale _
  have hs (i j) : Ac.bonds X (f z) (e i) (e j) ↔ Ac.bonds X z i j := by
    simp only [Ac.bonds,Ac.meets,he,h]
    have hh : ¬Disjoint (spin (X i) s x) (spin (X j) s x) ↔ ¬ Disjoint (X i) (X j) := not_congr (disjoint_image (aff_inj ..))
    exact and_congr_right fun _ => and_congr_right fun _ => by simpa only [Finset.not_disjoint_iff] using hh
  constructor
  · intro h; obtain ⟨a,ha⟩ := h.1
    refine ⟨⟨e a,(he a).mpr ha⟩,fun i hi j hj => ?_⟩
    obtain ⟨p,rfl⟩ := e.surjective i; obtain ⟨q,rfl⟩ := e.surjective j
    exact (h.2 p ((he _).mp hi) _ ((he _).mp hj)).lift e fun i j h => (hs i j).mpr h
  intro h; obtain ⟨a,ha⟩ := h.1; obtain ⟨b,rfl⟩ := e.surjective a
  refine ⟨⟨b,(he _).mp ha⟩,fun i hi j hj => ?_⟩
  have he' := (h.2 (e i) ((he _).mpr hi) (e j) ((he _).mpr hj)).lift e.symm (p:=Ac.bonds X z) (fun i j h => ?_)
  · unfold onFun at he'; rw [e.symm_apply_apply,e.symm_apply_apply] at he'; exact he'
  obtain ⟨k,rfl⟩ := e.surjective i; obtain ⟨l,rfl⟩ := e.surjective j; unfold onFun; rw [e.symm_apply_apply,e.symm_apply_apply]; exact (hs _ _).mp h

private lemma grips (z : Finset (Codes n α)) : L.Fuel z ↔ L.Fuel ((L.wheel m).finsetCongr z) := by
  unfold Fuel; rw [ignition L.zone (L.wheel m) z (L.wheels m),L.wheels_paint, Finset.image_nonempty,L.wheels_set]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  have hv (j k : ℕ) : Disjoint (oldSites H (m.kp j)) (oldSites H (m.kp k)) ↔ Disjoint (oldSites H j) (oldSites H k) := by
    unfold oldSites; rw [m.forced_support,m.forced_support,disjoint_image (aff_inj ..)]
  constructor
  · intro h i hi j hj e
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hi; obtain ⟨l,hl,rfl⟩ := mem_image.mp hj
    exact (hv _ _).2 (h hb hl fun H => e (congr_arg _ H))
  intro h i hi j hj e; exact (hv _ _).mp (h (mem_image_of_mem m.kp hi) (mem_image_of_mem m.kp hj) (m.kp.injective.ne e))

def turning : Equiv.Perm L.Record := Equiv.subtypeEquiv (L.wheel m).finsetCongr (L.grips m)
private lemma shifts (i : L.Record) (U : Config G n) : L.Ready (L.turning m i) U ↔ L.Ready i (pull s x U) := by
  unfold Ready; simp only [turning,Equiv.subtypeEquiv_apply]; rw [L.wheels_paint m,L.wheels_set m,L.paint_coil m]
  have he : Injective (affine s x) := aff_inj ..
  let f := pull s x U
  have hE j := list_transfer q j U s x
  have ht j : ¬ Disjoint (Key.skin (Key.perm s x j)) (spin (L.inv i.val) s x) ↔ ¬Disjoint j.skin (L.inv i.val) := by
    rw [Key.spun,spin, Finset.disjoint_image he]
  have hi j : permits H (m.kp j) U ↔ permits H j f := eligible_send s x H.p.threshold _ _ _
    (m.forced_support _) (m.forced_inventory _) (m.forced_tests _ _)
  have hx : ((i.val.toLeft.image m.kp).biUnion (claims H)) = spin (i.val.toLeft.biUnion (claims H)) s x := by
    simpa only [Equiv.finsetCongr_apply,Finset.map_eq_image] using! capstan m.kp _ (claims H) _ m.forced_inventory i.val.toLeft
  rw [hx,spin,← flags_send s x H.p.threshold U, ← Finset.image_inter _ _ he,spin,Finset.image_subset_image_iff he]
  constructor <;> rintro ⟨h,p,t,hu⟩
  · refine ⟨fun j hj => (hE _).mp (h (mem_image_of_mem _ hj)), fun j hj hh => ?_, fun j hj =>
      (hi j).mp (t _ (mem_image_of_mem _ hj)),hu⟩
    exact (mem_image_of_injective (Key.perm s x).injective).mp (p _ ((hE _).mpr hj) ((ht _).mpr hh))
  refine ⟨fun j hj => ?_,fun j hj hh => ?_,fun j hj => ?_,hu⟩
  · obtain ⟨k,hk,rfl⟩ := mem_image.mp hj; exact (hE _).mpr (h hk)
  · obtain ⟨b,rfl⟩ := (Key.perm s x).surjective j; exact mem_image_of_mem _ (p _ ((hE _).mp hj) ((ht _).mp hh))
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hj; exact (hi _).2 (t p hp)
private lemma stays (U : Config G n) (p : L.Record) : L.solid (L.turning m p) U=L.solid p (pull s x U) := by
  have hi : _ ↔ _ := eligible_send s x q.threshold U (L.sole p) (L.sole (L.turning m p)) (L.pins m _) (L.paint_coil m _) (L.shifts m _ _)
  unfold solid; rw [hi]; split
  · change (∏ j ∈ p.val.map (L.wheel m).toEmbedding, L.glow j U)=_
    rw [Finset.prod_map]; apply Finset.prod_congr rfl
    intro j _; rcases j with j|j|j
    · rfl
    · exact congr_arg Real.exp (L.flare.shifts s x j U)
    exact congr_arg (fun v=> Real.exp v - 1) (L.more.shifts s x j U)
  rfl

private def lamps : Equiv.Perm L.Book := Equiv.sumCongr (L.turning m) (Equiv.prodCongr (Equiv.refl ℕ) (frameSites s x))
private lemma transmits (i : L.Book) : (L.stamp (L.lamps m i)).support=spin (L.stamp i).support s x ∧
    (L.stamp (L.lamps m i)).inventory=spin (L.stamp i).inventory s x ∧
    (∀ U,(L.stamp (L.lamps m i)).extraTest U ↔ (L.stamp i).extraTest (pull s x U)) ∧
    ∀ U,L.tailK (L.lamps m i) U=L.tailK i (pull s x U) := by
  rcases i with i|i
  · refine ⟨L.pins m _,L.paint_coil m _, L.shifts m i,fun U => ?_⟩
    change L.solid (L.turning m i) U * (∏ j ∈ ((L.wheel m).finsetCongr i.val).toLeft, _)=_
    rw [L.stays m,L.wheels_set,Finset.prod_image m.kp.injective.injOn]; exact congr_arg _ (Finset.prod_congr rfl fun i _ => m.valuesK i U)
  have h : ({affine s x i.2} : Finset _) = spin {i.2} s x := Finset.image_singleton .. |>.symm
  exact ⟨h,h,fun _ => Iff.rfl,fun U => by change 0*_=(0:ℝ)*_; simp⟩

def mobilized [Countable α] : L.printer.activities.Moves s x where
  ep := m.ep
  kp := L.label.trans ((L.lamps m).trans L.label.symm)
  reg_site := m.reg_site
  reg_support := m.reg_support
  forced_support i := by
    change (L.stamp (L.label (L.label.symm _))).support=_; rw [L.label.apply_symm_apply]; exact (L.transmits m _).1
  forced_inventory i := by
    change (L.stamp (L.label (L.label.symm _))).inventory=_; rw [L.label.apply_symm_apply]; exact (L.transmits m _).2.1
  forced_tests i U := by
    change (L.stamp (L.label (L.label.symm _))).extraTest _ ↔ _; rw [L.label.apply_symm_apply]; exact (L.transmits m _).2.2.1 U
  valuesE := m.valuesE
  valuesK i U := by change L.tailK (L.label (L.label.symm _)) U= _; rw [L.label.apply_symm_apply]; exact (L.transmits m _).2.2.2 U
end YM.Further.ThresholdSourceRestart.Sluice.Menu
