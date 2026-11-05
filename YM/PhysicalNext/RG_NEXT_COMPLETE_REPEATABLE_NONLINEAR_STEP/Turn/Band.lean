import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Repaid
import YM.Push.LOCAL_SPLITTING.BundleMoves


/-! # Whole address rotation for first gas

Includes crossing native K force, Stores pieces, towers at all lengths,
mandatory reach. No weight comparisons used to fix support, neither omit
zero labels nor choose reanchoring according to field. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}

section connectivity
variable {α β : Type} [DecidableEq α] [DecidableEq β] (e : α≃β) (g : Equiv.Perm (Site c)) {Y : α→Support c} {X : β→Support c}
    {A : Finset α} {D : Finset β} (hp : ∀ i j,j∈Y i ↔ g j∈ X (e i)) (h : ∀ i,i∈A ↔ e i∈D)
include h hp
omit [DecidableEq α] [DecidableEq β] in
lemma joined (hx : Ac.Spark Y A) : Ac.Spark X D := by
  constructor
  · obtain ⟨i,hi⟩ := hx.1; exact ⟨e i,(h i).1 hi⟩
  intro i; obtain ⟨i,rfl⟩ := e.surjective i; intro hi j; obtain ⟨j,rfl⟩ := e.surjective j
  intro hj; refine Relation.ReflTransGen.lift (r:=Ac.bonds Y A) (p:=Ac.bonds X D) e ?_ _ _ (hx.2 i ((h i).2 hi) j ((h j).2 hj))
  rintro x y ⟨hx,hy,z,hz,hv⟩; exact ⟨(h x).1 hx,(h y).1 hy,g z,(hp x z).1 hz,(hp y z).1 hv⟩
omit [DecidableEq α] [DecidableEq β] in
lemma seam : Ac.Spark Y A ↔ Ac.Spark X D := ⟨joined e g hp h,joined e.symm g.symm (fun i j=> by simpa using (hp (e.symm i) (g.symm j)).symm) (fun i=>by simpa using (h (e.symm i)).symm)⟩
omit [DecidableEq α] [DecidableEq β] in
lemma gains : D.biUnion X=(A.biUnion Y).image g := by
  apply (display g ..).2; intro i; simp only [mem_biUnion]; conv_rhs => rw [← e.exists_congr_right]
  simp_rw [hp,h]
omit [DecidableEq α] [DecidableEq β] in
lemma gaps : (A:Set α).PairwiseDisjoint Y ↔ (D:Set β).PairwiseDisjoint X := by
  refine ⟨fun he i hi j hj hn=> ?_,fun he i hi j hj hn=> ?_⟩
  · obtain ⟨i,rfl⟩ := e.surjective i; obtain ⟨j,rfl⟩ := e.surjective j; exact (assign_guard g (hp i) (hp j)).1 (he ((h i).2 hi) ((h j).2 hj) (fun hk=>hn (congr_arg _ hk)))
  exact (assign_guard g (hp i) (hp j)).2 (he ((h i).1 hi) ((h j).1 hj) (e.injective.ne hn))
end connectivity
section seeds
variable (S) (s : Signed) (b : Site c)
def germ : Equiv.Perm (Packets.Seed S) := Equiv.sumCongr (Locations.shiftFaces s (S.ratio.embed b)) (Equiv.sumCongr (StepData.sendBonds s b) (StepData.sendSites s b))
lemma lettering (A : Stores S) (j : Packets.Seed S) : j∈Packets.seeds S (Locations.book s b A) ↔ germ S s b j∈Packets.seeds S A := by rcases j with i|i|i <;> simp [Packets.seeds,germ,atA,atCost, show ∀ i, i ∈ (Locations.book s b A).flags ↔ StepData.sendSites s b i∈ A.flags from atF s b A]
lemma attached (A : Stores S) (l B : ℕ) : Packets.connected S l B (Locations.book s b A) ↔ Packets.connected S l B A := by
  refine seam (germ S s b) (StepData.sendSites s b) (Y:=Packets.skin S l B) (X:=Packets.skin S l B) (fun i=> (display _ _ _).1 ?_) (lettering S s b A)
  refine halo_pull s b _ _ _ ((display (StepData.sendSites s b) _ _).1 ?_)
  rcases i with i|i|i
  · exact Locations.start_map ..
  · exact pointers ..
  change ({StepData.sendSites s b i}:Support c) = _; simp [Packets.points]
end seeds
section move
variable (T : Tube G S) (R : Rep G f) (π : R.activities.Moves s (S.ratio.embed b))
  (l B : ℕ)
def badge : Equiv.Perm (Head S) := Equiv.sumCongr (books s b S).symm
    (Equiv.sumCongr π.kp (Equiv.sumCongr (logTurn S s b π.ep) (windWarn S s b))) -- uses π
abbrev caravan := (badge R π).finsetCongr
lemma insignia (i : Head S) : areas R T l B (badge R π i)=(areas R T l B i).image (affine s b) := by
  rcases i with A|k|p|p
  · obtain ⟨A,rfl⟩ := (books s b S).surjective A; change ((books s b S).symm _).dome _ = _; rw [Equiv.symm_apply_apply]; exact surround ..
  · exact enlarged _ _ _ _ _ _ (π.forced_support k)
  · exact logStory _ _ π ..
  exact alarmStory ..
variable (Z : Molecule S)
lemma colors : ground R T l B (caravan R π Z)=(ground R T l B Z).image (affine s b) :=
  gains (badge R π) (StepData.sendSites s b) (fun i=> (display _ _ _).1 (insignia T R π l B i)) ((given _ _ _).1 rfl)
lemma frontispiece (A : Stores S) : (books s b S A)∈Z.toLeft ↔ A∈(caravan R π Z).toLeft := by rw [mem_toLeft,mem_toLeft]; simp [caravan,badge]
lemma chart (z : ℕ) : z∈own Z ↔ π.kp z∈own (caravan R π Z) := by rw [literal,literal]; simp [caravan,badge]
lemma mark : roster Z=Locations.book s b (roster (caravan R π Z)) := by
  apply (Packets.sectorAlphabet S).injective; change Packets.seeds S (roster Z)=_
  ext i; change _ ↔ _∈ Packets.seeds _ (Locations.book s b (roster _)); rw [lettering,Matter.register,Matter.register,mem_biUnion,mem_biUnion]
  conv_lhs => rw [← (books s b S).exists_congr_right]
  exact exists_congr fun x => and_congr (frontispiece R π Z x) (lettering S s b x i)
lemma connected_zone : Ac.Spark (areas R T l B) Z ↔ Ac.Spark (areas R T l B) (caravan R π Z) :=
  seam (badge R π) (StepData.sendSites s b) (fun i=> (display _ _ _).1 (insignia T R π l B i)) ((given _ _ _).1 rfl)
lemma zones : Layout (roster Z) l B Z.toLeft ↔ Layout (roster (caravan R π Z)) l B (caravan R π Z).toLeft := by
  let M:=caravan R π Z
  have he : (∀ i∈ Z.toLeft,Packets.connected S l B i)↔ ∀ i∈ M.toLeft,Packets.connected S l B i := by
    conv_lhs=> rw [← (books s b S).forall_congr_right]
    exact forall_congr' fun i=> imp_congr (frontispiece R π Z i) (attached S s b i l B)
  have hv := gaps (books s b S).symm (StepData.sendSites s b) (Y:=fun x=> x.dome (l*B)) (X:=fun x=>x.dome (l*B)) (fun i=> by
    obtain ⟨i,rfl⟩ := (books s b S).surjective i; rw [Equiv.symm_apply_apply]; exact Locations.dome_map s b i (l*B)) (show ∀ i,i∈ Z.toLeft↔ (books s b S).symm i∈ M.toLeft from fun i=>by simpa only [Equiv.apply_symm_apply] using (frontispiece R π Z ((books s b S).symm i)))
  exact ⟨fun h=> ⟨he.1 h.checkpoints,hv.1 h.crews,Matter.register _⟩,fun h=>⟨he.2 h.checkpoints,hv.2 h.crews,Matter.register _⟩⟩
lemma teams : troupe T R l B Z ↔ troupe T R l B (caravan R π Z) := by
  let S1 := StepData.sendSites s (S.ratio.embed b)
  let S2 := Locations.shiftFaces s (S.ratio.embed b)
  refine and_congr (zones R π l B Z) (and_congr (gaps π.kp S1 (fun i=> (display S1 _ _).1 (π.forced_support i)) (chart R π Z)) ?_)
  unfold Contract.incidence; conv_rhs => rw [← π.kp.forall_congr_right]
  apply forall_congr'; intro i; apply imp_congr (chart R π Z i); conv_rhs=> rw [← S1.forall_congr_right]
  refine forall_congr' fun j=> imp_congr ((display S1 _ _).1 (π.forced_inventory i) j) ?_
  rw [mark R π Z]; conv_rhs => rw [← S2.exists_congr_right]
  exact exists_congr fun x=> and_congr (atCost ..) ((display S1 _ _).1 (Work.H03.touched_send ..) _)
end move
section conditions
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    (hv : Y.V=pull s b X.V) (hx : Y.x=X.x) (R : Rep G f) (π : R.activities.Moves s (S.ratio.embed b))
    (l : ℕ) (Z : Molecule S)
include hv hx
lemma needed : RG.flags (Pressure.temp Y.x) Y.V ∩ ground R T l Y.B Z=(roster Z).flags ↔
    RG.flags (Pressure.temp X.x) X.V ∩ ground R T l X.B (caravan R π Z)=(roster (caravan R π Z)).flags := by
  rw [hx,hv, mark R π Z, Finset.ext_iff, Finset.ext_iff]
  conv_rhs=> rw [← (StepData.sendSites s b).forall_congr_right]
  have h : X.B=Y.B := congr_arg radiusB hx.symm; rw [h]
  refine forall_congr' fun i => ?_
  rw [mem_inter,mem_inter]; exact iff_congr (and_congr (toured ..) ((display _ _ _).1 (colors T R π ..) _)) (atF ..)
lemma accounting : standsIn Y R l Z ↔ standsIn X R l (caravan R π Z) := by
  refine and_congr ?_ (and_congr ?_ (needed hv hx R π l Z))
  · unfold Coat.B; rw [hx]; exact connected_zone ..
  unfold Coat.B; rw [hx]; exact teams ..
end conditions
end YM.PhysicalNext.Repeat.Turn
