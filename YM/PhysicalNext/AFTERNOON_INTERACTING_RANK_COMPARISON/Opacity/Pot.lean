import YM.Extra.MULTISOURCE_TRAJECTORIES.Trials
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Light
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Toe
import YM.Push.ABSOLUTE_SUMS.Gas

/-!
# Coarse cores. Supports, seed data and responsibility

Keep all labels on the retained period and use absolute-sum pricing API.
Components at full reading halo; do not pay again for owners. Constants
in facet polled at same height.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display.Sew
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A B : Stores S}

namespace Pot
abbrev Core (S : StepData c f) (x : ℝ) := Subtype (Packets.connected S 500 (radiusB x)) -- Ext includes structure
abbrev acre (o : Core S x) := o.val.dome (500*radiusB x)
lemma acres_lit (o : Core S x): (acre o).Nonempty:= by rw [acre, ← support_reads]; exact (support_nonempty ..).mpr o.property.1

def owners (A : Stores S) (x : ℝ) := univ.filter fun o : Core S x=> seeds S o.val∈ Packets.pieces S 500 (radiusB x) A
lemma owned {o : Core S x}: o∈ owners A x ↔ seeds S o.val ∈ Packets.pieces S 500 (radiusB x) A:= by simp [owners]
lemma subcovers {o : Core S x} (h : o∈owners A x): seeds S o.val ⊆ seeds S A:= fun _ hi=> (pieces_price S 500 _ A|>.2.2.1) ▸ mem_biUnion.mpr ⟨_,owned.mp h,hi⟩
lemma owner_eq (U : Finset (Core S x)): U=owners A x ↔ (U:Set (Core S x)).PairwiseDisjoint acre ∧ U.biUnion (fun u=>seeds S u.val)=seeds S A:= by
  let B:= radiusB x
  let v : Core S x ↪ Finset (Seed S):=⟨fun t=> seeds S t.val,fun i j h=> Subtype.ext ((sectorAlphabet S).injective h)⟩
  have hs : (owners A x).map v=Packets.pieces S 500 B A:= by
    ext i; rw [Finset.mem_map]; constructor
    · rintro ⟨z,h,rfl⟩; exact owned.mp h
    intro hi
    have h: connected S 500 B (store S i):= by unfold connected; rw [seeds_store]; exact (pieces_price ..).1 i hi
    exact ⟨⟨_,h⟩, owned.mpr (by change seeds S (store S _)∈_; rw [seeds_store]; exact hi), seeds_store ..⟩
  let f (U:Finset (Core S x)):= U.biUnion fun u=>seeds S u.val
  have he U : (U.map v).biUnion id=f U:= by
    unfold f; ext; simp [v]
  constructor
  · rintro rfl; refine ⟨fun i hi j hj hij=>?_, Eq.trans (he _).symm ?_⟩
    · have ht:= (pieces_price S 500 (radiusB x) A|>.2.1) (owned.mp hi) (owned.mp hj) (fun h=>hij (v.injective (show v i=v j from h)))
      change Disjoint (Packets.support _ _ _ _) (Packets.support _ _ _ _) at ht; rw [support_reads,support_reads] at ht; exact ht
    rw [hs,(pieces_price S 500 (radiusB x) A|>.2.2.1)]
  rintro ⟨hp,hA⟩
  have hf : (U.map v).biUnion id=seeds S A:= (he U).trans hA
  apply Finset.map_injective v; rw [hs, ← show store S ((U.map v).biUnion id)=A from hf ▸ store_seeds ..]
  refine (pieces_of S 500 B _ ?_ ?_).symm
  · rintro _ h; obtain ⟨j,h,rfl⟩:=mem_map.mp h; exact j.property
  intro i hi j hj h; obtain ⟨i,he₁,rfl⟩:=Finset.mem_map.mp hi; obtain ⟨j,he₂,rfl⟩:=Finset.mem_map.mp hj
  change Disjoint (support S _ _ (seeds S _)) (support S _ _ (seeds S _)); rw [support_reads,support_reads]
  exact hp he₁ he₂ (fun e=> h (congr_arg v e))
lemma owner_dome (A : Stores S) (x R) :
    (owners A x).biUnion (fun (t : Core S x)=> dome t.val R)=A.dome R:= by
  have h:= ((owner_eq (A:=A) (owners A x)).1 rfl).2
  ext i; rw [mem_biUnion]; rw [← show R*1=R from mul_one R]; simp_rw [← support_reads];
  rw [← h]; simp only [Packets.support,mem_biUnion]
  constructor
  · rintro ⟨j,hj,v,hv,hp⟩; exact ⟨v,⟨_,hj,hv⟩,hp⟩
  rintro ⟨j,⟨v,hv,hz⟩,hp⟩; exact ⟨_,hv,j,hz,hp⟩

-- convert to Annex1AD certificate for signed windows
open AnalyticBridge.Annulus1AD
lemma pack {o : Core S x} (h : o∈owners A x): Packet o.val A (500*radiusB x):= by
  have hp := subcovers h
  let v:= o.val; let B:= radiusB x
  let e : Equiv (AnalyticBridge.Annulus1AD.Mark S) (Seed S):= Equiv.sumAssoc ..
  have hv (T : Stores S) (i : AnalyticBridge.Annulus1AD.Mark S) : planted T i ↔ e i∈seeds S T:= by rcases i with (i|i)|i <;> simp [e, planted,seeds]
  constructor
  · intro t ht; exact mem_filter.mpr ⟨mem_univ _,(hv A t).mpr (hp ((hv v t).mp (mem_filter.mp ht).2))⟩
  intro i hA hi
  have ht : e i∈(owners A x).biUnion (fun t => seeds S t.val) := by rw [(owner_eq (A:=A) (owners A x)|>.1 rfl).2]; exact (hv _ i).1 hA
  obtain ⟨j,hj,hu⟩:= mem_biUnion.mp ht
  have he:j ≠ o:= by rintro rfl; exact hi ((hv ..).2 hu)
  refine Disjoint.mono_left ?_ (((owner_eq (A:=A) (owners A x)).1 rfl).1 hj h he)
  intro p hp; change p∈ j.val.dome (500*B)
  rw [← support_reads]; refine mem_biUnion.mpr ⟨e i,hu,?_⟩
  rcases i with (i|i)|i <;> exact hp

-- Identify core orientation without assuming every A carried with a branch

def sale (e : Wheel c) : Equiv.Perm (Seed S) := Equiv.sumCongr (shiftFaces e.1 (S.ratio.embed e.2)) (Equiv.sumCongr (StepData.sendBonds e.1 e.2) (orient e))
lemma turnSeeds (e : Wheel c) (A : Stores S): seeds S A=(seeds S (book e.1 e.2 A)).map (sale (S:=S) e).toEmbedding := by
  ext i; obtain ⟨i,rfl⟩:= (sale (S:=S) e).surjective i; rw [mem_map_equiv,Equiv.symm_apply_apply]; rcases i with i|i|i
  · simp [sale,seeds,Locations.book]
  · simp [sale,seeds,Locations.book]
  change _ ∈ Finset.disjSum A.costs (disjSum A.aisles A.flags)↔ _∈disjSum _ (disjSum _ _)
  simp only [sale,Equiv.sumCongr_apply, Sum.map_inr, inr_mem_disjSum]; exact Iff.symm (by rw [Locations.book]; dsimp only; rw [Finset.mem_map_equiv]; rfl)
lemma turnAcre (e : Wheel c) (i : Seed S) (x : ℝ): Packets.skin S 500 (radiusB x) (sale e i) = pushed e (Packets.skin S 500 (radiusB x) i):= by
  unfold Packets.skin; rw [push_walk]; apply congr_arg; unfold pushed Packets.points; rw [Finset.map_eq_image]; rcases i with i|i|i
  · exact Locations.start_map ..
  · exact Locations.pin_map ..
  exact (Finset.image_singleton (orient e) i).symm
lemma moved (e : Wheel c) (x : ℝ) (A : Stores S): Packets.connected S 500 (radiusB x) (book e.1 e.2 A) ↔ Packets.connected S 500 (radiusB x) A:= by
  unfold Packets.connected Whole
  rw [turnSeeds e A]; exact migrate_connect _ _ _ _ (fun i=> turnAcre e i x)

def grow (S : StepData c f) (x : ℝ) (e : Wheel c) (i : Core S x) : Core S x:= ⟨book e.1 e.2 i.val,(moved e x _).2 i.property⟩
lemma turns (e : Wheel c) : Injective (grow S x e) := by
  intro i j h; have he : seeds S i.val=seeds S j.val:=by
    have hx : seeds S (book e.1 e.2 i.val)=seeds S (book e.1 e.2 j.val):= congr_arg (fun i:Core S x=> seeds S i.val) h
    rw [turnSeeds e i.val]; exact (congr_arg _ hx).trans (turnSeeds e j.val).symm
  exact Subtype.ext ((sectorAlphabet S).injective he)

def hoop (S : StepData c f) (x : ℝ) (e : Wheel c) : Equiv.Perm (Core S x) := Equiv.ofBijective (grow S x e) (Finite.injective_iff_bijective.mp (turns _))
lemma hoop_day (S : StepData c f) (x : ℝ) (e : Wheel c) (i : Core S x) : pushed e (acre (hoop S x e i))= acre i:= by
  rw [acre,acre,← support_reads,← support_reads]; rw [turnSeeds e i.val];
  exact (migration (orient e) _ (sale e) _ _ (fun i=>turnAcre e i x)).symm
lemma hoop_level (S : StepData c f) (x : ℝ) (e q : Wheel c) (i : Core S x) : hoop S x (meet e q) i=hoop S x q (hoop S x e i) := Subtype.ext (Pump.marks ..)
def scope : Sheet (fun u:Core S x=> acre u) := ⟨fun e=> (hoop S x e).symm, fun e q i=> by
  change (hoop _ _ _).symm i=_; rw [show hoop S x (meet e q)=(hoop S x e).trans (hoop S x q) from Equiv.ext (hoop_level S x e q)]; rfl, fun e i=>by have hz:=hoop_day S x e ((hoop S x e).symm i); rw [Equiv.apply_symm_apply] at hz; exact hz.symm⟩
lemma rotate_owners (A : Stores S) (x : ℝ) (e : Wheel c): owners (book e.1 e.2 A) x = (owners A x).map (hoop S x e).toEmbedding:= by
  symm
  let Q:= book e.1 e.2 A; let u:= (owners A x).map (hoop S x e).toEmbedding
  have h (i:Core S x): acre (hoop S x e i) = (acre i).map (orient e).symm.toEmbedding:= ne_map (E:=orient e) ((scope (S:=S) (x:=x)).extend e) i
  refine (owner_eq ..).mpr ⟨(migration_disjoint _ _ _ _ h _|>.mp ((owner_eq (owners A x)).1 rfl).1),?_⟩
  have hf (i:Core S x): seeds S i.val=(seeds S (hoop S x e i).val).map (sale (S:=S) e).toEmbedding:= turnSeeds ..
  apply Finset.map_injective (sale e).toEmbedding
  change (u.biUnion _).map _ = _
  rw [← turnSeeds e A]
  have ht:= migration (sale e) u (hoop S x e).symm (fun i=>seeds S i.val) (fun i=>seeds S i.val) (fun i=> (by
    obtain ⟨j,rfl⟩:= (hoop S x e).surjective i; simp only [Equiv.symm_apply_apply]; exact hf j))
  rw [← ht, show u.map (hoop S x e).symm.toEmbedding=owners A x by ext; simp [u]]
  exact ((owner_eq (owners A x)).1 rfl).2
end Pot
end YM.PhysicalNext.InteractingRank.Pump
