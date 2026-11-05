import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Guards
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Lens
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Reading
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Apertures
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Curtail
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.CUTOFF_PROJECTORS.Bank
import YM.Push.CUTOFF_PROJECTORS.Passage
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical


/-!
Reuse Sharp's geometric work comparing fog *entries* across tag
synchronizations and Store completions. Here we want to choose sample just
by component inventory, then completing output flags, EVEN for otherwise
impossible components. `Rigging` doesn't quite do that (requires full
K.Makes of sample in nonempty case), so verify Placed & `By` ourselves
(including on invalid script reads) without requiring script realizability
at the sample. Compare to Rig.lean. Use a pad of 11B for affecting any
freeze query out through one B. The script later is responsible for also
not changing any other reads (including of mean).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus 
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Route
 
variable {G : Gauge} {ι E : Type} [DecidableEq E] {c f : Side} {S : StepData c f} {x : ℝ}
    {V : Config G c} {F : Forest S.ratio} {K : Cards S ι E} {A : Stores S} {n : Finset E} {Q : Finset ι}

/-- Completion used for the actual Gaussian purchasing. Will compare
whenever a family `Makes`. -/
def patch (x : ℝ) (V : Config G c) (A : Stores S) : Stores S := { A with flags := RG.flags (temp x) V }

structure Localized (x : ℝ) (K : Cards S ι E) (i : ι) : Prop where
  loaded : (K.seeds i).dome (11*radiusB x) ⊆ K.X i

namespace Localized
variable (M : ∀ i, Localized x K i) (hQ : K.Makes A n Q)
include hQ

lemma compare (i : ι) (hi : i∈Q) : (K.seeds i).costs ⊆ A.costs ∧ (K.seeds i).aisles ⊆ A.aisles ∧
    (K.seeds i).flags ⊆ A.flags := by
  rw [← hQ.2.1]; exact ⟨fun j hj => Finset.mem_biUnion.mpr ⟨i,hi,hj⟩, fun j hj => Finset.mem_biUnion.mpr ⟨i,hi,hj⟩,
    fun j hj => Finset.mem_biUnion.mpr ⟨i,hi,hj⟩⟩

private lemma far {j i : ι} {w : Site c} (hi : i∈Q) (hw : w∈K.X i) (hj : j∈Q) (hv : w∈K.X j) : i=j :=
    Classical.byContradiction (fun he => Finset.disjoint_left.mp (show Disjoint _ _ from hQ.1 hi hj he) hw hv)

lemma reads (i : ι) (k : S.Choices) (hi : i∈Q) (h : A.flags=RG.flags (temp x) V) (F : Forest S.ratio) :
    Physical.Reads (K.X i) A (patch x V (K.seeds i)) F F V V k k := by
  refine ⟨fun _ _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => Iff.rfl,fun _ _ => (h ▸ Iff.rfl),?_,?_⟩
  · intro j hj
    refine ⟨fun hx=>?_,fun hz => (compare hQ i hi).1 hz⟩
    rw [← hQ.2.1] at hx
    obtain ⟨l,hl,hr⟩ := Finset.mem_biUnion.mp hx
    let y:=S.ratio.parent j.1
    have he1 : y∈K.X i := hj (Finset.mem_image_of_mem _ (Work.E01.base_touched j))
    have he2 : y∈K.X l := K.gate l (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨j,hr,Finset.mem_image_of_mem _ (Work.E01.base_touched j)⟩)))
    exact (far hQ hi he1 hl he2).symm ▸ hr
  intro j hj
  refine ⟨fun hx=>?_,fun hz => (compare hQ i hi).2.1 hz⟩
  rw [← hQ.2.1] at hx
  obtain ⟨l,hl,hr⟩ := Finset.mem_biUnion.mp hx
  have he1 : j.1 ∈ K.X i := hj (by simp [pinPos])
  have he2 : j.1 ∈ K.X l := K.gate l (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨j,hr,by simp [pinPos]⟩)))
  exact (far hQ hi he1 hl he2).symm ▸ hr

private lemma placeA (w : Site c) : w∈A.place ↔ ∃ i∈Q,w∈(K.seeds i).place := by
  rw [← hQ.2.1]; simp only [Stores.place,Cards.ports, Finset.mem_union, Finset.mem_biUnion]; grind

include M
lemma weather (i : ι) (hi : i∈Q) (h : A.flags=RG.flags (temp x) V)
    {w u : Site c} (hu : u∈K.X i) (ht : separation w u ≤ radiusB x) :
    w∈A.dome (10*radiusB x) ↔ w∈(patch x V (K.seeds i)).dome (10*radiusB x) := by
  unfold Stores.dome; rw [halo_spec,halo_spec]
  constructor
  · rintro ⟨l,hl,hl'⟩
    refine ⟨l,?_,hl'⟩
    obtain ⟨j,hj,hq⟩ := (placeA hQ l).mp hl
    suffices i=j by
      subst j; unfold Pressure.Stores.place at *; simp only [Finset.mem_union] at *
      rcases hq with hq|hq
      · exact Or.inl hq
      exact Or.inr (show l∈RG.flags (temp x) V from h ▸ (compare hQ i hi).2.2 hq)
    apply far hQ hi hu hj; apply (M j).loaded
    apply halo_spec.mpr
    exact ⟨l,hq,(separation_triangle l w u).trans ((Nat.add_le_add hl' ht).trans (by omega))⟩
  rintro ⟨l,hl,hl'⟩
  refine ⟨l,?_,hl'⟩
  rcases Finset.mem_union.mp hl with hl|hl
  · exact (placeA hQ l).mpr ⟨_,hi,Finset.mem_union_left _ hl⟩
  exact Finset.mem_union_right _ (h.symm ▸ hl)

lemma frost (i : ι) (hi : i∈Q) (h : A.flags=RG.flags (temp x) V) (hB : 120≤radiusB x) (e : F.Free)
    {w : Site c} (hw : w∈K.X i) (he : separation w (S.ratio.parent e.val.1) ≤ radiusB x/20) :
    chill A x F e ↔ chill (patch x V (K.seeds i)) x F e := by
  unfold chill
  refine or_congr (weather M hQ i hi h hw ((separation_comm ..).trans_le (he.trans (by omega))))
    (weather M hQ i hi h hw ?_)
  rw [separation_comm]; exact (separation_triangle _ (S.ratio.parent e.val.1) _).trans
    ((Nat.add_le_add he (Work.E03.parent_step ..)).trans (by omega))
end Localized

/-- Interior site list (symmetric endpoint check) for all Z coordinates,
necessary bustle of possible frozen arguments captured using whole X
regardless of interior. `sewn` will accommodate mean & synchronized
marginal panels AND the By test. `held` marks those *active* fine
arguments to be held in analytical FKer change; separate from F.Free
chill. -/
structure Badge (S : StepData c f) (x : ℝ) (X : Support c) where
  near : Support c
  held : Finset (Bond f)
  sewn : halo (20*radiusB x) near ⊆ X

namespace Badge
variable {X : Support c} (b : Badge S x X)

def dreams (F : Forest S.ratio) (A : Stores S) := Finset.univ.filter (fun e : F.Free => chill A x F e ∧
    S.ratio.parent e.val.1 ∈ X ∧ S.ratio.parent (e.val.1+Lattice.step e.val.2) ∈ X)
def tests (F : Forest S.ratio) (A : Stores S) := Finset.univ.filter (fun e : F.Free=> ¬chill A x F e ∧
    S.ratio.parent e.val.1∈b.near ∧ S.ratio.parent (e.val.1+Lattice.step e.val.2)∈b.near)

lemma contained_site : b.near ⊆ X := Finset.Subset.trans (halo_subset ..) b.sewn

def ribbon (F : Forest S.ratio) (A : Stores S) : Ribbon F X where
  frost := dreams (x:=x) (X:=X) F A
  breeze := b.tests F A
  ice i h := (Finset.mem_filter.mp h).2.2
  wind i h := let p:=(Finset.mem_filter.mp h).2.2; ⟨b.contained_site p.1,b.contained_site p.2⟩

lemma here (F : Forest S.ratio) (A : Stores S) : (b.ribbon F A).Placed x A where
  frost i h := (Finset.mem_filter.mp h).2.1
  breeze i h := (Finset.mem_filter.mp h).2.1

lemma bag (F : Forest S.ratio) (A : Stores S) (e : F.Free) (h : e∈(b.ribbon F A).breeze) :
    halo (20*radiusB x) {S.ratio.parent e.val.1} ⊆ X :=
  Finset.Subset.trans (Corona.halo_mono le_rfl (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp h).2.2.1)) b.sewn
end Badge

variable (M : ∀ i,Localized x K i) (B : ∀ i,Badge S x (K.X i)) (V : Config G c) (F : Forest S.ratio)
  (hB : 120≤radiusB x)

abbrev placed (j : ι) := (B j).ribbon F (patch x V (K.seeds j))

include M hB
lemma badge_charge (hQ : K.Makes A n Q) (i : Q) (h : A.flags=RG.flags (temp x) V) :
    (placed B V F i.val).Placed x A := by
  let R := B i.val; let w := placed B V F i.val
  have hh : w.Placed x (patch x V (K.seeds i)) := Badge.here ..
  have he (e : F.Free) (hp : S.ratio.parent e.val.1∈K.X i.val) := Localized.frost M hQ _ i.property h hB e hp
    (by rw [separation_self]; omega)
  refine ⟨fun e hx => (he e (w.ice e hx).1).mpr (hh.frost _ hx),fun e hx ht => (hh.breeze e hx) ((he e (w.wind e hx).1).mp ht)⟩

variable {T : Tube G S} {R : Rep G f} {W : ℝ} {D : Allocation G S x W} {L : Almanac T D R F}

def clears (hf : S.patch.Branches S.kernel G) (he : Next.SectorChange.span S.patch x ≤ radiusB x/50)
    (hr : ∀ A k, A.flags=RG.flags (temp x) V → L.C A V k=fog A F T x V k) : Roster L V K := by
  let w := placed B V F
  let a i := patch x V (K.seeds i)
  refine ⟨w,a,fun _ => rfl,fun i=>Badge.here ..,?_,fun A Q m hm hk i=> badge_charge M B V F hB hk i hm,?_,?_⟩ -- order
  · intro k l i hh; rw [hr _ _ rfl,hr _ _ rfl]
    refine Contact.synchronized hf hB _ _ hh (fun i _ _ => Iff.rfl) ?_
    intro t
    exact Finset.Subset.trans (Corona.halo_mono (by unfold Contact.billRadius; omega) (Finset.Subset.refl _))
      ((B i).bag F _ t.1.val t.1.property)
  · intro A k Q m ha h i; rw [hr _ _ ha,hr _ _ rfl]
    refine Contact.synchronized hf hB _ _ (show Tags.Synchronized (K.X i.val) k k from ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩) ?_ ?_
    · rintro ⟨j,z⟩ e he
      exact Localized.frost M h _ i.property ha hB e ((w i.val).wind j.val j.property).1 he
    intro t
    exact Finset.Subset.trans (Corona.halo_mono (by unfold Contact.billRadius; omega) (Finset.Subset.refl _)) ((B i.val).bag F _ t.1.val t.1.property)
  intro A k Q m ha h i j hg
  rw [hr _ _ ha]
  apply Aperture.insulated (show Disjoint (K.X i.val) (K.X j.val) from h.1 i.property j.property (mt Subtype.ext hg))
  exact fun t ht=>Finset.Subset.trans (Corona.halo_mono (by omega) (Finset.Subset.refl _)) ((B i.val).bag F _ t ht)
end Route
end YM.PhysicalNext.Dictionary
