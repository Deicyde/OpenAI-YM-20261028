import YM.Extra.MULTISOURCE_TRAJECTORIES.Localization
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
/-!
# Exact deletion consistency for insertion signals and localized fragments

Removing species / adding exclusions. Use the same blocking measure,
partition into windows, selected position, and degrees. The inverse pass is
*naturally* restricted (although its triangular algorithm has an array-size
dependent iteration bound). No likelihood factor or label recalibrated on a
subarray.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Marker Finset Function RG Wilson Overlay Lattice
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {V V' : Type} [DecidableEq V] [DecidableEq V'] {R : Census V} {R' : Census V'}

structure Names (R : Census V) (R' : Census V') where
  e : V ↪ V'
  visible (s : R.Mode) : s.val.image e ∈ R'.choices

namespace Names
variable (u : Names R R')

def share (s : R.Mode) : R'.Mode := ⟨_,u.visible s⟩
lemma inj : Injective u.share := fun _ _ h => Subtype.ext (image_injective u.e.injective (congrArg Subtype.val h))
@[simp] lemma quiet : u.share R.quiet = R'.quiet := Subtype.ext (image_empty _)
@[simp] lemma fire (i : V) : u.share (R.fire i)=R'.fire (u.e i) := Subtype.ext (image_singleton ..)

lemma merges (x y z : R.Mode) : Poly.merges (u.share x) (u.share y) (u.share z) ↔ Poly.merges x y z := by
  unfold Poly.merges share
  rw [disjoint_image u.e.injective, ← image_union, (image_injective u.e.injective).eq_iff]

lemma inherits {s : R.Mode} {t : Finset V'} (h : t ⊆ (u.share s).val) : ∃ a : R.Mode,t=(u.share a).val := by
  let T := s.val.filter (fun i => u.e i∈t)
  refine ⟨⟨T,R.down s.property T (filter_subset ..)⟩,(Finset.ext fun i => ?_)⟩
  constructor
  · intro hi; obtain ⟨a,ha,rfl⟩ := mem_image.mp (h hi); exact mem_image_of_mem _ (mem_filter.mpr ⟨ha,hi⟩)
  intro hi; obtain ⟨a,ha,rfl⟩ := mem_image.mp hi; exact (mem_filter.mp ha).2

lemma part_shared (a b : Poly R') (z : R.Mode) : (a*b).part (u.share z) = ((Poly.inject fun s => a.part (u.share s)) *
    (Poly.inject fun s => b.part (u.share s))).part z := by
  let S := univ.image u.share
  have hm {x y : R'.Mode} (h : Poly.merges x y (u.share z)) : x∈S := by
    obtain ⟨x',hx⟩ := u.inherits (h.2 ▸ subset_union_left : x.val ⊆ (u.share z).val)
    exact mem_image.mpr ⟨x',mem_univ _,Subtype.ext hx.symm⟩
  rw [Poly.part_mul,Poly.part_mul,← sum_subset (subset_univ S) ?_,sum_image u.inj.injOn]
  · apply sum_congr rfl; intro i _
    rw [← sum_subset (subset_univ S) (fun j _ hj => if_neg (fun he => hj (hm ((Poly.wind ..).mp he)))),sum_image u.inj.injOn]
    exact sum_congr rfl fun j _ => by simp [u.merges,Poly.part,Poly.inject]
  exact fun i _ hi => sum_eq_zero fun j _ => if_neg (fun he => hi (hm he))

def restriction : Poly R' →+* Poly R where
  toFun a := Poly.inject fun s => a.part (u.share s)
  map_one' := Poly.ext fun i => by
    change Poly.part 1 (u.share i) = Poly.part 1 i
    simp only [Poly.one_part, ← u.quiet,u.inj.eq_iff]
  map_mul' a b := Poly.ext fun i => u.part_shared a b i
  map_zero' := rfl
  map_add' _ _ := rfl

lemma smul (a : Poly R') (b : ℂ) : u.restriction (b • a) = b • u.restriction a := rfl

variable [Fintype V] [Fintype V']
lemma pass_restrict {a : Poly R'} (h : a.part R'.quiet=0) : u.restriction (Poly.pass a) = Poly.pass (u.restriction a) := by
  unfold Poly.pass; rw [map_sum]; simp_rw [u.smul, map_pow]
  symm; refine sum_subset (range_mono (by have := Fintype.card_le_of_injective _ u.e.injective; omega)) ?_
  intro i _ hi; rw [Poly.stops _ _ _ (by simp only [mem_range,not_lt] at hi; omega),smul_zero]
  simpa [restriction,Poly.inject,Poly.part,quiet] using h

lemma connected_restrict {a : Poly R'} (h : a.part R'.quiet=1) : u.restriction (connected a) = connected (u.restriction a) := by
  have he := connected_quiet h
  have hh : (u.restriction (connected a)).part R.quiet=0 := by change (connected a).part (u.share R.quiet)=0; simpa using he
  have hv : (u.restriction a).part R.quiet=1 := by change a.part (u.share R.quiet)=1; simpa using h
  apply pass_inj hh (connected_quiet hv)
  rw [← u.pass_restrict he, pass_connected h, pass_connected hv]
end Names

variable {G : Gauge} {H : History G} {N p : ℕ}
namespace Insertions
variable (u : Names R R') (A : Insertions H V' N p)

def subset : Insertions H V N p := ⟨A.load ∘ u.e, A.field ∘ u.e, fun _ => A.smooth _⟩

lemma total_shared (s : R.Mode) (j : ℕ) (hj : j ≤ N) : A.total (u.share s) j = (A.subset u).total s j := by
  have he (a : ℝ) : Ride.bump a (u.share s) A.load = Ride.bump a s (A.subset u).load := Finset.prod_image u.e.injective.injOn
  induction hj using Nat.decreasingInduction with
  | self =>
    funext x; rw [total_top,total_top, source,source, he]
    exact congrArg (_ * ·) (prod_image (f:=fun i => A.field i x) u.e.injective.injOn)
  | of_succ j hj ih => rw [total_step _ _ _ hj,total_step _ _ _ hj,ih,he]

variable [Fintype V] [Fintype V']
lemma cumulant_shared (s : R.Mode) (j : ℕ) (hj : j ≤ N) : A.cumulant j (u.share s) = (A.subset u).cumulant j s := by
  funext x
  have he := congrArg (Poly.part · s) (u.connected_restrict (A.ratios_quiet hj x))
  refine he.trans ?_
  rw [show u.restriction (A.ratios R' j x) = (A.subset u).ratios R j x by ext a; exact congrArg (· * _) (congrFun (A.total_shared u a j hj) x)]
  rfl
end Insertions

namespace Names
variable (u : Names R R') {n : Side} (W : Windows n)
abbrev Full (R : Census V) := Hot R × W.Piece

def look (t : Hot R) : Hot R' := ⟨u.share t.val,t.property.image _⟩
def fragment (t : Full W R) : Full W R' := (u.look t.1,t.2)
lemma fragment_injective : Injective (u.fragment W) := by
  intro a b h; exact Prod.ext (Subtype.ext (u.inj (congrArg (fun i => i.1.val) h))) (show (u.fragment W a).2 = (u.fragment W b).2 from congrArg Prod.snd h)
end Names

namespace Insertions
variable [Fintype V] [Fintype V'] (u : Names R R') (A : Insertions H V' N p) {j : ℕ} (W : Windows (H.S.side j p))
    (atSite : V' → Site (H.S.side j p)) (core : V' → Support (H.S.side j p))

lemma region_shared (q : Hot R × W.Piece) : (A.fragments R' W atSite core).region (u.fragment W q) =
    ((A.subset u).fragments R W (atSite ∘ u.e) (core ∘ u.e)).region q := by
  simp only [fragments,Names.fragment,Names.look,Names.share, image_biUnion,comp_def]
lemma H_shared (hj : j≤N) (q : Hot R × W.Piece) : (A.fragments R' W atSite core).H (u.fragment W q) =
    ((A.subset u).fragments R W (atSite ∘ u.e) (core ∘ u.e)).H q := by
  simp only [fragments,Names.fragment,Names.look, A.cumulant_shared u _ j hj]
  simp only [Names.share,image_biUnion,comp_def]
end Insertions
end YM.Extra.Trajectories
