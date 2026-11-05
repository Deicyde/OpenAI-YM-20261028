import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
/-!
# Retain the very gas packets in each allowed restriction

Including zero histories on published fragment keys and all old letters. Extra
padding in the Nat enumerations has no meaning. The host address in P *is*
shared. Full unions include test atoms even if values cancel; cannot introduce
a new old-K predicate by enlarging the array.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Marker Lattice Wilson RG Overlay Function Finset
open scoped Classical
variable {G : Gauge} {n : Side} {P : Rep G n} {V V' : Type} [DecidableEq V] [DecidableEq V'] {R : Census V} {R' : Census V'}
    {α β : Type*}

structure Sub {u : Names R R'} (X : Layers P R α) (Y : Layers P R' β) where
  letter : α ↪ β
  tag i : Y.tag (letter i)=u.share (X.tag i)
  full (s : β) (a : R.Mode) : (Y.tag s).val ⊆ (u.share a).val → s∈Set.range letter
  wall i : Y.region (letter i)=X.region i
  values i : Y.H (letter i)=X.H i

namespace Sub
open Layers
variable {u : Names R R'} {X : Layers P R α} {Y : Layers P R' β} (h : Sub (u:=u) X Y)

def rise : Letter α ↪ Letter β := (Embedding.refl ℕ).sumMap h.letter
lemma area (i : Letter α) : Y.area (h.rise i)=X.area i := by cases i with
  | inl i => rfl
  | inr i => exact h.wall i
lemma weight (i : Letter α) (U : Config G n) : Y.weight U (h.rise i)=X.weight U i := by cases i with
  | inl i => rfl
  | inr i => change Y.residual _ _ = X.residual _ _; simp only [Layers.residual,h.wall,h.values]
lemma lefts (s : Finset (Letter α)) : (s.map h.rise).toLeft = s.toLeft := by ext; simp [rise,Embedding.sumMap]
lemma rights (s : Finset (Letter α)) : (s.map h.rise).toRight = s.toRight.map h.letter := by ext; simp [rise,Embedding.sumMap]


lemma image_union (s : Finset α) : (s.map h.letter).biUnion (fun i => (Y.tag i).val) =
    (s.biUnion (fun i => (X.tag i).val)).image u.e := by
  ext x; simp only [mem_image, mem_biUnion,mem_map,exists_exists_and_eq_and,h.tag,Names.share]; aesop

lemma chain (s : Finset (Letter α)) {i j : Letter α} : Ac.chain Y.area (s.map h.rise) (h.rise i) (h.rise j) ↔ Ac.chain X.area s i j := by
  have he (i j : Letter α) : Ac.bonds X.area s i j ↔ Ac.bonds Y.area (s.map h.rise) (h.rise i) (h.rise j) := by
    simp only [Ac.bonds,Ac.meets,h.area,mem_map']
  refine ⟨?_,Relation.ReflTransGen.lift _ (fun _ _ => (he _ _).mp) i j⟩
  suffices ∀ k, Ac.chain Y.area (s.map h.rise) (h.rise i) k → ∀ j,k=h.rise j → Ac.chain X.area s i j from
    fun hh => this _ hh _ rfl
  intro k hk; induction hk with
  | refl => intro j hh; rw [h.rise.injective hh]; exact .refl
  | tail _ hb ih =>
    intro j hh; obtain ⟨a,_,rfl⟩ := mem_map.mp hb.1
    exact .tail (ih a rfl) ((he _ j).mpr (hh ▸ hb))

lemma spark (s : Finset (Letter α)) : Ac.Spark Y.area (s.map h.rise) ↔ Ac.Spark X.area s := by
  unfold Ac.Spark; simp only [forall_mem_map,h.chain,map_nonempty]

lemma pairwise (s : Finset α) : ((s.map h.letter : Finset β) : Set β).PairwiseDisjoint (fun i => (Y.tag i).val) ↔
    (s : Set α).PairwiseDisjoint (fun i => (X.tag i).val) := by
  unfold Set.PairwiseDisjoint Set.Pairwise onFun
  simp [h.tag,Names.share,Finset.disjoint_image u.e.injective]

lemma solid {s : Finset (Letter α)} (hs : X.Solid s) : Y.Solid (s.map h.rise) where
  old := (h.lefts s).symm ▸ hs.old
  mark := (h.rights s).symm ▸ hs.mark.map
  join := (h.spark s).mpr hs.join
  sep := (h.lefts s).symm ▸ hs.sep
  fits := by
    rw [Fits,h.rights,h.pairwise,h.image_union]; exact ⟨hs.fits.1,u.visible ⟨_,hs.fits.2⟩⟩

def send (c : X.Component) : Y.Component := ⟨_,h.solid c.property⟩



lemma stamp (c : X.Component) : Y.stamp (h.send c)=u.share (X.stamp c) := by
  exact Subtype.ext (by simp [Layers.stamp,send,h.rights,unionTag,h.image_union,Names.share])



end Sub

namespace Insertions
variable [Fintype V] [Fintype V'] {H : History G} {N p j : ℕ}

def sublayers (u : Names R R') (A : Insertions H V' N p) (W : Windows (H.S.side j p))
    (atSite : V' → Site (H.S.side j p)) (core : V' → Support (H.S.side j p)) (hj : j ≤ N) :
    Sub (u:=u) ((A.subset u).fragments R W (atSite ∘ u.e) (core ∘ u.e)) (A.fragments R' W atSite core) where
  letter := ⟨_,u.fragment_injective W⟩
  wall _ := A.region_shared ..
  tag _ := rfl
  values _ := A.H_shared u W atSite core hj _
  full := by
    intro q a he
    obtain ⟨b,hb⟩ := u.inherits he
    have h := hb ▸ q.1.property
    change ((↑b : Finset V).image u.e).Nonempty at h
    obtain ⟨s,hs⟩ := h
    obtain ⟨s,hs',rfl⟩ := mem_image.mp hs
    exact ⟨(⟨b,s,hs'⟩,q.2),Prod.ext (Subtype.ext (Subtype.ext hb.symm)) rfl⟩
end Insertions
end YM.Extra.Trajectories
