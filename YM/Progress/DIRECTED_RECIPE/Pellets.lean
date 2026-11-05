import YM.Progress.DIRECTED_RECIPE.Digest

/-!
# Even after fusion: explicit embedding, unused slots at each shape

At every configuration including with flags. Never merge extra histories just
because their inventory is in common. All terms off the image are identically
zero. This in particular explains why we can require permanent unused labels
in the selected recipe in addition to the integration laws. A nonzero value
must satisfy the original eligibility too; keep these receipts when attempting
marked transports. Cost to apply markers and add their predicates not included
here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Ovens Ovens.Pipes Wilson Lattice
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {X : Pipes G n} (d : Tap G n) (P : BudgetPoint)

def folio (G : Gauge) (n : Side) : ℕ ≃ (drawer G n).Pellet := ((drawer G n).encoding).some

namespace Rack
lemma lefts_up (A : Finset Label) (X : Pipes G n) : lefts (A.map (up X)) = (lefts A).map (upK X) := by
  ext x; constructor
  · intro hx
    obtain ⟨i,hi,H⟩ := Finset.mem_map.mp (Finset.mem_toLeft.mp (show x ∈ (A.map (up X)).toLeft from hx))
    cases i with
    | inl j => exact Finset.mem_map.mpr ⟨_, Finset.mem_toLeft.mpr hi, Sum.inl.inj H⟩
    | inr j => cases H
  intro h; obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
  exact Finset.mem_toLeft.mpr (Finset.mem_map.mpr ⟨_, Finset.mem_toLeft.mp hi, rfl⟩)

lemma sparks_up (A : Finset Label) (X : Pipes G n) :
    Ac.Spark (drawer G n).patch (A.map (up X)) ↔ Ac.Spark X.patch A := by
  let e := up X
  let p := Ac.bonds X.patch A
  let q := Ac.bonds (drawer G n).patch (A.map e)
  have he : LeftInverse (invFun e) e := leftInverse_invFun e.injective
  have hb (i j) : q (e i) (e j) ↔ p i j := by
    simp [q,p,e,Ac.bonds,Ac.meets,same_patch]
  constructor <;> rintro ⟨hv,h⟩ <;> refine ⟨?_,?_⟩
  · exact Finset.map_nonempty.mp hv
  · intro i hi j hj
    change Relation.ReflTransGen p i j
    rw [← he i, ← he j]
    refine Relation.ReflTransGen.lift (r:=q) (p:=p) (invFun e) (fun a b hs => ?_)
      _ _ (h _ (Finset.mem_map.mpr ⟨i,hi,rfl⟩) _ (Finset.mem_map.mpr ⟨j,hj,rfl⟩))
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hs.1
    obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp hs.2.1
    change p (invFun e (e a)) (invFun e (e b))
    rw [he,he]; exact (hb a b).1 hs
  · exact hv.map
  intro i hi j hj
  obtain ⟨i,hia,rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨j,hja,rfl⟩ := Finset.mem_map.mp hj
  exact Relation.ReflTransGen.lift (r:=p) (p:=q) e (fun a b => (hb a b).2) i j (h i hia j hja)

lemma contains_up (A : Finset Label) (X : Pipes G n) :
    (drawer G n).contains (A.map (up X)) ↔ X.contains A := by
  simp only [contains,lefts_up,sparks_up,Finset.map_nonempty]
  rw [paired _ (Q:=fun i j => Disjoint (X.kernel i).support (X.kernel j).support) (fun a b => by
    simp only [hard_up, bareFoot, readFoot])]

def send (X : Pipes G n) : X.Pellet ↪ (drawer G n).Pellet where
  toFun A := ⟨A.val.map (up X), (contains_up _ _).mpr A.property⟩
  inj' _ _ h := Subtype.ext (Finset.map_injective (up X) (Subtype.ext_iff.mp h))

/-- Necessary as well as sufficient. -/
lemma outside (A : (drawer G n).Pellet) (X : Pipes G n) :
    A ∉ range (send X) ↔ ∃ i∈ A.val, i ∉ range (up X) := by
  constructor
  · intro h; contrapose! h
    obtain ⟨a, ha⟩ := finsets_full (up X) _ h
    exact ⟨⟨a,(contains_up a X).mp (ha.symm ▸ A.property)⟩, Subtype.ext ha⟩
  rintro ⟨i,hi,hi'⟩ ⟨v,rfl⟩
  obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hi
  exact hi' ⟨j,hj⟩

variable (F : ℕ ≃ X.Pellet)

def nameUp : ℕ ↪ ℕ := (F.toEmbedding.trans (send X)).trans (folio G n).symm.toEmbedding

lemma master (i : ℕ) : folio G n (nameUp F i) = send X (F i) := Equiv.apply_symm_apply ..

lemma addr_sup (i : ℕ) :
    (addr (folio G n) P (nameUp F i)).support = (addr F P i).support := by
  change (drawer G n).skin _ = X.skin _
  rw [master]
  exact mapped_biUnion (up X) (same_patch X) _

lemma addr_inv (i : ℕ) :
    (addr (folio G n) P (nameUp F i)).inventory = (addr F P i).inventory := by
  change (drawer G n).plot _ = X.plot _
  rw [master]; unfold plot
  change (lefts ((F i).val.map (up X))).biUnion _ = _
  rw [lefts_up]; exact mapped_biUnion _ (fun i => by
    simp [hard_up, bareFoot,readFoot]) _

lemma addr_perm (i : ℕ) (U : Config G n) (h : (addr F P i).eligible P.threshold U) :
    (addr (folio G n) P (nameUp F i)).eligible P.threshold U := by
  refine ⟨by rw [addr_sup,addr_inv]; exact h.1,?_⟩
  change condition ..
  unfold condition; rw [master]
  intro j hj
  change j∈lefts ((F i).val.map (up X)) at hj
  rw [lefts_up] at hj
  obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
  rw [hard_up]
  exact ⟨(h.2 k hk).1,trivial⟩
end Rack

open Rack
variable {d P}

lemma lift_fused {δ b : ℝ} (hg : X.Digests d P δ b) (F : ℕ ≃ X.Pellet) :
    Readdress P (upE X) (nameUp F) (fused F P d) (fused (folio G n) P (widen X d)) := by
  refine ⟨reg_up X,addr_sup P F, addr_inv P F,fun _ => stuffed ..,?_, fun _ he => blank _ _ he, ?_,
    addr_perm P F⟩
  · intro i
    funext U
    change solid _ _ _ _ _ = solid _ _ _ _ _
    let a := addr F P i
    by_cases h : a.eligible P.threshold U
    · rw [solid,if_pos (addr_perm P F i U h),solid,if_pos h,master]
      change (∏ j∈(F i).val.map (up X), _) = _
      rw [Finset.prod_map]
      simp_rw [same_atom]
    have hr : solid F P d i U = 0 := if_neg (c := (addr F P i).eligible P.threshold U) h
    rw [hr]
    unfold solid
    split
    · next ht =>
        rw [master]
        change (∏ j∈ (F i).val.map (up X), _) = _
        rw [Finset.prod_map]; simp_rw [same_atom]
        by_contra hn
        apply h
        have hv := ht.1
        rw [addr_sup,addr_inv] at hv
        refine ⟨hv,fun j hj => hg.stamp.forced.permit j U ?_⟩
        intro hh
        exact hn (Finset.prod_eq_zero (Finset.mem_toLeft.mp hj) hh)
    rfl
  intro j hj
  funext U
  change solid _ _ _ _ _ = 0
  rw [solid]
  split
  · have he : folio G n j ∉ range (send X) := by
      rintro ⟨a,ha⟩; obtain ⟨i,rfl⟩ := F.surjective a
      exact hj ⟨i,(folio G n).injective ((master F i).trans ha)⟩
    obtain ⟨i,hi,hi'⟩ := (outside _ _).mp he
    exact Finset.prod_eq_zero hi (zero_atom _ _ _ _ hi')
  rfl

section Reserved
/-- A single hard kernel label occurs as a pellet, even if its numerical
coefficient is zero. -/
def singleLeft (X : Pipes G n) : ℕ ↪ X.Pellet where
  toFun i := ⟨{Sum.inl i}, by
    refine ⟨⟨i,by simp [lefts]⟩,⟨Finset.singleton_nonempty _, ?_⟩,?_⟩
    · simp only [Finset.mem_singleton]; rintro a rfl b rfl
      exact .refl
    simp [lefts,Set.Pairwise]⟩
  inj' i j h := Sum.inl_injective (Finset.singleton_inj.mp (show ({.inl i}:Finset Label) = {.inl j} from Subtype.ext_iff.mp h))

def blankRow (n : Side) : RegularAddress n × ℕ ↪ ℕ := spare (regularKeys n)

/-- Infinitely many designated dormant Pellet slots FOR EACH support and
nonempty inventory in it. -/
def sleepK (G : Gauge) (n : Side) : Foot n × ℕ ↪ ℕ :=
  (((spare (hardKeys n)).trans (singleLeft (drawer G n))).trans (folio G n).symm.toEmbedding)

lemma sleep_id (x : Foot n) (j : ℕ) :
    folio G n (sleepK G n (x,j)) = singleLeft (drawer G n) (spare (hardKeys n) (x,j)) :=
  Equiv.apply_symm_apply ..

lemma sleeping_out (X : Pipes G n) (F : ℕ ≃ X.Pellet) (x : Foot n) (j : ℕ) :
    sleepK G n (x,j) ∉ range (nameUp F) := by
  rintro ⟨i,hi⟩
  have h := (master F i).symm.trans ((congr_arg _ hi).trans (sleep_id x j))
  have he : Sum.inl (spare (hardKeys n) (x,j))∈ (send X (F i)).val := by
    rw [h]; exact Finset.mem_singleton_self _
  obtain ⟨k,_,H⟩ := Finset.mem_map.mp he
  cases k with
  | inr k => cases H
  | inl k => exact distinct _ (fun i => readFoot (X.kernel i)) x j ⟨k,Sum.inl.inj H⟩

variable (P)
lemma base_exact (x : Foot n) (j : ℕ) : (drawer G n).kernel (spare (hardKeys n) (x,j)) = bareFoot G x := by
  simp only [drawer,recorded]

lemma tile_exact (x : Foot n) (j : ℕ) :
    readFoot (addr (folio G n) P (sleepK G n (x,j))) = x := by
  refine foot_ext ?_ ?_
  · simp only [readFoot, addr, skin, sleep_id]
    change Finset.biUnion {Sum.inl _} _ = _
    rw [Finset.singleton_biUnion]; simp only [patch, Sum.elim_inl, base_exact,bareFoot]
  simp only [readFoot, addr, plot, sleep_id]
  change Finset.biUnion (lefts {Sum.inl _}) _ = _
  ext a; simp [lefts,base_exact,bareFoot]

lemma tile_test (x : Foot n) (j : ℕ) (U : Config G n) :
    (addr (folio G n) P (sleepK G n (x,j))).extraTest U ↔ x.support ∩ flags P.threshold U = x.inventory := by
  change condition .. ↔ _
  unfold condition; rw [sleep_id]; change (∀ i∈lefts {Sum.inl _}, _) ↔ _
  simp [lefts,base_exact,bareFoot,ForcedAddress.eligible]



/-- Space still available at every fitted representation. -/
structure HasSlots (A : Activities G n) : Prop where
  reg : A.reg = (drawer G n).reg
  forced : A.forced = addr (folio G n) P
  regular i : A.E (blankRow n i) = 0
  forced_zero i : A.K (sleepK G n i) = 0

variable {P}
lemma never_spent {δ b} (hg : X.Digests d P δ b) :
    HasSlots P (fused (folio G n) P (widen X d)) := by
  have he := lift_fused hg X.encoding.some
  exact ⟨rfl,rfl, fun i => he.restE _ (distinct _ _ i.1 i.2),
    fun i => he.restK _ (sleeping_out X _ i.1 i.2)⟩
end Reserved
end YM.Progress.DirectedRecipe
