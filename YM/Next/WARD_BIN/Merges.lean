import YM.Next.WARD_BIN.Gas

/-!
# Components identity (exact polynomial, pointwise on the compact links)

Proven **without** interpreting distinct copies as powers of a scalar.
Apply over the nilpotent algebra for simultaneous discrepancies. Works for
any pairwise disjoint nonempty source footprints. Nonempty primary inventories.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Gas
open Lattice Wilson RG Finset Ac Relation Function
open scoped BigOperators Matrix.Norms.Frobenius Classical
variable {n : Side} {V : Type*} [DecidableEq V]

abbrev Letters (V : Type*) (n : Side) := Sum V (Shape n)

def hull (Y : V → Support n) : Letters V n → Support n := Sum.elim Y wall

def thread (Y : V → Support n) (v : V) (i : Shape n) := (Y v ∩ wall i).Nonempty

variable (Y : V → Support n) {T : Finset (Letters V n)}

omit [DecidableEq V] in
lemma seam {v : V} {i : Shape n} (hv : Sum.inl v ∈ T) (hi : Sum.inr i ∈ T) :
    thread Y v i ↔ bonds (hull Y) T (Sum.inl v) (Sum.inr i) :=
 ⟨by rintro ⟨x,h⟩; exact ⟨hv,hi,x,(mem_inter.mp h).1,(mem_inter.mp h).2⟩,
  by rintro ⟨a,b,x,h,H⟩; exact ⟨x,mem_inter.mpr ⟨h,H⟩⟩⟩

/-- Positive-address components, vacuum components included. Local even when
there's only one marker. -/
abbrev Camp (Y : V → Support n) :=
  {T : Finset (Letters V n) // Spark (hull Y) T ∧ T.toRight.Nonempty ∧ (T.toRight:Set (Shape n)).PairwiseDisjoint wall}

abbrev markers (p : Camp Y) := p.val.toLeft
abbrev olds (p : Camp Y) := p.val.toRight
omit [DecidableEq V] in
lemma roots (p : Camp Y) : (olds Y p).Nonempty := p.property.2.1
omit [DecidableEq V] in
lemma active (p : Camp Y) : Spark (hull Y) p.val := p.property.1
omit [DecidableEq V] in
lemma distinct (p : Camp Y) : (olds Y p : Set (Shape n)).PairwiseDisjoint wall := p.property.2.2
omit [DecidableEq V] in
lemma splitCamp (p : Camp Y) : (markers Y p).disjSum (olds Y p)=p.val := toLeft_disjSum_toRight

def spans (p : Camp Y) : Shape n :=
  ⟨(p.val.biUnion (hull Y), (olds Y p).biUnion inv), by
    obtain ⟨i,hi⟩ := roots Y p; obtain ⟨x,hx⟩ := present i
    refine ⟨⟨x,mem_biUnion.mpr ⟨i,hi,hx⟩⟩, fun y he => ?_⟩
    obtain ⟨q,hq,hh⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨Sum.inr q, mem_toRight.mp hq, grows q hh⟩⟩

omit [DecidableEq V] in
lemma has_letter (p : Camp Y) {x} (hx : x∈p.val) : hull Y x ⊆ wall (spans Y p) :=
  fun _ hk => mem_biUnion.mpr ⟨x,hx,hk⟩
omit [DecidableEq V] in
lemma has_wall (p : Camp Y) {i} (hi : i∈ olds Y p) : wall i ⊆ wall (spans Y p) :=
  has_letter Y p (mem_toRight.mp hi)
omit [DecidableEq V] in
lemma has_marker (p : Camp Y) {v} (hv : v∈markers Y p) : Y v ⊆ wall (spans Y p) :=
  has_letter Y p (mem_toLeft.mp hv)

private lemma contact {α : Type*} (S : α → Support n) {C : Finset α} {a b}
    (h : chain S C b a) (hn : b ≠ a) : ∃ x, Ac.bonds S C x a ∧ x ≠ a := by
  induction h with
  | refl => contradiction
  | @tail x y h hy I =>
    by_cases ht : x=y
    · subst x; exact I hn
    exact ⟨_,hy,ht⟩

omit [DecidableEq V] in
lemma inner_stem (p : Camp Y) (h : Pairwise (Disjoint on Y)) {v} (hv : v∈ markers Y p) :
    ∃ q∈olds Y p, thread Y v q := by
  obtain ⟨i,hi⟩ := roots Y p
  obtain ⟨x,he,hx⟩ := contact (hull Y) ((active _ p).2 _ (mem_toRight.mp hi) _ (mem_toLeft.mp hv)) (by simp)
  obtain ⟨hw,hb,k,hj,ht⟩ := he
  cases x with
  | inl y => exact False.elim (disjoint_left.mp (h fun H => hx (congr_arg _ H)) hj ht)
  | inr x => exact ⟨x,mem_toRight.mpr hw,k, mem_inter.mpr ⟨ht,hj⟩⟩

omit [DecidableEq V] in
lemma outer_stem (p : Camp Y) (hx : (markers Y p).Nonempty) {q} (hq : q∈olds Y p) :
    ∃ v∈markers Y p, thread Y v q := by
  obtain ⟨i,hi⟩ := hx
  obtain ⟨x,he,hx⟩ := contact (hull Y) ((active _ p).2 _ (mem_toLeft.mp hi) _ (mem_toRight.mp hq)) (by simp)
  cases x with
  | inr x =>
    obtain ⟨ha,hb,k,hj,ht⟩ := he
    exact False.elim (disjoint_left.mp ((distinct Y p) (mem_toRight.mpr ha) hq fun H => hx (congr_arg _ H)) hj ht)
  | inl y => exact ⟨y,mem_toLeft.mpr he.1,(seam Y he.1 he.2.1).mpr he⟩

omit [DecidableEq V] in
/-- One marker inside any ambient V. -/
lemma one_marker (v : V) (D : Finset (Shape n)) (h : D.Nonempty) (hh : (D:Set (Shape n)).PairwiseDisjoint wall) :
    Spark (hull Y) (({v}: Finset V).disjSum D) ↔ ∀ i∈D,thread Y v i := by
  constructor
  · intro hp q hq
    let p : Camp Y := ⟨_,hp,by rw [toRight_disjSum]; exact h,by rw [toRight_disjSum]; exact hh⟩
    simpa only [markers,olds,p,toLeft_disjSum,mem_singleton,exists_eq_left] using
      outer_stem Y p (by simp [p,markers]) (show q∈olds Y p by simpa [p,olds] using! hq)
  intro he
  let T := ({v}:Finset V).disjSum D
  have hv : Sum.inl v ∈ T := by simp [T]
  have hz : ∀ i∈T,chain (hull Y) T (Sum.inl v) i := by
    intro i hij; cases i with
    | inl z => rw [mem_singleton.mp (inl_mem_disjSum.mp hij)]; exact .refl
    | inr z => exact .single ((seam Y hv hij).mp (he z (inr_mem_disjSum.mp hij)))
  exact ⟨⟨Sum.inl v,hv⟩,fun i hi j hj => ReflTransGen.trans (Ac.swaps _ (hz i hi)) (hz j hj)⟩

def just (i : Shape n) : Camp Y :=
  ⟨{Sum.inr i},by
    have ht : ( {Sum.inr i} : Finset (Letters V n)).toRight = {i} := by ext; simp
    rw [ht]; refine ⟨⟨singleton_nonempty _,fun x hx y hy => ?_⟩,singleton_nonempty _,?_⟩
    · rw [mem_singleton.mp hx,mem_singleton.mp hy]; exact .refl
    simp [Set.PairwiseDisjoint]⟩
omit [DecidableEq V] in
@[simp] lemma old_just (i : Shape n) : olds Y (just Y i)={i} := by
  ext; simp [olds,just]
omit [DecidableEq V] in
@[simp] lemma spans_just (i : Shape n) : spans Y (just Y i)=i := by
  apply Subtype.ext; dsimp only [spans]; rw [old_just]; simp [just,hull,wall,inv]


omit [DecidableEq V] in
lemma no_marker {p : Camp Y} (hx : markers Y p=∅) : p=just Y (spans Y p) := by
  obtain ⟨i,hi⟩ := roots Y p
  have he : p=just Y i := by
    apply Subtype.ext
    ext x; rw [show (just Y i).val={Sum.inr i} from rfl]
    cases x with
    | inl u =>
      rw [← mem_toLeft]; change u∈markers Y p ↔ _
      simp [hx]
    | inr j =>
      rw [mem_singleton, Sum.inr.injEq]
      constructor
      · intro hj; by_contra hn
        obtain ⟨x,H,hh⟩ := contact (hull Y) ((active Y p).2 _ hj _ (mem_toRight.mp hi)) fun he => hn (Sum.inr_injective he)
        obtain ⟨ha,hb,k,hj,ht⟩ := H
        cases x with
        | inr y => exact disjoint_left.mp ((distinct Y p) (mem_toRight.mpr ha) hi fun H => hh (congr_arg Sum.inr H)) hj ht
        | inl v => exact notMem_empty v (hx ▸ (show v∈markers Y p from mem_toLeft.mpr ha))
      exact fun H => H.symm ▸ mem_toRight.mp hi
  simp [he]

/-! Coherent selections = non-orphan left vertices after disjoint charge. -/

abbrev Score (V : Type*) (n : Side) := Finset V × Finset (Shape n)
variable {M : Support n}



def notes (C : Finset (Camp Y)) : Score V n := (C.biUnion (markers Y),C.biUnion (olds Y))
omit [DecidableEq V] in
lemma named {C : Finset (Camp Y)} (hx : Holds (spans Y) M C) (hh : ∀ v, (Y v).Nonempty) :
    (C:Set (Camp Y)).PairwiseDisjoint (markers Y) := by
  intro p hp q hq hn; apply disjoint_left.mpr; intro x he hx'
  obtain ⟨z,hz⟩ := hh x
  exact disjoint_left.mp (hx.disj hp hq hn) (has_marker Y p he hz) (has_marker Y q hx' hz)

omit [DecidableEq V] in
lemma distinct_charges {C : Finset (Camp Y)} (hx : Holds (spans Y) M C) :
    (C:Set (Camp Y)).PairwiseDisjoint (olds Y) := by
  intro p hp q hq hn; apply disjoint_left.mpr; intro x he hx'
  obtain ⟨z,hz⟩ := mentions x
  exact disjoint_left.mp (hx.disj hp hq hn) (has_wall Y p he hz) (has_wall Y q hx' hz)
lemma area {D : Finset (Camp Y)} : D.biUnion (inv ∘ spans Y) = (notes Y D).2.biUnion (inv ∘ id) := by
  rw [notes, biUnion_biUnion]; rfl











section Complete
variable {R : Type*} [Fintype V] [CommSemiring R]
variable (f : V → R) (K : Shape n→R)

def chance (b : Score V n) := (∏ i∈b.1,f i)*∏ i∈b.2,K i

def foot (M : Support n) (p : Camp Y) : R :=
  if markers Y p=∅ then K (spans Y p)
  else if wall (spans Y p)∩M=inv (spans Y p) then chance f K (markers Y p,olds Y p) else 0

def merge (M : Support n) : Shape n → R := fun q => ∑ p : Camp Y, if spans Y p=q then foot Y f K M p else 0

omit [Fintype V] in
lemma parts_weight {D : Finset (Camp Y)} (hx : Holds (spans Y) M D) (hh : ∀ v, (Y v).Nonempty) :
    (∏ p∈D,foot Y f K M p)=chance f K (notes Y D) := by
  have he (p : Camp Y) (hp : p∈D) : foot Y f K M p=(∏ i∈markers Y p,f i)*∏ i∈olds Y p,K i := by
    unfold foot; rw [if_pos (hx.owns hp)]; split_ifs with h
    · rw [h]
      have hw := no_marker Y h
      nth_rw 2 [hw]
      rw [old_just]; simp
    rfl
  unfold chance
  change (∏ p∈D,_)=(∏ i∈ D.biUnion (markers Y), _) * (∏ i∈D.biUnion (olds Y),_)
  rw [prod_biUnion (named Y hx hh),prod_biUnion (distinct_charges Y hx), ← prod_mul_distrib]; exact prod_congr rfl he


end Complete
end YM.WardBin.Gas
