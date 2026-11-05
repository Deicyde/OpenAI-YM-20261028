import YM.Ovens.Coffee
import YM.Progress.DIRECTED_RECIPE.Padding

/-!
# A dictionary chosen independently of the population

A `Pipes` for *this* torus, covering every shape. Flags are still
read as in the specification; extra tests may be placed *inside*
payloads. Raw `X : Pipes` are not required to have trivial tests. We will
store those X as well. There are even *designated* zero addresses (all
shapes) at every step, not just unused numbers depending on where in the
parameter range one starts to mark. Include both transported active slots and
designated zeros in the Moves permutations. Permutations need only be
supplied at each parameter value as in Valid; the dictionary itself will not
vary. No claim that paths never wrap or flag neighborhoods are small.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Ovens Wilson Lattice MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

section Rooms
variable {α : Type*}
/-- Two independent series of labels for each address shape. -/
abbrev Slots (α : Type*) := α × (ℕ ⊕ ℕ)

def rows (α : Type) [Countable α] [Nonempty α] : ℕ ≃ Slots α :=
  letI := Classical.choice (nonempty_denumerable (Slots α))
  (Denumerable.eqv _).symm

/-- `j` records a label of the old alphabet even when its support agrees
with that of another label. Never drop decisions. -/
def use (E : ℕ ≃ Slots α) (f : ℕ → α) : ℕ ↪ ℕ where
  toFun j := E.symm (f j, Sum.inl j)
  inj' _ _ h := Sum.inl_injective (congr_arg Prod.snd (E.symm.injective h))

lemma book (E : ℕ ≃ Slots α) (f : ℕ → α) (j : ℕ) : E (use E f j) = (f j, .inl j) :=
  Equiv.apply_symm_apply E _

/-- Infinitely many specific slots, left dormant. -/
def spare (E : ℕ ≃ Slots α) : α × ℕ ↪ ℕ where
  toFun j := E.symm (j.1, Sum.inr j.2)
  inj' _ _ h := Prod.ext (congr_arg (Prod.fst : Slots α → α) (E.symm.injective h))
    (Sum.inr_injective (congr_arg Prod.snd (E.symm.injective h)))

lemma recorded (E : ℕ ≃ Slots α) (x : α) (j : ℕ) : E (spare E (x,j)) = (x, .inr j) :=
  Equiv.apply_symm_apply E _

lemma distinct (E : ℕ ≃ Slots α) (f : ℕ → α) (x : α) (j : ℕ) : spare E (x,j) ∉ range (use E f) := by
  rintro ⟨k,h⟩
  have ht := congr_arg E h
  rw [recorded,book] at ht
  simp at ht

/-- Extend an old Moves permutation to the WHOLE dictionary. Active labels
for a shape are sent according to their original permutation. Thus whether
an active label was a real old address is preserved once the footprint law
is in force. This also acts separately on the infinite reserves. -/
def rearrange (E : ℕ ≃ Slots α) (g : Equiv.Perm α) (p : Equiv.Perm ℕ) : Equiv.Perm ℕ :=
  (E.trans (Equiv.prodCongr g (Equiv.sumCongr p (Equiv.refl ℕ)))).trans E.symm

lemma stocked (E : ℕ ≃ Slots α) (g : Equiv.Perm α) (p : Equiv.Perm ℕ) (i : ℕ) :
    E (rearrange E g p i) = (g (E i).1, Sum.map p id (E i).2) := by
  simp only [rearrange, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply]
  rfl

lemma move_stock (E : ℕ ≃ Slots α) (g : Equiv.Perm α) (p : Equiv.Perm ℕ) (f : ℕ → α)
    (h : ∀ i, g (f i) = f (p i)) (j : ℕ) : rearrange E g p (use E f j) = use E f (p j) := by
  apply E.injective
  simp [stocked,book,h]



lemma unused {e : ℕ ↪ ℕ} {M p : Equiv.Perm ℕ} (hm : ∀ i, M (e i) = e (p i)) {j : ℕ}
    (h : j ∉ range e) : M j ∉ range e := by
  rintro ⟨i,hi⟩
  obtain ⟨i, rfl⟩ := p.surjective i
  rw [← hm] at hi
  exact h ⟨i, M.injective hi⟩
end Rooms

section Shape
variable {G : Gauge} {n : Side}

structure Foot (n : Side) where
  support : Support n
  inventory : Support n
  ne : inventory.Nonempty
  sub : inventory ⊆ support

def readFoot (A : ForcedAddress G n) : Foot n := ⟨A.support,A.inventory,A.inventory_ne,A.inventory_sup⟩

/-- Every extra test is already enforced by nonzero K (or by nonzero
appointment of a new coefficient, keeping *that* appointment's certificate).
Index by all shapes. Can't index by all possible predicate functions. -/
def bareFoot (G : Gauge) (A : Foot n) : ForcedAddress G n :=
  ⟨A.support,A.inventory,A.ne,A.sub,fun _ => True⟩

abbrev Zone (n : Side) := { Y : Support n // Y.Nonempty }

lemma foot_ext {A B : Foot n} (hs : A.support = B.support) (hi : A.inventory = B.inventory) : A=B := by
  cases A; cases B; congr
lemma reg_ext {A B : RegularAddress n} (hs : A.site=B.site) (hi : A.support=B.support) : A=B := by
  cases A; cases B; congr

lemma foot_countable (n : Side) : Countable (Foot n) :=
  Function.Injective.countable (show Function.Injective (fun x : Foot n => (x.support,x.inventory)) from
    fun _ _ h => foot_ext (congr_arg Prod.fst h) (congr_arg Prod.snd h))
lemma reg_countable (n : Side) : Countable (RegularAddress n) :=
  Function.Injective.countable (show Function.Injective (fun x : RegularAddress n => (x.site,x.support)) from
    fun _ _ h => reg_ext (congr_arg Prod.fst h) (congr_arg Prod.snd h))

def regularKeys (n : Side) : ℕ ≃ Slots (RegularAddress n) :=
  @rows _ (reg_countable n) ⟨⟨0,{0},Finset.mem_singleton_self _⟩⟩

def hardKeys (n : Side) : ℕ ≃ Slots (Foot n) :=
  @rows _ (foot_countable n) ⟨⟨{0},{0},Finset.singleton_nonempty _, Finset.Subset.refl _⟩⟩

def softKeys (n : Side) : ℕ ≃ Slots (Zone n) :=
  @rows _ inferInstance ⟨⟨{0},Finset.singleton_nonempty _⟩⟩
end Shape

section Box
variable {G : Gauge} {n : Side}

/-- Chosen even on all small tori. Never depends on the parameter, level,
history or any estimate. -/
def drawer (G : Gauge) (n : Side) : Pipes G n where
  reg i := (regularKeys n i).1
  kernel i := bareFoot G (hardKeys n i).1
  softer i := (softKeys n i).1.val
  sites i := (softKeys n i).1.property

namespace Rack
variable (X : Pipes G n)

def upE : ℕ ↪ ℕ := use (regularKeys n) X.reg

def upK : ℕ ↪ ℕ := use (hardKeys n) fun i => readFoot (X.kernel i)

def upS : ℕ ↪ ℕ := use (softKeys n) fun i => (⟨X.softer i, X.sites i⟩ : Zone n)

lemma reg_up (i : ℕ) : (drawer G n).reg (upE X i) = X.reg i := by simp [drawer, upE, book]
lemma hard_up (i : ℕ) : (drawer G n).kernel (upK X i) = bareFoot G (readFoot (X.kernel i)) := by
  simp [drawer, upK, book]
lemma soft_up (i : ℕ) : (drawer G n).softer (upS X i) = X.softer i := by simp [drawer, upS, book]

def widen (d : Tap G n) : Tap G n where
  regular := stuff (upE X) d.regular
  forced := stuff (upK X) d.forced
  logarithm := stuff (upS X) d.logarithm

lemma preserves (d : Tap G n) (P : BudgetPoint) :
    Readdress P (upE X) (upK X) (X.pours d) ((drawer G n).pours (widen X d)) := by
  refine ⟨reg_up X,fun i => ?_,fun i => ?_,fun _ => stuffed ..,fun _ => stuffed ..,
    fun _ h => blank _ _ h, fun _ h => blank _ _ h,fun i U h => ?_⟩
  · unfold Pipes.pours
    simp only [hard_up,bareFoot,readFoot]
  · unfold Pipes.pours
    simp only [hard_up,bareFoot,readFoot]
  dsimp only [Pipes.pours]
  rw [hard_up]
  exact ⟨h.1,trivial⟩
end Rack
end Box

section Perm
variable {n : Side} (e : Equiv.Perm (Site n))

def relocate (A : RegularAddress n) : RegularAddress n :=
  ⟨e A.site,A.support.image e, Finset.mem_image_of_mem _ A.anchor⟩

lemma relocate_inverse : LeftInverse (relocate e.symm) (relocate e) := fun A => by
  refine reg_ext ?_ ?_ <;> simp [relocate, Finset.image_image]

def regMap : Equiv.Perm (RegularAddress n) :=
  ⟨relocate e, relocate e.symm, relocate_inverse e, relocate_inverse e.symm⟩

def stepOn (A : Foot n) : Foot n :=
  ⟨A.support.image e,A.inventory.image e, A.ne.image _, Finset.image_mono _ A.sub⟩

lemma stepOn_inverse : LeftInverse (stepOn e.symm) (stepOn e) := fun A => by
  refine foot_ext ?_ ?_ <;> simp [stepOn, Finset.image_image]

def hardMap : Equiv.Perm (Foot n) :=
  ⟨stepOn e, stepOn e.symm, stepOn_inverse e, stepOn_inverse e.symm⟩

def rezone (A : Zone n) : Zone n := ⟨A.val.image e,A.property.image _⟩
lemma rezone_inverse : LeftInverse (rezone e.symm) (rezone e) := fun A => Subtype.ext (by
  simp [rezone, Finset.image_image])

def softMap : Equiv.Perm (Zone n) :=
  ⟨rezone e,rezone e.symm, rezone_inverse e, rezone_inverse e.symm⟩
end Perm

section Lift
open Rack
variable {G : Gauge} {n : Side} {X : Pipes G n}

def destination (s : Signed) (b : Site n) : Equiv.Perm (Site n) := s.actEquiv.toEquiv.trans (Equiv.addRight b)

/-- Applies *any* incoming permutation supplied by Moves. The proof uses
that carrier and location footprints transform. Result is a permutation for
the NEW population, with its own kernel eligibility at all entries. -/
def on_shelves {d : Tap G n} {s : Signed} {b : Site n} (M : (X.pours d).Moves s b) :
    ((drawer G n).pours (widen X d)).Moves s b := by
  let z := destination s b
  let e := rearrange (regularKeys n) (regMap z) M.ep
  let k := rearrange (hardKeys n) (hardMap z) M.kp
  have hr (i : ℕ) : (drawer G n).reg (e i) = regMap z ((drawer G n).reg i) :=
    congr_arg Prod.fst (stocked (regularKeys n) (regMap z) M.ep i)
  have he (i : ℕ) := congr_arg Prod.fst (stocked (hardKeys n) (hardMap z) M.kp i)
  have h1 (i : ℕ) : e (upE X i) = upE X (M.ep i) := move_stock _ _ _ X.reg
    (fun i => reg_ext (M.reg_site _).symm (M.reg_support _).symm) i
  have h2 (i : ℕ) : k (upK X i) = upK X (M.kp i) := move_stock _ _ _ (fun i => readFoot (X.kernel i))
    (fun i => foot_ext (M.forced_support _).symm (M.forced_inventory _).symm) i
  refine ⟨e, k, fun i => congr_arg RegularAddress.site (hr i), fun i => congr_arg RegularAddress.support (hr i),
    fun i => congr_arg Foot.support (he i), fun i => congr_arg Foot.inventory (he i), fun _ _ => Iff.rfl, ?_, ?_⟩
  · intro i U
    change stuff (upE X) d.regular (e i) U = stuff (upE X) d.regular i _
    by_cases H : i ∈ range (upE X)
    · obtain ⟨i,rfl⟩ := H
      rw [h1,stuffed,stuffed]; exact M.valuesE ..
    rw [blank _ _ (unused h1 H), blank _ _ H]; rfl
  intro i U
  change stuff (upK X) d.forced (k i) U = stuff (upK X) d.forced i _
  by_cases H : i ∈ range (upK X)
  · obtain ⟨i,rfl⟩ := H
    rw [h2,stuffed,stuffed]; exact M.valuesK ..
  rw [blank _ _ (unused h2 H), blank _ _ H]; rfl

lemma carries_log {d : Tap G n} (s : Signed) (b : Site n) (p : Equiv.Perm ℕ)
    (h : ∀ i, X.softer (p i) = (X.softer i).image (affine s b))
    (hd : ∀ U i, d.logarithm (p i) U = d.logarithm i (pull s b U)) :
    let q := rearrange (softKeys n) (softMap (destination s b)) p
    (∀ i,(drawer G n).softer (q i) = ((drawer G n).softer i).image (affine s b)) ∧
    ∀ U i, (widen X d).logarithm (q i) U = (widen X d).logarithm i (pull s b U) := by
  intro q
  have he (i : ℕ) : q (upS X i) = upS X (p i) := move_stock _ _ _ (fun i => ⟨X.softer i, X.sites i⟩)
    (fun j => Subtype.ext (h j).symm) i
  refine ⟨fun i => congr_arg Subtype.val (congr_arg Prod.fst (stocked (softKeys n) (softMap (destination s b)) p i)),?_⟩
  intro U i
  dsimp only [widen]
  by_cases H : i ∈ range (upS X)
  · obtain ⟨j,rfl⟩ := H
    rw [he,stuffed,stuffed,hd]
  rw [blank _ _ (unused he H), blank _ _ H]; rfl
end Lift
end YM.Progress.DirectedRecipe
