import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import YM.Gauge.MatrixGroup
import YM.Lattice.Faces

/-!
We work directly on the same cubic `Site`/`Per` objects as both integrals,
so even when flag/path/Ward objects wind this tree and face count needs no
comparison with an open box. Numerator can use these faces *before* gauge
fixing (last-axis wrapping links at non-roots eliminated before top-slice
horizontal links, etc.). Four global positive link variables left, not an
untreated layer at a wall.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Torus
open Lattice  Function
open scoped BigOperators
variable {n : Side}

abbrev E (n : Side) := Edge (Site n)
def arrives (e : E n) : Site n := e.1+step e.2

/-- No nonzero coordinates *above* `a`. -/
def Flat (x : Site n) (a : Axis) := ∀ i : Axis, a < i → x i = 0

def Tree (e : E n) := Flat e.1 e.2 ∧ (e.1 e.2).val+1 < n.val
instance decidableTree : DecidablePred (Tree (n:=n)) := fun e => by unfold Tree Flat; infer_instance

def free (n : Side) : Finset (E n) := Finset.univ.filter fun e => ¬ Tree e
lemma memFree {e : E n} : e∈free n ↔ ¬ Tree e := by simp [free]

private lemma val_one (hn : 2 ≤ n.val) : (1 : Per n).val = 1 := (ZMod.val_eq_one hn _).2 rfl
lemma before (hn : 2 ≤ n.val) (x : Site n) (a : Axis) (ha : x a ≠ 0) :
    ((x-step a : Site n) a).val+1=(x a).val := by
  have hx : 1 ≤ (x a).val := ZMod.val_pos.mpr ha
  simp only [Pi.sub_apply,step_apply,↓reduceIte,ZMod.val_sub ((val_one hn).le.trans hx),val_one hn]
  omega
lemma ahead (hn : 2 ≤ n.val) (x : Site n) (a : Axis) (ha : (x a).val+1 < n.val) :
    ((x+step a : Site n) a).val=(x a).val+1 := by
  simp only [Pi.add_apply,step_apply,↓reduceIte,ZMod.val_add,val_one hn]
  exact Nat.mod_eq_of_lt ha
lemma wraps (hn : 2 ≤ n.val) (x : Site n) (a : Axis) : (x a).val+1=n.val ↔ (x+step a : Site n) a=0 := by
  rw [← ZMod.val_eq_zero]
  simp only [Pi.add_apply,step_apply,↓reduceIte,ZMod.val_add,val_one hn]
  constructor
  · intro h; rw [h,Nat.mod_self]
  intro h
  rcases lt_or_eq_of_le (show (x a).val+1 ≤ n.val from ZMod.val_lt _) with hh|hh
  · rw [Nat.mod_eq_of_lt hh] at h; omega
  exact hh

lemma arrives_flat {e : E n} (he : Tree e) : Flat (arrives e) e.2 := by
  intro i h; simp only [arrives,Pi.add_apply,step_apply,if_neg h.ne',add_zero]; exact he.1 i h
lemma enters (hn : 2 ≤ n.val) {e : E n} (he : Tree e) : (arrives e) e.2 ≠ 0 :=
  ZMod.val_pos.mp (by rw [arrives,ahead hn _ _ he.2]; omega)
lemma arrives_ne (hn : 2 ≤ n.val) {e : E n} (he : Tree e) : arrives e ≠ 0 := by
  intro h; apply enters hn he; rw [h]; rfl
lemma enters_once (hn : 2 ≤ n.val) {a b : E n} (ha : Tree a) (hb : Tree b) (h : arrives a = arrives b) : a=b := by
  have he : a.2=b.2 := by
    rcases lt_trichotomy a.2 b.2 with hi|hi|hi
    · have hv := arrives_flat ha _ hi; rw [h] at hv; exact (enters hn hb hv).elim
    · exact hi
    have hv := arrives_flat hb _ hi; rw [← h] at hv; exact (enters hn ha hv).elim
  apply Prod.ext ?_ he
  unfold arrives at h; rw [he] at h
  exact add_right_cancel h
lemma high {x : Site n} (hx : x≠0) : ∃ a : Axis, x a≠0 ∧ Flat x a := by
  let S := Finset.univ.filter fun a => x a≠0
  have H : S.Nonempty := by
    obtain ⟨a,ha⟩ := Function.ne_iff.mp hx
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  let y := S.max' H
  refine ⟨y,(Finset.mem_filter.mp (Finset.max'_mem _ H)).2,?_⟩
  intro i hi
  by_contra w
  exact (Finset.le_max' S _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,w⟩)).not_gt hi

lemma from_previous (hn : 2 ≤ n.val) (x : Site n) (hx : x ≠ 0) : ∃ e : E n, Tree e ∧ arrives e=x := by
  obtain ⟨a,ha,H⟩ := high hx
  refine ⟨(x-step a,a),⟨?_,?_⟩,sub_add_cancel ..⟩
  · intro i hi; simpa only [Pi.sub_apply,step_apply, if_neg hi.ne',sub_zero] using H i hi
  exact lt_of_eq_of_lt (before hn x a ha) (ZMod.val_lt _)

def length (x : Site n) := ∑ i, (x i).val
lemma grows (hn : 2 ≤ n.val) (x : Site n) (a : Axis) (h : (x a).val+1 < n.val) :
    length (x+step a)=length x+1 := by
  unfold length
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),ahead hn x a h,
    ← Finset.add_sum_erase _ (fun i => (x i).val) (Finset.mem_univ a),add_right_comm _ 1]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi; simp [Finset.ne_of_mem_erase hi]

lemma howmany (hn : 2 ≤ n.val) : (free n).card=3*Fintype.card (Site n)+1 := by
  let t := Finset.univ.filter (Tree (n:=n))
  have hi : Set.InjOn arrives (↑t : Set _) := fun x hx y hy =>
    enters_once hn (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have ht : t.image arrives = (Finset.univ : Finset (Site n)).erase 0 := by
    ext x; rw [Finset.mem_erase,Finset.mem_image]
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ⟨arrives_ne hn (Finset.mem_filter.mp ha).2,Finset.mem_univ _⟩
    rintro ⟨hx,-⟩; obtain ⟨e,he,h⟩ := from_previous hn x hx
    exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,h⟩
  have hs : t.card+1=Fintype.card (Site n) := by
    rw [← Finset.card_image_of_injOn hi,ht,Finset.card_erase_add_one (Finset.mem_univ _),Finset.card_univ]
  have hu : t.card+(free n).card=Fintype.card (Site n)*4 := by
    rw [show Fintype.card (Site n)*4 = Fintype.card (E n) by simp [E, Edge, Axis],← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not ..
  omega

def rim (a : Axis) : E n := (-step a,a)
def paid (n : Side) := free n \ Finset.univ.image rim
lemma rim_free (hn : 2 ≤ n.val) (a : Axis) : rim a ∈ free n := by
  rw [memFree]; intro h
  exact arrives_ne hn h (neg_add_cancel _)
lemma rim_count (hn : 2 ≤ n.val) : (paid n).card+4=(free n).card := by
  unfold paid
  let L := Finset.univ.image (rim (n:=n))
  have ht : L ⊆ free n := by rintro v hv; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv; exact rim_free hn _
  have hi : Injective (rim (n:=n)) := fun i j h => congr_arg Prod.snd h
  have hh : L.card=4 := by rw [Finset.card_image_of_injective _ hi]; simp [Axis]
  have he := Finset.card_sdiff_add_card_eq_card ht
  rw [hh] at he; exact he

def block (e : E n) : Finset Axis := insert e.2 (Finset.univ.filter fun a => e.1 a ≠ 0)
def last (e : E n) := (block e).max' (Finset.insert_nonempty ..)
private lemma memBlock {a} {e : E n} : a∈block e ↔ a=e.2 ∨ e.1 a ≠ 0 := by simp [block]
lemma bound_last (e : E n) : e.2 ≤ last e := Finset.le_max' (block e) _ (memBlock.mpr (.inl rfl))
lemma last_live (e : E n) : e.2≠last e → e.1 (last e)≠0 := by
  intro h
  exact (memBlock.mp (Finset.max'_mem (block e) _)).resolve_left (Ne.symm h)
lemma last_flat (e : E n) : Flat e.1 (last e) := by
  intro i hi; by_contra w
  exact (Finset.le_max' (block e) _ (memBlock.mpr (.inr w))).not_gt hi
lemma last_le (e : E n) (a : Axis) (ha : e.2 ≤ a) (hf : Flat e.1 a) : last e ≤ a := by
  by_contra! hn
  exact last_live e (ne_of_lt (ha.trans_lt hn)) (hf _ hn)

/-- Edges on a positive face. -/
def reads (p : Face (Per n)) : Finset (E n) :=
    let a := p.2.val.1
    let b := p.2.val.2
    { (p.1,a), (p.1+step a,b), (p.1+step b,a), (p.1,b) }

/-- Higher dimension first; then wrapping verticals before horizontal at that dimension;
then reverse height. We use a score on ALL edges, sort just paid/non-tree/non-rim. -/
def index (e : E n) : Axis ×ₗ (ℕ ×ₗ ℕ) := toLex (last e, toLex (if last e=e.2 then 1 else 0,length e.1))
private lemma less_aux {e f : E n} (h : last e < last f) : index e < index f :=
    Prod.Lex.toLex_lt_toLex.mpr (.inl h)
private lemma paid_not (e : E n) (h : e ∈ paid n) : ¬ Tree e := memFree.mp (Finset.mem_sdiff.mp h).1

section Horizontal

-- highest nonzero layer b above the axis of the horizontal. Use the vertical face to the preceding layer.
private lemma horizontal (hn : 2 ≤ n.val) (x : Site n) (a b : Axis) (he : a < b) (hp : last (x,a)=b) :
    ∃ p : Face (Per n), (x,a) ∈ reads p ∧
      ∀ u ∈ reads p, u∈ paid n → u ≠ (x,a) → index u < index (x,a) := by
  let y := x-step b
  have hx : y + step b=x := sub_add_cancel ..
  have ht : Flat x b := hp ▸ last_flat (x,a)
  have hm : x b≠0 := hp ▸ last_live (x,a) (show a≠last (x,a) by simpa only [hp] using he.ne)
  have hw : Flat y b := by intro i hi; unfold y; simp [hi.ne',ht _ hi]
  have hh : (y b).val+1 < n.val := lt_of_eq_of_lt (before hn x b hm) (ZMod.val_lt _)
  have hV : Tree (y+step a,b) := by
    constructor
    · intro i hi; simpa only [Pi.add_apply,step_apply, if_neg (he.trans hi).ne',add_zero] using hw _ hi
    change ((y+step a : Site n) b).val+1<n.val
    simpa [he.ne'] using hh
  let p : Face (Per n) := (y,⟨(a,b),he⟩)
  have H : reads p = {(y,a), (y+step a,b), (x,a), (y,b)} := by
    dsimp only [reads,p]; rw [hx]
  refine ⟨p,H ▸ (by simp),?_⟩
  intro u hu huv hux
  rw [H] at hu
  have hs := paid_not _ huv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with hu|hu|hu|hu <;> subst u
  · rcases lt_or_eq_of_le (last_le (y,a) b he.le hw) with hi|hi
    · exact less_aux (hi.trans_eq hp.symm)
    apply Prod.Lex.toLex_lt_toLex.mpr; right
    refine ⟨hi.trans hp.symm,Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨?_,?_⟩)⟩
    · simp only [hi,hp]
    change length y < length x
    rw [← hx, grows hn y b hh]
    omega
  · exact (hs hV).elim
  · exact (hux rfl).elim
  exact (hs ⟨hw,hh⟩).elim
end Horizontal

private lemma vertical (hn : 2 ≤ n.val) (x : Site n) (a : Axis) (hp : (x,a) ∈ paid n) (he : last (x,a) = a) :
    ∃ p : Face (Per n), (x,a) ∈ reads p ∧
      ∀ u ∈ reads p, u∈paid n → u ≠ (x,a) → index u < index (x,a) := by
  have hh : Flat x a := he ▸ last_flat (x,a)
  have hw : (x a).val+1 = n.val := by
    rcases lt_or_eq_of_le (show (x a).val+1 ≤ n.val from ZMod.val_lt _) with h|h
    · exact (paid_not _ hp ⟨hh,h⟩).elim
    exact h
  let z := x+step a
  have hza : z a=0 := (wraps hn x a).mp hw
  have hz : z ≠ 0 := by
    intro h
    have hu : x = - step a := eq_neg_of_add_eq_zero_left h
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,by rw [hu]; rfl⟩)
  obtain ⟨b,hb,hy⟩ := high hz
  have hba : b < a := by
    rcases lt_trichotomy b a with h|h|h
    · exact h
    · exact (hb (h ▸ hza)).elim
    exact (hb (by simp [z,h.ne',hh _ h])).elim
  have Hx : x b=z b := by simp [z,hba.ne]
  let y := x-step b
  have ht : y+step b=x := sub_add_cancel x _
  have HA : Flat y a := by intro i hi; simp [y,(hba.trans hi).ne',hh _ hi]
  have hl : (y b).val+1 < n.val := lt_of_eq_of_lt (before hn x b (by rwa [Hx])) (ZMod.val_lt _)
  have hv : last (y,a)=a := le_antisymm (last_le (y,a) _ le_rfl HA) (bound_last (y,a))
  have hy' : y+step a=z-step b := sub_add_eq_add_sub ..
  have hT : Tree (y+step a,b) := by
    rw [hy']; constructor
    · intro i hi; simpa only [Pi.sub_apply,step_apply,if_neg hi.ne',sub_zero] using hy i hi
    exact lt_of_eq_of_lt (before hn z b hb) (ZMod.val_lt (z b))
  let p : Face (Per n) := (y,⟨(b,a),hba⟩)
  have H : reads p = {(y,b),(x,a),(y+step a,b),(y,a)} := by dsimp only [reads,p]; rw [ht]
  refine ⟨p,H ▸ (by simp),?_⟩
  intro u hu huv hux
  rw [H] at hu
  have hs := paid_not _ huv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with hu|hu|hu|hu <;> subst u
  · rcases lt_or_eq_of_le (last_le (y,b) _ hba.le HA) with hi|hi
    · exact less_aux (hi.trans_eq he.symm)
    apply Prod.Lex.toLex_lt_toLex.mpr; right
    refine ⟨hi.trans he.symm, Prod.Lex.toLex_lt_toLex.mpr (.inl ?_)⟩
    simp [hi,he,hba.ne']
  · exact (hux rfl).elim
  · exact (hs hT).elim
  apply Prod.Lex.toLex_lt_toLex.mpr; right
  refine ⟨hv.trans he.symm,Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨?_,?_⟩)⟩
  · simp [hv,he]
  change length y < length x
  rw [← ht,grows hn y b hl]
  omega

theorem eliminates (hn : 2 ≤ n.val) (e : E n) (H : e∈ paid n) :
    ∃ p : Face (Per n), e ∈ reads p ∧ ∀ u ∈ reads p, u∈paid n → u≠e → index u < index e := by
  obtain ⟨x,a⟩ := e
  rcases lt_or_eq_of_le (bound_last (x,a)) with h|h
  · exact horizontal hn x a _ h rfl
  exact vertical hn x a H h.symm
end YM.Push.Corrected.Torus
