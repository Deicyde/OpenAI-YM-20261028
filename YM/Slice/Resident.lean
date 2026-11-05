import YM.Slice.Sequence


/-!
# Recover actual cylinder from one Brick

Place at width native L (L=joints+1). Need strict time fit. Action along time
PROVED for literal translates, not retuning. Reflected orientation produces
correct starred Brick. No assumption about the support fitting as N varies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice.Time
open Lattice Wilson Cells MeasureTheory Measure Filter Function Set
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {a : Axis} {G : Gauge} {m : ℕ} {n : Side}

def offset (a : Axis) (t : Per n) : Site n := t • Lattice.step a
@[simp] theorem atOffset (a) (t : Per n) : offset a t a = t := by simp [offset]
@[simp] theorem offOffset (a) (t : Per n) {b} (hb : b≠a) : offset a t b=0 := by simp [offset,hb]

theorem plane_offset (t r : Per n) (x : Row a n) : plane a t x+offset a r=plane a (t+r) x := by
  ext i; by_cases he : i=a <;> simp [he,plane]

theorem crops (t r : Per n) (x : Circle G a n) : crop a t m (fun z => x (z+r))=crop a (t+r) m x := by
  unfold crop; simp [add_assoc,add_comm r]

theorem marched (t : Per n) (U : Config G n) : leaves a (translate (offset a t) U)= fun z => leaves a U (z+t) := by
  funext z; apply Prod.ext
  · funext i; simp [leaves,translate,plane_offset]
  funext i; simp [leaves,translate,plane_offset]

lemma translation (D : Brick a G n) (s t : Per n) (U : Config G n) : D.value s (translate (offset a t) U) = D.value (s+t) U := by
  rw [Brick.value,marched,crops];rfl

lemma flippedCrop (C : Cut n) (x : Sequence m G C.pos n) (t : Per n) (h : level C t=t+((m+1:ℕ):Per n))
    (F : Config G n) (H : crop C.pos t m (leaves C.pos F)=x) : crop C.pos t m (leaves C.pos (C.pullC G F)) = reverseF x := by
  subst x
  have ht : F=chain C.pos (leaves C.pos F) := ((slice C.pos).left_inv _).symm
  set M := leaves C.pos F
  have hx : leaves C.pos (C.pullC G F) = opposite C M := by
    conv_lhs => rw [ht,mirrors]
    exact (slice C.pos).apply_symm_apply _
  have hs (i : ℕ) : level C (t+i) = t+(↑(m+1:ℕ):Per n) -i := by
    unfold level; rw [← h]; unfold level; abel
  rw [hx]; apply Prod.ext
  · ext1 i
    have hd : i.val<m+2 := i.isLt
    simp [crop,opposite,reverseF, hs,Nat.cast_sub (by omega : i.val ≤ m+1), add_sub_assoc]
  ext1 i
  have hh := i.isLt
  simp [crop,opposite,reverseF, hs,Nat.cast_sub (by omega : i.val ≤ m),add_sub_assoc]; ring_nf

lemma flipValue (C : Cut n) (k) (h : C.kind=.site)
    (B : Brick C.pos G n) (p : Per n) (ht : C.baseLine=p+(k:ℕ))
    (hr : B.width=k+k) (F : Config G n) : star (B.value p (C.pullC G F)) = B.reflect.value p F := by
  have he : level C p = p+((B.joints+1:ℕ):Per n) := by
    change _ = p+((B.width:ℕ):Per n); rw [level,h,ht,hr, Kind.shift];push_cast;ring
  unfold Brick.value
  rw [flippedCrop C _ p he F rfl]; rfl

/- Fill sequence with arbitrary outside value. Need period>width and no use of its last
thread in strict applications. -/
def fill (a : Axis) (b : Per n) (S : Sequence m G a n) : Circle G a n := fun i =>
  ((if h : (i-b).val < m+2 then S.1 ⟨_,h⟩ else 1), (if h : (i-b).val < m+1 then S.2 ⟨_,h⟩ else 1))

@[fun_prop] lemma fill_cont (b : Per n) : Continuous (fill (m := m) (G := G) a b) := by
  unfold fill; apply continuous_pi
  intro i; split_ifs <;> fun_prop

def extend (β : Config G n → ℂ) (a : Axis) (b : Per n) (m : ℕ) := β ∘ (chain a) ∘ (fill (m := m) a b)

lemma selects (k : Config G n → ℂ) (h : Continuous k) (b : Per n) (_ : m+1 < n.val)
    (H : LocalOn {x : Site n | (x a-b).val < m+1} k) :
    ∃ B : Brick a G n, B.width=m+1 ∧ k=B.value b := by
  let B : Brick a G n := ⟨m, extend k a b m, h.comp ((chain_cont _).comp (fill_cont _))⟩
  refine ⟨B,rfl, funext fun U => H U _ ?_⟩
  intro i hp _
  change (i.1 a-b).val < m+1 at hp
  have he := Nat.lt_succ_of_lt hp
  change U i = chain a (fill a b (crop a b m (leaves a U))) i
  have ht : fill a b (crop a b m (leaves a U)) (i.1 a) = leaves a U (i.1 a) := by
    unfold fill
    rw [dif_pos he, dif_pos hp]; apply Prod.ext <;> simp [crop,Per,add_comm b]
  conv_lhs => rw [show U=chain a (leaves a U) from ((slice a).left_inv _).symm]
  simp only [chain,ht]
end YM.Slice.Time
