import YM.Bid.Phase

/-!
# Actual stencil transfers for alpha-product tests at RankWidths. No need
joint Gram powers proof inside bids -- expose topology & limiting procedure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Set Filter Function MeasureTheory OS OS.Ground Org Org.Phase Spec Table Word Analysis Extraction Retain Cells Wilson
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal
variable {G : Gauge} {C : Family G} {F : Filter (ℕ×ℕ)} {S : Table C.book} {V : Chamber S timeAxis}

/-- One fixed episode, each word on comparison grid k. Distinct & generic
within words (other words may occupy same points). Polynomials allow constants.
The coefficients of linear combination may be independent of mesh N here.
-/
structure Scene (C : Family G) (F : Filter (ℕ×ℕ)) (k : ℕ) where
  num : ℕ
  factor : Fin num→ℂ
  image (i : Fin num) : ℕ
  seats (i : Fin num) (j : Fin (image i)) : Lattice.Cover
  gen (i : Fin num) : Order.grid C k (seats i)∈generic _
  weight (i : Fin num) : Fin (image i) → ℕ
  point (i : Fin num) (j : Fin (image i)) : C.label (weight i j)
  current (i : Fin num) (j : Fin (image i)) (N p : ℕ) : C.label (weight i j)
  views i j : Tendsto (fun t:ℕ×ℕ => current i j t.1 t.2) F (𝓝 (point i j))

namespace Scene
variable {k b : ℕ} (E : Scene C F k)

def word (i : Fin E.num) : C.book.Word := realize (fun j => ⟨_,E.point i j⟩) (Order.grid C k (E.seats i))
def cluster (A : Spread V) : A.algebra := ∑ i,E.factor i • M A (E.word i) ((realized _ _).2 (generic_conf _ (E.gen i)))

def cuts (N p) (u : Lattice.Cover) (v : Config G (C.side N p)) := ∑ i, E.factor i * ∏ j,
    C.O N p (d:=E.weight i j) (E.current i j N p) (location C.S k N p (E.seats i j+u)) v

/-- offset, in **k-sites**, count *2*t*i. all four axes even. -/
def step (C : Family G) {b k : ℕ} (h : b≤k) (t j : ℕ) : Lattice.Cover := fun _ => ↑((C.S.toDepth h 0).count.val*(2*t*j))
-- 2*m consecutive; even positions use ordinary bar (after ground proof).
def twice (h : b≤k) (t m N p) (v : Config G (C.side N p)) := ∏ j : Fin (2*m),
    if j.val%2=0 then star (E.cuts N p (step C h t j.val) v) else E.cuts N p (step C h t j.val) v

def flick (h : b≤k) (t m : ℕ) (i : Fin (2*m) → Fin E.num) := (List.ofFn fun j : Fin (2*m) =>
    let w := E.word (i j)
    carry (if j.val%2=0 then Word.conjugate w else w) (C.S.gridPoint k (step C h t j.val))).flatten

def price (m : ℕ) (i : Fin (2*m) → Fin E.num) := ∏ j : Fin (2*m), if j.val%2=0 then star (E.factor (i j)) else E.factor (i j)

def fromCut (h : b≤ k) (t m N p : ℕ) := moment (C.beta N p) (E.twice h t m N p)
def wanted (h : b≤k) (t m : ℕ) (S : Table C.book) := ∑ i,E.price m i * S.expect (E.flick h t m i)
end Scene


end YM.Trace.Verse
