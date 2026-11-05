import YM.Bid.Phase

/-!
# Actual stencil transfers for alpha-product tests at RankWidths. No need
joint Gram powers proof inside bids -- expose topology & limiting procedure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Set Filter Function MeasureTheory OS OS.Ground Org Org.Phase Spec Table Word Analysis Extraction Retain Cells Wilson
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff ENNReal
variable {G : Gauge} {C : Family G} {F : Order} {S : Table C.book} {V : Chamber S timeAxis}

/-- One fixed episode, each word on comparison grid k. Distinct & generic
within words (other words may occupy same points). Polynomials allow constants.
The coefficients of linear combination may be independent of mesh N here.
-/
structure Episode (C : Family G) (F : Order) (k : ℕ) where
  num : ℕ
  factor : Fin num→ℂ
  image (i : Fin num) : ℕ
  seats (i : Fin num) (j : Fin (image i)) : Lattice.Cover
  gen (i : Fin num) : Order.grid C k (seats i)∈generic _
  weight (i : Fin num) : Fin (image i) → ℕ
  point (i : Fin num) (j : Fin (image i)) : C.label (weight i j)
  current (i : Fin num) (j : Fin (image i)) (N p : ℕ) : C.label (weight i j)
  views i j : F.limits (fun _ => True) (current i j) (point i j)

namespace Episode
variable {k b : ℕ} (E : Episode C F k)

def word (i : Fin E.num) : C.book.Word := realize (fun j => ⟨_,E.point i j⟩) (Order.grid C k (E.seats i))
def cluster (A : Spread V) : A.algebra := ∑ i,E.factor i • M A (E.word i) ((realized _ _).2 (generic_conf _ (E.gen i)))

def cuts (N p) (u : Lattice.Cover) (v : Config G (C.side N p)) := ∑ i, E.factor i * ∏ j,
    C.O N p (d:=E.weight i j) (E.current i j N p) (location C.S k N p (E.seats i j+u)) v

def Sold (b : ℕ) (g : ℝ) : Prop := ∀ ε : ℝ, 0<ε → F.late fun N p => ∃ h : b≤N,
    let A := center C.S p h 0
    Interior (A.chamber 0) (E.cuts N p 0) ∧ A.rootTest (C.beta N p) (E.cuts N p 0) ≤ g+ε

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
end Episode

/-- geometer/budget user -/
def B15 : Prop := ∀ {G : Gauge} {C : Family G} {F S} (_ : Seed C F S) {k b} (e : b≤k) (E : Episode C F k) (g : ℝ),
    0 ≤ g → E.Sold b g → ∀ (t : ℕ), 0 < t → ∀ (n : ℕ) (ε : ℝ),0 < ε → F.late fun N p => ‖E.fromCut e t n N p‖≤ (g+ε)^(2*n)

/-- limit of tested pairs (or whole trains), before φ. -/
def B16 : Prop := ∀ {G : Gauge} {C : Family G} {F S} (_ : Seed C F S) {k b} (e : b≤ k) (E : Episode C F k), ∀ n,
    ∀ᶠ t in atTop, Tendsto (fun i : ℕ × ℕ => E.fromCut e t n i.1 i.2) F.fuse (𝓝 (E.wanted e t n S))

def B17 : Prop := ∀ {G : Gauge} {C : Family G} {F S} (_ : Seed C F S) (V : Chamber S timeAxis) (A : Spread V),
    Theme V A → Steady V → Phase.reflects (C:=C) V A → ∀ b k (p : b ≤ k) (E : Episode C F k) n,
      Tendsto (fun t => E.wanted p t n S) atTop (𝓝 (inner ℂ V.omega0 (((star (E.cluster A)*E.cluster A)^n:A.algebra).val V.omega0)))

-- build ep
structure Sends {V : Chamber S timeAxis} (A : Spread V) (F : Order) (b k : ℕ) (c : ℝ) (v : A.algebra) : Prop where
  germ : ∃ E : Episode C F k, E.cluster A=v ∧ E.Sold b c

def B18 : Prop := ∀ {G : Gauge} {C : Family G} {F S} (_ : Seed C F S) (V : Chamber S timeAxis) (A : Spread V),
    Theme V A → ∀ d (X : Columns C S d) (Q : X.Trials) (K : Columns.Trials.Valid F Q),
    (∀ k i c j, Sends A F (Q.width k) (Q.depth k) (Q.gap k) (Retain.Δone Q A k i c j)) ∧
    (∀ k i c j x (h : j<x), Sends A F (Q.width k) (Q.depth k) (Q.gap k) (Retain.Δtwo Q K A k i c j x h))

-- Sanity check scaling for B15-B17 consumer.
private lemma fees (h : B15) (B : B16) (L : B17) (s : Seed C F S) (A : Spread V) (ht : Theme V A) (he : Steady V) (hp : Phase.reflects (C:=C) V A)
    {b k} {v : A.algebra} {c : ℝ} (hc : 0 ≤ c) (hb : b ≤ k) (p : Sends A F b k c v) : Retain.Tall A v c := by
  obtain ⟨E,hR,H⟩ := p.germ
  subst v; intro n
  let X := (inner ℂ V.omega0 (((star (E.cluster A)*E.cluster A)^n:A.algebra).val V.omega0)).re
  have hv ε (hε : 0 < ε) : X ≤ (c+ε)^(2*n) := by
    refine le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp (L s V A ht he hp b k hb E n)) ?_
    filter_upwards [B s hb E n,eventually_gt_atTop 0] with t hP hg
    refine le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hP) ?_
    change ∀ᶠ i : ℕ × ℕ in F.fuse, _
    have ht : ∀ᶠ i in F.fuse, ‖E.fromCut hb t n i.1 i.2‖ ≤ (c+ε)^(2*n) := h s hb E c hc H _ hg _ ε hε
    exact ht.mono fun i H => (Complex.re_le_norm _).trans H
  have ht : Tendsto (fun ε : ℝ => (c+ε)^(2*n)) (𝓝[>] 0) (𝓝 (c^(2*n))) := by
    simpa only [add_zero] using ((show Continuous (fun ε : ℝ => (c+ε)^(2*n)) by fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  exact ge_of_tendsto ht (Eventually.mono self_mem_nhdsWithin (fun i hi => hv i hi))

lemma episode (h : B15) (B : B16) (L : B17) (Y : B18) (s : Seed C F S) (A : Spread V) (ht : Theme V A) (he : Steady V) (hp : Phase.reflects (C:=C) V A)
    {d : ℕ} {X : Columns C S d} (Q : X.Trials) (K : Columns.Trials.Valid F Q) : Retain.Funds Q K A := by
  obtain ⟨T,E⟩ := Y s V A ht d X Q K
  exact ⟨fun k i c j => fees h B L s A ht he hp (Q.allowed k) (Q.window k) (T k i c j),
         fun k i c j x H => fees h B L s A ht he hp (Q.allowed k) (Q.window k) (E k i c j x H)⟩
end YM.Bid
