import YM.Push.ABSOLUTE_SUMS.Charge
import YM.Push.ABSOLUTE_SUMS.Labels
import YM.Push.ABSOLUTE_SUMS.Reserves



/-!
# Charging a whole connected result

Combine optional input costs and grant-paid packet costs, retaining a
polynomial on the WHOLE word and a reduced exponential receipt, for
example for the forced labels. Yields HIT per address, not a statement
about running an RG automaton or proof that its outputs do have the
per-term tests. Can use before committing post-L budgets. A concrete
sufficient set of inequalities; larger halo factors for overlaps can
be included via the l parameter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Mixed
open Lattice Wilson RG Pressure Finset Reserves Packets
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {c f : Side}

/-- Numerical controls at one step. -/
structure Costs where
  exponent : ℝ  -- awarded output support exponent
  reservePoly : ℝ  -- ε
  reserveTree : ℝ  -- δ
  cap : ℝ       -- C charged to packet
  spendSeed : ℝ -- unpriced per-seed expenses (log cost)
  extraSeed : ℝ -- coefficient of seed count in D*
  markSeed : ℝ  -- what to EXTRACT per seed
  gain : ℝ      -- e.g. μ β t²
  optionalHit : ℝ
  packetRatio : ℝ
  rootHit : ℝ
  q : ℝ

namespace Costs

def head (b : Costs) := b.exponent + 2*b.reservePoly + b.reserveTree
def spend (b : Costs) := b.spendSeed + 2*b.reservePoly*b.extraSeed + b.markSeed

/-- Named sufficient test. Doesn't rely on topology of any possible
partial choice, beta path, etc. Applies pointwise. -/
structure Buy (b : Costs) (L : Side) (l B : ℕ) : Prop where
  eps : 0 < b.reservePoly
  δ : 0 < b.reserveTree
  γ : 0 < b.rootHit
  capture : 0 ≤ b.cap
  extra : 0 ≤ b.extraSeed
  marked : 0 ≤ b.markSeed
  price : 0 ≤ b.exponent
  packet : Packets.fit L l B b.head b.spend b.gain b.packetRatio
  combined : totalCharge L b.cap l B b.packetRatio 0 + b.optionalHit ≤ b.rootHit
  trees : Trees.degreePrice B b.rootHit b.reserveTree ≤ b.q
  grows : b.q < 1

/-- Degree/stencil/mandatory-seed answer -/
def ceiling (b : Costs) (m k r : ℕ) (T : ℝ) := Reserves.extract b.reservePoly k T
  (b.markSeed*r) * Reserves.treeYield b.rootHit b.q m
end Costs

abbrev Alphabet (S : StepData c f) (ι : Type*) := Stores S ⊕ ι
variable {ι : Type*} (S : StepData c f)

def foot (l B : ℕ) (X : ι → Support c) : Alphabet S ι → Support c :=
    Sum.elim (fun A => A.dome (l*B)) X

def shares : Alphabet S ι → ℕ := Sum.elim Pressure.Stores.shares (fun _ => 0)

def lengths (a : Costs) (d : ι → ℝ) : Alphabet S ι → ℝ :=
    Sum.elim (fun A => a.extraSeed*A.shares) d

def costs (l B : ℕ) (p : Stores S → ℝ) (w : ι → ℝ) : Alphabet S ι → ℝ :=
    Sum.elim (fun A => if connected S l B A then p A else 0) w

def stamp (b : Costs) (i : Alphabet S ι) : ℝ := b.markSeed * shares S i

def charges (l B : ℕ) (X : ι → Support c) (a : Costs) (d : ι → ℝ) :=
    setPrice (foot S l B X) B (lengths S a d)

structure Accounts (l B : ℕ) (b : Costs) (X : ι → Support c) (w d : ι → ℝ) (p : Stores S → ℝ) : Prop where
  packetBound : ∀ A : Stores S, connected S l B A → 0 ≤ p A ∧
    p A ≤ Packets.income b.cap b.spendSeed b.gain A.shares
  holds : ∀ i,0 ≤ w i
  extra : ∀ i,0 ≤ d i
  pays : Ac.Hit X B (tariff w d (fun _ => 0) b.reservePoly) b.head b.optionalHit

section Components
variable (l B : ℕ) (b : Costs) (X : ι → Support c) (w d : ι → ℝ) (p : Stores S → ℝ)
variable (hr : b.Buy S.patch.L l B) (ha : Accounts S l B b X w d p)

include hr ha in
theorem ready_vertices :
    let Y := foot S l B X; let f := costs S l B p w
    Trees.Ready Y B (tariff f (lengths S b d) (stamp S b) b.reservePoly) (b.exponent+2*b.reservePoly)
      b.rootHit b.reserveTree b.q := by
  intro Y f
  let w1 A := p A * Real.exp (2*b.reservePoly*(b.extraSeed*A.shares)+b.markSeed*A.shares)
  have he A (hh : connected S l B A) : 0 ≤ w1 A ∧ w1 A ≤ Packets.income b.cap b.spend b.gain A.shares := by
    obtain ⟨hi,hI⟩ := ha.packetBound A hh
    unfold w1; refine ⟨mul_nonneg hi (Real.exp_pos _).le,
      (mul_le_mul_of_nonneg_right hI (Real.exp_pos _).le).trans_eq ?_⟩
    unfold Packets.income Costs.spend; rw [mul_assoc,← Real.exp_add]; ring_nf
  have hv := Packets.packet_hit S l B w1 hr.capture hr.packet he
  let z := Sum.elim (fun A => if connected S l B A then w1 A else 0)
    (tariff w d (fun _ => 0) b.reservePoly)
  have hZ : tariff f (lengths S b d) (stamp S b) b.reservePoly = z := by
    funext i; rcases i with A|i
    · by_cases h : connected S l B A <;> simp [f,costs,lengths,shares,stamp,w1,z,tariff,h]
    simp [f,costs,lengths,stamp,shares,w1,tariff,z]
  rw [hZ]
  refine ⟨hr.γ,hr.δ,hr.trees,hr.grows,?_,?_⟩
  · rintro (A|i)
    · unfold z; dsimp only [Sum.elim]; split
      next h => exact (he A h).1
      next h => exact le_rfl
    exact mul_nonneg (ha.holds _) (Real.exp_pos _).le
  intro x
  exact budget_loosen (Labels.together _ _ _ hv ha.pays x) hr.combined

-- Connectivity is for the union of packets and additional addresses,
-- not pretending packets separated by the original sector choices
-- cannot interact through other read supports.
def Allowed (m r : ℕ) (T : ℝ) (s : Finset (Alphabet S ι)) :=
    Ac.Spark (foot S l B X) s ∧ m ≤ s.card-1 ∧ r ≤ (∑ i∈s, shares S i) ∧
    T ≤ charges S l B X b d s

def Price (k : ℕ) (s : Finset (Alphabet S ι)) :=
    (∏ i∈s, costs S l B p w i)*(1+charges S l B X b d s)^k

def selected (m k r : ℕ) (T : ℝ) (s : Finset (Alphabet S ι)) :=
    if Allowed S l B b X d m r T s then Price S l B b X w d p k s else 0

include hr ha in
lemma zero_le_price (k : ℕ) (s : Finset (Alphabet S ι)) : 0 ≤ Price S l B b X w d p k s := by
  have he i : 0 ≤ costs S l B p w i := by
    rcases i with A|i
    · unfold costs; dsimp only [Sum.elim]; split
      next hh => exact (ha.packetBound _ hh).1
      next hh => exact le_rfl
    exact ha.holds i
  have ht i : 0 ≤ lengths S b d i := by
    rcases i with A|i
    · exact mul_nonneg hr.extra (Nat.cast_nonneg _)
    exact ha.extra i
  have hh : 0 ≤ charges S l B X b d s := sum_nonneg fun i _ =>
    add_nonneg (Nat.cast_nonneg _) (ht i)
  unfold Price; exact mul_nonneg (prod_nonneg fun i _ => he i) (by positivity)

include hr ha in
/-- The shape used for absolute hit/KBound consumption. -/
theorem mixed_hit (m k r : ℕ) (T : ℝ) : Ac.Hit
    (fun s : Finset (Alphabet S ι) => s.biUnion (foot S l B X)) B
    (selected S l B b X w d p m k r T) b.exponent (b.ceiling m k r T) := by
  let Y := foot S l B X; let f := costs S l B p w
  have he i : 0 ≤ f i := by
    rcases i with A|i
    · unfold f costs; dsimp only [Sum.elim]; split
      next hh => exact (ha.packetBound A hh).1
      next hh => exact le_rfl
    exact ha.holds i
  have ht i : 0 ≤ lengths S b d i := by
    rcases i with A|i
    · exact mul_nonneg hr.extra (Nat.cast_nonneg _)
    exact ha.extra i
  have hh := ready_vertices S l B b X w d p hr ha
  intro x
  let Q := Allowed S l B b X d m r T
  have hs (s : Finset (Alphabet S ι)) (h : Q s) :
      T ≤ charges S l B X b d s ∧ b.markSeed * r ≤ ∑ i∈s, stamp S b i := by
    refine ⟨h.2.2.2,?_⟩
    simp only [stamp,← mul_sum]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h.2.2.1) hr.marked
  convert Reserves.sets Y B f (lengths S b d) (stamp S b) he ht hr.eps hr.price hh
    m k x Q (fun s _ _ _ h => hs s h) using 1; ext s
  by_cases hl : x∈s.biUnion Y
  · change (if x ∈ s.biUnion Y then _ else _) = _
    by_cases hy : Q s
    · have he := hy.1; have hm := hy.2.1
      rw [if_pos hl,selected,if_pos hy,if_pos ⟨hy,hm⟩,rooted,if_pos ⟨he,hl⟩]
      unfold Price; change _*_*_ = _
      dsimp only [Trees.currency,charges,f,Y]; ring
    rw [if_pos hl,selected,if_neg hy,zero_mul,if_neg (fun ⟨h,_⟩ => hy h)]
  · change (if x ∈ s.biUnion Y then _ else _) = _
    rw [if_neg hl]; unfold rooted; split <;> simp [hl]
  rfl

include hr ha in
/-- Cost converter at all cutoffs. p is the PER-PACKET cost before
hit summation; optional Hit likewise pertains to individual optional
addresses. At output, distinct occurrences still have their own costs.
Don't mistake `he` for a bound on FIRST-INTEGRATION analytic coefficients
without actually deriving it there (on the corresponding geometry).
`Y` is actual overlap footprint, may be smaller than the charged one.
Taking `r = 1` extracts an exponential for all K-type terms that use a
packet (retain this test where needed; not inferred universally!). -/
theorem output {κ : Type*} (Y : κ → Support c) (g : κ → ℝ) (spell : κ → Finset (Alphabet S ι))
    (hg : ∀ i, 0 ≤ g i) (m k r : ℕ) (T C : ℝ) (hC : 0 ≤ C)
    (hy : ∀ i, g i≠0 → Y i ⊆ (spell i).biUnion (foot S l B X))
    (he : ∀ (s : Finset (Alphabet S ι)) (L : Finset κ), (∀ i∈L, spell i=s) →
      ∑ i∈L, g i ≤ C*selected S l B b X w d p m k r T s) :
    Ac.Hit Y B g b.exponent (C*b.ceiling m k r T) := by
  refine Labels.variants (fun s => s.biUnion (foot S l B X)) B hr.price ?_ Y spell g hg hy he
  intro i
  have he := budget_scale hC (mixed_hit S l B b X w d p hr ha m k r T i)
  convert he using 1; ext s
  split
  next he => ring
  next he => rw [mul_zero]

include hr ha in
/-- Example output application on `A` itself. External estimate `hv`
requires actual sales to have been tied to packets and optional costs
on the actual labels (no term outside these forms unless it too is
charged as another form). Contract gives no other fields of Valid. -/
theorem forcedBudget {G : Gauge} (A : Activities G c) (P : BudgetPoint) (spell : ℕ → Finset (Alphabet S ι))
    (hb : P.B=B) (hh : P.supportExponent=b.exponent)
    (g : ℕ → ℝ) (he : ∀ i,0 ≤ g i ∧ ∀ U, ‖A.K i U‖ ≤ g i) (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hy : ∀ i, g i≠0 → (A.forced i).support ⊆ (spell i).biUnion (foot S l B X))
    (hv : ∀ (s : Finset (Alphabet S ι)) (L : Finset ℕ), (∀ i∈L, spell i=s) →
      ∑ i∈L, g i ≤ C*selected S l B b X w d p 0 k 1 0 s) :
    A.KBound P (C*b.ceiling 0 k 1 0) := by
  refine ⟨g,he,?_⟩
  intro x
  simpa only [BudgetPoint.mass,hb,hh,mul_comm] using
    output S l B b X w d p hr ha _ _ spell (fun i => (he i).1) _ _ _ _ _ hC hy hv x
end Components
end YM.Push.AbsoluteSums.Mixed
