import YM.Overlay.Assembly



/-!
# Marker-support check and conversion to Metered

Try supplying Prepared at every stop.
Units covered, norm converters at true stop order. No use determinant to adjust marks.
Weak family in C may need to pass off-panel bounds as well; see B ledger. Here
area permits count-independent costs at center. Spend ≤1 on each single
(includes stencil caps/dim & w factors, pay relative to ALL the requested markers),
mixed may use a **provisional** smaller radius but demand at least this if
using path exponent reserve, otherwise must supply the final bounds directly.
Order defined at upstream stamps, support costs at actual halo. Don’t vary
the history. Not asserting these fortes hold!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Mix
open Set Filter Function RG Marker Lattice Wilson Cells MeasureTheory Overlay Stock Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators NNReal ENNReal ComplexOrder

variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

-- factorial budget token. `plate ℓ` permits *one* weight for label,
-- stores witness for each derivative order.
def grain (P : BudgetPoint) (s : Support n) (F : Config G n → ℂ) (x : Site n) (W : ℝ) :=
    ∃ f : ℕ → ℝ,(∀ i,0 ≤ f i) ∧ (∑ i∈ Finset.range (P.order+1),f i/(i.factorial:ℝ)) ≤ W ∧
      ∀ (k : List (Directions G n)), k.length ≤ P.order → (∀ i∈k,P.dirBound x i) →
        ∀ U : Config G n, Healthy P.threshold s U → ‖leftDerivs F k U‖ ≤ f k.length

-- indicator budgets with arbitrary support reserve, KEEP uses width ζ exactly (cost in Meat).
def loaf (P : BudgetPoint) (S : Support n) (r x : ℝ) := Real.exp ((P.supportExponent+r)*coverNumber P.B S) * x

def ranked (Q : R.Mode) : Bool := 2 ≤ Q.val.card

structure Stubs {P : Rep G n} (A : Bands R P) where
  a : ℕ → ℝ
  k : ℕ × ℕ → ℝ
  nonnegative i : 0 ≤ a i
  usable i : 0≤k i
  kernels : ∀ i x,x∈(A.rays i).val → grain P.p (A.support i) (A.H i) (A.origins x) (a i)
  supplies i j U : ‖A.entries i j U‖ ≤ k (i,j)
  paid i : 0<k i → A.entries i.1 i.2 ≠ 0

namespace Stubs
variable {P : Rep G n} {A : Bands R P} (T : Stubs A)

def crown (w : V→ℝ) (δ : ℝ) (q : ℕ) := Poly.toll w (A.rays q)*loaf P.p (A.support q) δ (T.a q)

def cord (w : V→ℝ) (δ : ℝ) (q : ℕ × ℕ) := Poly.toll w (A.marks q.1 q.2)*loaf P.p (P.activities.forced q.1).support δ (T.k q)

def funded (w : V→ℝ) (δ : ℝ) (b : Bool) (u : ℝ) :=
    (∀ i : V, SumBudget (fun j => if ranked (A.rays j)=b ∧ i∈(A.rays j).val then T.crown w δ j else 0) u) ∧
    ∀ i : V,SumBudget (fun j : ℕ×ℕ => if ranked (A.marks j.1 j.2)=b ∧ i∈(A.marks j.1 j.2).val then T.cord w δ j else 0) u

def far := ∀ v q,v≠q → 8 ≤ P.p.B ∧
    P.p.B * P.p.B ≤ separation (A.origins v) (A.origins q)

-- Request accepts raw provisional rates relative to support reserve OR FINAL rank≥2.
def intake (w : V → ℝ) := T.funded w 0 true 1 ∨
    ∃ (t : V→ℝ) (r : ℝ),0≤ r ∧ (∀ i,0<t i ∧ w i≤ t i*Real.exp (r*P.p.B/64)) ∧ T.funded t r true 1

-- fiscal ask for one level with uniform prices
structure Holds (A : Bands R P) (w : ℝ) : Prop where
  units i : w * ‖A.units i‖ ≤ 1
  ready : A.Active
  spaced : far (A:=A)
  atC : ∃ B : Stubs A,B.funded (fun _ => w) 0 false 1 ∧ B.intake (fun _ => w)
end Stubs

variable {C : Family G} {d m N i p : ℕ}

def alignment {C : Family G} (m p N : ℕ) {V : Type} (q : ∀ i, V → Site (C.side i p)) :=
    ∀ i, m ≤ i → i < N → ∀ j,(C.path.levels.clock.op i p).ratio.parent (q (i+1) j)=q i j

def camp (C : Family G) (p m i : ℕ) (x : Site (C.side m p)) := open scoped Classical in
    if h : m ≤ i then (C.S.toDepth h p).embed x else 0

def ticket (C : Family G) (k : ℝ) (N p m i : ℕ) (q : m≤N) : Prop :=
    (∀ j,(Cells.center C.S p q 0).copyMap j 0=camp C p m N j) ∧
    alignment m p N (C:=C) (camp C p m) ∧
    ∀ r,i ≤ r → r ≤ N → ∀ x y,x ≠ y →
      C.path.levels.clock.coverSize r^2*k ≤ (separation (camp C p m r x) (camp C p m r y) : ℝ)

def envelope (C : Family G) (p : ℝ) (n : ℕ) :=
    p*(C.path.levels.params n).columns * ∏ j∈ Finset.range n, (C.path.levels.params (j+1)).columns

def width (C : Family G) (p : ℝ) (k n : ℕ) := C.path.levels.clock.hatCoupling n ^ k / envelope C p n

def last (C : Family G) (n : ℕ) (t : ℝ) := t / (Nat.factorial ((C.path.levels.params n).order):ℝ)

def paidL (C : Family G) := ∀ i,(Nat.factorial ((C.path.levels.params i).order):ℝ) ≤ (C.path.levels.params i).columns
-- RWinding producer pre-L easily impose via enlarge columns. Include in tariff only.

/-! RMetered producer port: want ALL m with opens, get Lanes on same H with
  cardinal-copy stubs. Ensemble through EVERY encoding. `arise` start spans before;
  uses etc. Not promising x-hat receipt anywhere. Stamp reserves Cl.MAY need
  enlarge support ensuring Shape at P.p for all T. -/

structure Story {p m i N d : ℕ} (C : Family G) (L : Lane C.path (census (Site (C.side m p))) N p) (v : C.label d) (q : ℝ → ℕ → ℝ) (a : ℝ) : Prop where
  leg : m ≤ i
  endline : i ≤ N
  ship j : L.load j=d ∧ L.uses j=(Cells.center C.S p (leg.trans endline) 0).copy j (C.O N p (d:=d) v 0)
  camps j : i ≤ j → j ≤ N → ∀ k,(L.sites j).origins k=camp C p m j k
  bulk (j) : i≤j → j≤N → Stubs.Holds (L.sites j) (q a j)
  -- actual step
  reads (s : (census (Site (C.side m p))).Mode) : Integrable (Ride.Product (H:=C.path) (N:=N) (p:=p) L.uses s) (Wilson.law G (C.side N p) (C.beta N p))
  first s U : L.signal N s U = Ride.bump (C.path.S.a N) s L.load * (bare (C.path.β N p N) U : ℂ)*Ride.Product (H:=C.path) L.uses s U
  transforms j s : i≤j → j<N → L.signal j s=(Ride.bump (↑(C.path.S.block j).val) s L.load) •
    (C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (L.signal (j+1) s)

def Circle (C : Family G) (d : ℕ) (u : ℝ) := ∃ a : ℝ,∃ t k,0<a ∧ (1:ℝ)≤t ∧ ∀ m i,C.ref d ≤ m → Tabs.opens C.path.levels t m i →
    ∀ᶠ N : ℕ in atTop,∃ h : m ≤ N,∀ p,ticket C t N p m i h → ∀ v : C.label d,‖v‖ ≤ u → ∃ L,Story (i:=i) (m:=m) (p:=p) (N:=N) C L v (fun r i => width C r k i) a
end YM.Mix

namespace YM.Bid
open Set Filter Function RG Marker Lattice Wilson Cells MeasureTheory Overlay Stock Finset Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators NNReal ENNReal ComplexOrder

-- RESERVES constants 64 possible? path length ring_path cover L: D size ≤4B+2;
-- attach tour adds 2B each marker. for k≥2, B≥8. Good.
def I01 : Prop := ∀ (n : Side) (V : Type) [Fintype V] [DecidableEq V] (f : V → Site n) (B : ℕ), 8 ≤ B →
    ∀ F : Finset V, (∀ i∈F,∀ j∈F,i≠j → B^2 ≤ Lattice.separation (f i) (f j)) → 2≤ F.card → ∀ H : Lattice.Support n, F.image f ⊆ H →
      B * F.card ≤ 64*coverNumber B H

/-- prices all tagged weights. Fiscal including order≠k. -/
def I02 : Prop := I01 → ∀ (G : Gauge) (n : Side) (V : Type) [Fintype V] [DecidableEq V] (R : Census V)
    (X : Rep G n) (P : Bands R X) (r : ℝ),0 < r → Stubs.Holds P r →
    P.Radial (fun _ => r/(X.p.order.factorial:ℝ)) 1 2 2 1

/-- full geometry of ancestry to any stop. NOTE budget Contacts may require stage j large.
  link seam equality to all layers. -/
def I03 : Prop := ∀ (G : Gauge) (C : Family G) (k : ℝ), 1 ≤ k → Tabs C.path.levels →
    ∀ m i,Tabs.opens C.path.levels k m i → ∀ N,i ≤ N → ∀ p h,ticket C k N p m i h

/-- Number feasibility for ONE envelope, cols charged. fiscal estimate
 independent of weighting history. doesn't ensure Circle. -/
def I04 : Prop := ∀ (G : Gauge), G.Simple → ∀ (p : ℝ) (C : Family G) (r : ℕ), 0<p → paidL C →
    (∀ i,0 < width C p r i) ∧ ∀ ε : ℝ, 0<ε → ∀ᶠ i in atTop,
      5-Real.log (last C i (width C p r i)) ≤ ε*C.S.scale i

-- Actual assembly sanity.
variable {G : Gauge} {C : Family G}
theorem installs (h : G.Simple) (a : I01) (b : I02) (e : I03) (w : I04) (u : C.Makes) (hp : paidL C) (t : Tabs C.path.levels)
    (H : ∀ d (r : ℝ),0<r → Circle C d r) : Input.Metered C := by
  refine ⟨u,fun d r hr => ?_⟩
  obtain ⟨c,T,j,hc,hT,H⟩ := H d r hr
  let W := width C c j
  obtain ⟨he,hh⟩ := w G h c C j hc hp
  change ∀ i, 0<W i at he
  let A : Fuel C d r := ⟨T,hT,fun i ↦ ⟨i,last C i (W i),1,2,2,1,by apply div_pos (he i); positivity⟩,fun _ => rfl⟩
  refine ⟨A,?_,fun x hx => ?_⟩
  · intro i k hx hv
    have hb : i ≤ k := hv.1
    refine ⟨hb,?_⟩
    filter_upwards [H i k hx hv,eventually_ge_atTop k] with N HN hk
    obtain ⟨hN,H⟩:=HN
    refine ⟨hN,fun p v hI => ?_⟩
    have ht := e G C T hT t _ _ hv N hk p hN
    obtain ⟨L,hu⟩:=H p ht v hI
    obtain ⟨G1,G2,G3⟩ := ht
    have hB (ℓ) (hw : k ≤ ℓ) (hy : ℓ ≤ N) : (L.sites ℓ).Radial (fun _ => (A.stamps ℓ).w) 1 2 2 1 := by
      let X := (C.path.rep N p ℓ)
      have hf := b a G (C.side ℓ p) (Site (C.side i p)) (census _) X (L.sites ℓ) (W ℓ) (he ℓ) (hu.bulk _ hw hy)
      have HG : X.p.order=(C.path.levels.params ℓ).order := by
        unfold X; rw [(u.wilson.represents N p ℓ hy).vac]; rfl
      rwa [HG] at hf
    refine ⟨L,⟨hk,fun ℓ Hw Hy => ⟨(hu.bulk _ Hw Hy).ready,_,1,2,2,1,hB ℓ Hw Hy⟩,
      fun m s hm hi => ?_,hu.reads,hu.first,fun m hM hk s => hu.transforms m s hM hk⟩,hB k (le_refl _) hk,fun i => ⟨(hu.ship i).1,(hu.ship i).2,(hu.camps N hk (le_refl _) i).trans (G1 i).symm⟩⟩
    rw [hu.camps _ (hm.trans (Nat.le_succ _)) hi _,hu.camps _ hm hi.le]; exact G2 _ (hb.trans hm) hi _
  filter_upwards [hh x hx] with i hi
  change 1+2+2*1-_ ≤ _; norm_num;exact sub_le_iff_le_add.mp hi
end YM.Bid
