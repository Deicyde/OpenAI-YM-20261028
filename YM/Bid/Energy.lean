import YM.Pressure.Seeds


/-!
# `E##` STIPULATIONS of WP per Halo, not claims. Orientation-LOCAL!

Large negative L & C paid by actual large-endpoint costs. Costs at fixed W
post-L (both W0 and postmargin then). `Serves` notation for all periodic uses.
Red core UNAFFECTED L,D estimates not allocated but USAGE at end of Energy.
`Ringing` consumer near YU.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open YM.Pressure YM.Pressure.Stores YM.Pressure.Tube YM.Pressure.Teller Input
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ComplexOrder Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)

/-! Macro charge kernel & witnesses. -/

def mcharge (x : Site c) (b : Cell f) : ℕ :=
    ((box (macroR S.patch)).filter fun z => wrap f z + S.ratio.embed x=b.1 ∧
      -- touched only torus. Need all corner locations in macro lifted.
      ∀ i ∈ visits z (square b.2.val.1 b.2.val.2), i∈box (macroR S.patch)).card

structure Payments (δ : ℝ) {S : StepData c f} (A : Stores S) (x : ℝ) (U : Config G f) (Q V : Config G c) (K : ℕ) : Prop where
  pushes : (A.tides V x δ) ⊆ hit A U Q V x
  flags : A.flags.card ≤ 4 * (A.tides V x (temp x)).card
  fee : (A.tides V x δ).card ≤ K * (A.spend U Q V x).shares
  ours : (A.outs x).card ≤ K*(radiusB x)^4*A.shares
  covers : (A.hit U Q V x).card ≤ K*(radiusB x)^4*(A.spend U Q V x).shares

/-- Native macro transport & pricing reserve. -/
structure MacroStore (S : StepData c f) (G : Gauge) (i : ℕ) : Prop where
  funded (U : Config G f) (x : Site c) : port S x U=∑ b : Cell f, mcharge S x b*toll U b
  count (p : Cell f) : ∑ i : Site c,mcharge S i p ≤ i
  maps (x p) : 0 < mcharge S x p → separation x (S.ratio.parent p.1) ≤ i

def E01 : Prop := ∀ {G : Gauge} (P : Teller G) (δ : ℝ), 0 < δ → ∃ N : ℕ, ∀ L : Side, ∀ W : ℝ, 0<W →
    P.Serves L W fun S _ _ A x U k V => Payments δ A x U (S.prediction U k) V N ∧ MacroStore S G N

-- shell comparison through macro, price all actual links. Sides large enough.
def Cops {S : StepData c f} (U : Config G f) (V : Config G c) (Q : Config G c) (e : Bond f) (γ : ℝ) :=
    let i:= S.ratio.parent e.1
    G.chord (U e*(replica S.ratio V e)⁻¹) ≤ γ * port S i U +
      if i=S.ratio.parent (e.1+Lattice.step e.2) then 0 else wire Q V (i,e.2)

def E02 : Prop := ∀ (G : Gauge) (L : Side) (j : ℕ) (K : KernelChoices),∃ C : ℝ,0<C ∧
    ∀ (c f : Side) (S : StepData c f), S.kernel=K → S.patch.L=L → S.patch.J=j → 100*macroR S.patch ≤ f.val →
    1 < c.val → ∀ (F : Forest S.ratio) (U : Config G f), SliceSet S F U → ∀ V : Config G c, ∀ (u : Bond f),
    ∀ i : S.Choices, usable S U (S.ratio.parent u.1) i → Cops (S:=S) U V (S.prediction U i) u C

structure Anchored {m n : Type*} [Fintype m] [Fintype n] (F : m → n → Pay G) (x y : ℝ) (d : m → Site c) (v : n → Site c) (B : ℕ) : Prop where
  rows (i : m) : ∑ j : n,‖F i j‖ ≤ x
  columns (i : n) : ∑ j : m,‖F j i‖ ≤ y
  stencil (i j) : F i j≠0 → separation (d i) (v j) ≤ B/50

def tagged {n : Side} (p : Twin n) : Site n := p.1.1

structure Allowance (C : ℝ) {S : StepData c f} (T : Tube G S) (x : ℝ) (V : Config G c) : Prop where
  wide : Anchored (T.Φ (till x) V) (C/(S.patch.L.val:ℝ)^2) (C*S.patch.L.val^ (2:ℕ)) (S.ratio.parent ∘ tagged) tagged (radiusB x)
  narrow : Anchored (T.Φ' (till x) V) C C Prod.fst tagged (radiusB x)
  tight : Anchored (T.N (till x) V) C C Prod.fst tagged (radiusB x)

/-- Physical rows, including transport & torsion multiplicity. -/
def E03 : Prop := ∀ {G : Gauge} (P : Teller G), ∃ A : ℝ, 0<A ∧ ∀ (L : Side) (W : ℝ), P.Serves L W fun _ T _ _ x _ _ V => Allowance A T x V

-- ell route absolute inputs (same-level). Need true label sum near all fields; budget.
def crunch {n : Side} (T : PathData G) (R d : ℕ) (p u : Cell n) := ∑' i : ℕ,
    let F:= T.row p.2 i
    if d*F.2.length ≤ R ∧ F.2.plaq = u.2 ∧ wrap n F.2.offset+p.1=u.1 then |F.1| else 0

structure LaneCounts {G : Gauge} {n m : Side} (T : PathData G) (x t : ℝ) (c : Clip) (A : ℝ) (d : ℕ) (f : Site n → Site m) : Prop where
  attic (p u : Cell n) : 0 ≤ crunch T (till x) d p u
  finite (p : Cell n) : ∑ u,crunch T (till x) d p u ≤ A
  back (p : Cell n) : ∑ u,crunch T (till x) d u p ≤ A
  maps (p q) : 0 < crunch T (till x) d p q → separation (f p.1) (f q.1) ≤ radiusB x/50
  valued (p : Cell n) (U : Config G n) : ‖shorten T (till x) d U p‖ ≤ ∑ u, crunch T (till x) d p u * toll U u
  keeps (V : Config G n) (i : Cell n) : PathData.kept c t i.1 V → ‖shorten T (till x) d V i‖ ≤ A*t
  dropped (V : Config G n) (i : Site n) (j : Cell n) : t * Real.exp (separation i j.1/c.relaxation) < toll V j → separation (f i) (f j.1) ≤ radiusB x/50

structure Maximum (C : ℝ) {S : StepData c f} (T : Tube G S) (x : ℝ) (V : Config G c) : Prop where
  up v : ‖T.vision (till x) (temp x) V v‖≤ C*fiery G x S.patch.L
  phi v : ‖T.Mv (till x) (temp x) V v‖≤ C/(S.patch.L.val:ℝ)^2*fiery G x S.patch.L
  hot v : ‖T.Mw (till x) (temp x) V v‖≤ C*fiery G x S.patch.L

/-- Dv continuum widths tested at selectors, regardless of flags farther. -/
def E04 : Prop := E03 → ∀ {G : Gauge} (P : Teller G), ∃ A : ℝ, 0<A ∧ ∀ (L : Side) W, P.Serves L W (@fun c _ S T _ _ x _ _ V =>
      LaneCounts T.up x (fiery G x L) T.high A 1 S.ratio.parent ∧
      LaneCounts T.down x (temp x) T.low A L.val (id : Site c → Site c) ∧ Maximum A T x V)

/-- K-small & normalized crowd. Field REAL. -/
structure Crowds (δ B : ℝ) {S : StepData c f} (T : Tube G S) (x : ℝ) (V : Config G c) : Prop where
  positive (i : Cell c) : temp x < toll V i → toll V i ≤ δ → T.low.direct/4*temp x*toll V i ≤ T.workC (till x) V (temp x) i
  middle (i : Cell c) : toll V i ≤ temp x → -(B*temp x^4) ≤ T.workC (till x) V (temp x) i
  last (i : Cell c) : δ < toll V i → -(T.low.linear*temp x*toll V i) ≤ T.workC (till x) V (temp x) i

def CoverStore (P : Teller G) (δ : ℝ) := ∃ B : ℝ, 0<B ∧ ∀ (L : Side) (W : ℝ), P.Serves L W fun _ T _ _ x _ _ V => Crowds δ B T x V

def E05 : Prop := ∀ {G : Gauge} (P : Teller G),∃ δ : ℝ, 0 < δ ∧ CoverStore P δ

def Seals (P : Teller G) := ∃ N : ℕ, ∀ L : Side, N ≤ L.val → ∀ᶠ w : ℝ in atTop,
    ∃ d : ℝ, 0 < d ∧ P.Serves L w fun S T _ A x U k V =>
      (T.high.linear/2*(fiery G x L)*(∑ i∈ A.swell U (fiery G x L), toll U i) +
        d*(fiery G x L)^2*((A.costs \ A.swell U (fiery G x L)).card:ℝ) ≤ A.tally T x U V) ∧
      S.kernel.penalty/8*(∑ i∈A.aisles, wire (S.prediction U k) V i^2) ≤ A.talli T x (S.prediction U k) V

/-- Counts Fz payments on ACTUAL hull. W not chosen before L. -/
def E06 : Prop := E03 → E04 → ∀ {G : Gauge} (P : Teller G), Seals P

/-- For w-dependent m count all noise seeds (including
          small n>Wt but ≤2Wt).

Keeps cut positions exactly.

Estimates **do not** require linear
          cancellation.

No global sector hypothesis. -/
def Lapse (P : Teller G) (δ : ℝ) := ∃ C : ℝ, 0<C ∧ ∀ L : Side, ∀ W : ℝ, 0 < W →
    ∃ Z : ℝ, 0<Z ∧ P.Serves L W fun S T _ A x U k V =>
      let Q := S.prediction U k
      let t := fiery G x L
      let b : ℝ := radiusB x
      talll T x U Q V (A.hit U Q V x) + C/L.val^ (2:ℕ)*t*(∑ i ∈ A.swell U t,toll U i) +
        C*t*(∑ i∈A.aisles, wire Q V i) + Z*t^2*b^4*(A.spend U Q V x).shares ≥
          (T.low.linear*temp x)*(∑ i ∈ A.tides V x δ,toll V i)

def E07 : Prop := E01 → E03 → E04 → ∀ {G : Gauge} (P : Teller G) (δ : ℝ), 0 < δ → Lapse P δ

/-- UNaffected interior patch H0.4; loses polynomial B^10.
Axial in *coarse* gauge. Need analytic derivatives more. -/
def Stitches (P : Teller G) (L : Side) (W : ℝ) := ∃ C : ℝ, 0 < C ∧ P.Serves L W fun S _ _ A x U k V =>
    let B := radiusB x; let t := C*(B:ℝ)^10*largeT G x L
    ∀ p∈ A.outs x, p∉A.hit U (S.prediction U k) V x → ∃ z : Site _ → G.El,
      (∀ i : Bond _, separation p.1 i.1 ≤ 2*B/5 → G.chord (Lattice.gauge z V i) ≤ t) ∧
        ∀ i : Bond _, separation p.1 (S.ratio.parent i.1) ≤ 2*B/5 → G.chord (Lattice.gauge (z∘S.ratio.parent) U i) ≤ t

def E08 : Prop := E01 → E02 → ∀ {G : Gauge} (P : Teller G) (L : Side) (W : ℝ), 0 < W → Stitches P L W

def Belly (P : Teller G) (L : Side) (W : ℝ) := ∀ ε : ℝ, 0 < ε → P.Serves L W fun S T _ A x U k V =>
    let Q := S.prediction U k
    talll T x U Q V (A.outs x \ A.hit U Q V x) ≥ -(ε*fiery G x L^2*A.shares)

/-- red. Work larger. Relies on  in ANY oriented channel
          on actual T towers at linear order. Need prove. -/
def EBare : Prop := E03 → E04 → ∀ {G : Gauge} (P : Teller G) (L : Side) (W : ℝ), 0 < W → Stitches P L W → Belly P L W

/-- Assemble pre/post Gates. Does not know any Pinned Move. -/
def E09 : Prop := E01 → ∀ {G : Gauge} (P : Teller G), Seals P → ∀ δ : ℝ, 0<δ → CoverStore P δ → Lapse P δ →
    (∀ L : Side,∀ W : ℝ, 0<W → Belly P L W) → P.Grants

-- Smoke to actually ask loc.Halo
lemma issues (a : E01) (b : E02) (c : E03) (d : E04) (e : E05) (f : E06) (g : E07) (i : E08)
    (j : E09) (A : EBare) (k : Teller G) : Grants k := by
  obtain ⟨x,hx,K⟩ := e k
  exact j a k (f c d k) _ hx K (g a c d k x hx) fun L w hx => A c d k L w hx (i a b k L w hx)
end YM.Bid

noncomputable section
namespace YM.Bid
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open YM.Pressure YM.Pressure.Stores YM.Pressure.Tube YM.Pressure.Teller Input
open YM.RG.Supply YM.Pressure.Testing
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ENNReal ComplexOrder

/-- Demonstrate stage order for using this conclusion; arbitrarily many extra
pre-L requests still issueable by raising floor. Also raise at entrances
with changed curve. This does NOT assert that all the other estimates were
clocked/pinned. For Ringing wherever post-raisings also performed, may use
`recheck`. -/
lemma pricing_order {G : Gauge} (P : Sheet G) (K : MapPrices) (A : ∀ j i, Grants (Testing.query P K j i)) :
    ∃ k : ℕ → ℕ, ∀ n : ℕ → ℕ, (∀ i,k i ≤ n i) → ∀ D : Rolls { P with floorL := n }, ∀ m ≥ 0, ∀ Θ : Protection D,
    ∀ V : Supply.Delays Θ, ∃ W : Supply.Delays Θ,
      W.shells=V.shells ∧ W.growth=V.growth ∧ W.scaleEntry=V.scaleEntry ∧ V.betaEntry ≤ W.betaEntry ∧
        ∃ F : ℕ → ℕ → ℝ, Ringing K F W ∧ ∀ i, ∀ j,F i j ≥ m := by
  choose b hb using fun i j => (A i j).precedes
  let k i := max (b i i) (max (b i (i-1)) (P.floorL i))
  refine ⟨k,fun r hr D m hm Θ V => ?_⟩
  have hi (i j : ℕ) (hk : j≤ i) (hl : i≤ j+1) : b i j ≤ (D.L i).val := by
    apply le_trans ?_ (le_trans (hr i) (D.large i).need)
    rcases eq_or_lt_of_le hk with h|h
    · rw [h]; exact le_max_left ..
    have hq : j=i-1 := by omega
    nth_rewrite 1 [hq]; exact le_max_of_le_right (le_max_left ..)
  let P' : Sheet G := { P with floorL := r }
  have hf (i j : ℕ) : ∃ w ≥ m,∃ x : ℝ, j ≤ i → i ≤ j+1 → Stamp (p:=P') (D:=D) K i j w x := by
    by_cases h : j ≤ i ∧ i ≤ j+1
    · obtain ⟨W,hW,a,ha,hA⟩ := Eventually.exists ((eventually_gt_atTop m).and (hb i j (D.L i) (hi i j h.1 h.2)))
      obtain ⟨x,hx⟩ := eventually_atTop.mp hA.late
      exact ⟨W,hW.le,x,fun _ _ ↦ ⟨hm.trans_lt hW,a,ha,hx⟩⟩
    exact ⟨m,le_rfl,0,fun j i => False.elim (h ⟨j,i⟩)⟩
  choose F hF c hC using hf
  let W : Supply.Delays Θ := { V with betaEntry := fun i => max (V.betaEntry i) (max (c i i) (c i (i-1))) }
  refine ⟨W,rfl,rfl,rfl,fun i => le_max_left ..,F,⟨fun j i h ht hc => ?_⟩,hF⟩
  obtain ⟨hw,x,hx,hh⟩ := hC i j h ht
  refine ⟨hw,x,hx, fun b ha => hh b (le_trans ?_ ha)⟩
  rcases eq_or_lt_of_le h with h|h
  · rw [h]; exact le_max_of_le_right (le_max_left ..)
  have hf : j=i-1 := by omega
  rw [hf]; exact le_max_of_le_right (le_max_right ..)

lemma recheck {G : Gauge} {P : Sheet G} {D : Rolls P} {T : Protection D} {W V : Supply.Delays T} (h : W.betaEntry ≤ V.betaEntry)
    {F : ℕ → ℕ → ℝ} {K} (g : Ringing K F W) : Ringing K F V := by
  refine ⟨fun x i hx hh w => ?_⟩
  obtain ⟨h1,a,ha,hh⟩ := g.receipts x i hx hh w
  exact ⟨h1,a,ha,fun b hw => hh b ((h i).trans hw)⟩
end YM.Bid
