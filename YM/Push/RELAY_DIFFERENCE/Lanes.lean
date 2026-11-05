import YM.Push.RELAY_DIFFERENCE.Majorants
import YM.Push.RELAY_DIFFERENCE.Matching
import YM.Work.I02
import YM.Work.I03

/-!
# Passage for a genuine multi-source representation

Compile the remaining RG input at *density level*, see `Joint` and its
`ArrayBounds`.

All arrays on the actual Wilson vocabulary, all supports,
orientation copies and marker weights must be paid.

Does the downward/height arithmetic and application
to obtain the final normalized density estimates on these inputs.

This
includes the one-body cost (which only falls exponentially AFTER matching),
and the simultaneous mixed ranks and root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Labels Lattice Cells Marker Overlay Stock Bid Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {N p m i d r : ℕ} {f : Extraction.Order} {F : Trial C}

section Multi

/-- Aligned full polynomials on the common vacuum. -/
structure ArrayStep (D : Trial C) (d : ℕ) (hm : m ≤ r) (hr : r ≤ N)
    (L : GridLane C m N p) : Prop where
  distributed i : L.load i=d ∧ L.uses i=(center C.S p (hm.trans hr) 0).copy i (D N p 0)
  origin i : r ≤ i → i ≤ N → ∀ j, (L.sites i).origins j=camp C p m i j
  label i : r ≤ i → i ≤ N → (L.sites i).Active
  birth s U : L.signal N s U = Ride.bump (C.S.a N) s L.load *
      (bare (C.beta N p) U : ℂ)*Ride.Product L.uses s U
  sends i : r ≤ i → i < N → ∀ s, L.signal i s=(Ride.bump (C.S.block i).val s L.load) •
      (C.path.levels.clock.op i p).push (C.path.β N p (i+1)) (L.signal (i+1) s)

/-- All the given grain constants on this same chosen Lane (no cherry-picking
an independent story). -/
abbrev Pamphlet (L : GridLane C m N p) (r : ℕ) := ∀ i : ℕ, r ≤ i → i ≤ N → Stubs (L.sites i)

def payee (S : Solo C F d) (N p i : ℕ) := let v := S.duet N p;
    v.cost i+(C.labels.level d).coeffSize (v.voice i).x

def rent (S : Solo C F d) (P : Prices) (N p i : ℕ) := P.rate C (S.uniform (N,p)) N i

/-- Unweighted single cost in this population. Keep this separate: it needs
comparison of actual aligned marker data to the isolated S.

E.g. producer may prove with exact singleton components and masks paid in
each placement at the corresponding levels. `Range` at this interface doesn't
ask for term-by-term uniqueness or equality of origins' *presentations* with
each other; only the cost estimate in terms of the actual S. All estimate
tests use THIS L and its labels. The singleton *signal identity* also holds in
the common trajectory once `ArrayStep`, `Solo.Encoded` etc hold. -/
def Range (S : Solo C F d) (P : Prices) (L : GridLane C m N p) (i : ℕ) (T : Stubs (L.sites i)) :=
    (∀ j, ‖(L.sites i).units j‖ ≤ payee S N p i/P.coin i) ∧
    T.funded (fun _ => 1) 0 false (payee S N p i/P.coin i)

/-- Provisional prices may be weaker than final. Local estimates: rank-2+
start and step (from fiscal on the input polynomials/copies). E.g., use
`bulk`, `flag` to require extra scale smallness of the ranks when actually
running. All separation conditions for constructing these can be reserved
on `m,r` before input. Note `hop` buys even the support exponent increase
of a step! Not licensed by same-exponent estimates alone.
-/
structure ArrayBounds (S : Solo C F d) (P : Prices) (L : GridLane C m N p) {r : ℕ} (endline : r ≤ N)
    (B : Pamphlet L r) : Prop where
  range i (h : r ≤ i) (hr : i ≤ N) : Range S P L i (B i h hr)
  seed : Mixed (B N endline le_rfl) (rent S P N p N) 0 (P.bulk N) (P.flag N)
  hop i (h : r ≤ i) (ht : i < N) : let X := hope (P.reserve i) (C.path.levels.clock.coverSize i)
                                    let w := rent S P N p (i+1)
                                    let K := B (i+1) (h.trans i.le_succ) ht
                                    (∀ j,w*‖(L.sites (i+1)).units j‖ ≤ 1) → K.funded (fun _ => w) 0 false 1 →
                                    Mixed K w 0 (P.bulk (i+1)) (P.flag (i+1)) →
    Mixed (B i h ht.le) (w/P.bill i) (P.reserve i) (X*P.bulk i) (X*P.flag i)

/-- Same whole Lane. Application of the hypothesis may use the ancestors'
separation throughout the interval. Not a choice of a visualization AFTER
taking limits.
-/
def Joint (S : Solo C F d) (P : Prices) (hm : m ≤ r) (hr : r ≤ N) (p : ℕ) :=
    ∃ L : GridLane C m N p, ArrayStep S.diff d hm hr L ∧ ∃ B : Pamphlet L r, ArrayBounds S P L hr B

variable {S : Solo C F d} {P : Prices} {L : GridLane C m N p} {hm : m ≤ r} {hr : r ≤ N}

lemma origin_bill (A : ArrayStep S.diff d hm hr L)
    (H : ticket C P.sep N p m r (hm.trans hr)) (h : C.Makes)
    (hg : ∀ i, r ≤ i → 8 ≤ C.path.levels.clock.coverSize i) (i : ℕ) (hi : r ≤ i) (ht : i ≤ N) :
    Stubs.far (A:=L.sites i) := by
  intro v w h'
  rw [show (C.path.rep N p i).p=_ from (h.wilson.represents N p i ht).vac]
  refine ⟨hg _ hi, ?_⟩
  rw [A.origin _ hi ht _,A.origin _ hi ht _]
  let k := C.path.levels.clock.coverSize i
  change k*k ≤ _
  apply Nat.cast_le (α:=ℝ) |>.1
  refine le_trans ?_ (H.2.2 i hi ht v w h')
  have he := P.separation; simp only [Nat.cast_mul]
  rw [sq]; exact le_mul_of_one_le_right (by positivity) he

variable {B : Pamphlet L r} {W : Worth}

/-- Proof on the actual arity/path. No accumulating factorial per step: use
actual factorial `grain` in the mixed tests. Restore stop order separately
when exporting each Radial. Use LOCAL bounds on rank ≥2 and G09 margins
(independent of arity) also on all single tags. -/
theorem thru (hC : C.Makes) (E : S.Encoded N p) (u : S.LocalBounds W N p)
    (H : ArrayStep S.diff d hm hr L) (G' : ArrayBounds S P L hr B)
    (g : ∀ i,r ≤ i → i ≤ N → Stubs.far (A:=L.sites i))
    (hb : roomCost C.path.levels W) (hW : Bank W C.path.levels) (hd : C.ref d ≤ r)
    (hq : ∀ i, r ≤ i → P.buys C i) : ∀ i,r ≤ i → i ≤ N →
      (L.sites i).Radial (fun _ => rent S P N p i / (((C.path.levels.params i).order).factorial:ℝ)) 1 2 2 1 := by
  let w := rent S P N p
  have hw (i) : 0 < w i := P.rate_pos (Solo.uniform_pos E)
  have single (i) (hi : r ≤ i) (ht : i ≤ N) :
      (∀ j, w i * ‖(L.sites i).units j‖ ≤ 1) ∧ (B i hi ht).funded (fun _ => w i) 0 false 1 := by
    obtain ⟨hv,hv'⟩ := G'.range i hi ht
    exact singleton_price _ (P.legal i) (escrow_pos (Solo.uniform_pos E))
      (E.coins hC u hb hW i (hd.trans hi) ht) hv hv'
  have mixed (i) (hi : r ≤ i) (ht : i ≤ N) : Mixed (B i hi ht) (w i) 0 (P.bulk i) (P.flag i) := by
    induction ht using Nat.decreasingInduction with
    | self => exact G'.seed
    | of_succ k hk ih =>
      obtain ⟨h1,h2⟩ := single (k+1) (hi.trans k.le_succ) hk
      have hp := G'.hop k hi hk h1 h2 (ih (hi.trans k.le_succ))
      have he : (C.path.rep N p k).p.B=C.path.levels.clock.coverSize k := by rw [(hC.wilson.represents N p k hk.le).vac]; rfl
      refine mixed_pay (B _ _ _) (H.label k hi hk.le) (g k hi hk.le) (div_pos (hw (k+1)) (P.bills k))
        (hw k) (P.saved k) (he.symm ▸ P.receives (Solo.uniform_pos E) (hq k hi)) ?_
      rw [he]; exact hp
  intro i hi ht
  obtain ⟨h1,h2⟩ := single i hi ht
  let T := census (Site (C.side m p))
  have hv : Stubs.Holds (L.sites i) (w i) := ⟨h1,H.label i hi ht,g i hi ht,B i hi ht,h2,Or.inl
    (mixed_funded _ _ _ _ _ (P.bulk_pay _).2 (P.flag_pay _).2 (mixed i hi ht))⟩
  have he := Work.I02.answer Work.I01.answer G _ _ T (C.path.rep N p i) (L.sites i) (w i) (hw i) hv
  have hF : (C.path.rep N p i).p.order=(C.path.levels.params i).order := by rw [(hC.wilson.represents N p i ht).vac]; rfl
  rwa [hF] at he

private lemma readable {D : Trial C} (A : ArrayStep D d hm hr L)
    (H : Interior ((center C.S p (hm.trans hr) 0).chamber 0) (D N p 0)) (s : (census (Site (C.side m p))).Mode) :
    Integrable (Ride.Product L.uses s) (law G _ (C.beta N p)) := by
  let T := center C.S p (hm.trans hr) 0
  have he (j) : Interior Set.univ (L.uses j) :=
    (A.distributed j).2.symm ▸ (T.copies j H).enlarges (Set.subset_univ _)
  exact (Interior.combines _ s.val (fun j _ => he j)).integrable _

/-- Center lane fully passes to the stopping representation. -/
theorem lane_pass (h : C.Makes) (E : S.Encoded N p) (u : S.LocalBounds W N p) (hb : roomCost C.path.levels W)
    (hW : Bank W C.path.levels) (hd : C.ref d ≤ r) (hv : ArrayStep S.diff d hm hr L)
    (hp : ArrayBounds S P L hr B) (hw : ticket C P.sep N p m r (hm.trans hr))
    (hg : ∀ i, r ≤ i → 8 ≤ C.path.levels.clock.coverSize i) (hq : ∀ i, r ≤ i → P.buys C i)
    (H : Interior ((center C.S p (hm.trans hr) 0).chamber 0) (S.diff N p 0)) :
    L.Works r ∧ ∀ i,r ≤ i → i ≤ N →
      (L.sites i).Radial (fun _ => rent S P N p i / (((C.path.levels.params i).order).factorial:ℝ)) 1 2 2 1 := by
  have he := thru h E u hv hp (origin_bill hv hw h hg) hb hW hd hq
  refine ⟨⟨hr,?_,?_,readable hv H,hv.birth,hv.sends⟩,he⟩
  · intro i hi ht; exact ⟨hv.label i hi ht,_,1,2,2,1,he i hi ht⟩
  intro i j hi ht
  rw [hv.origin _ (hi.trans i.le_succ) ht,hv.origin _ hi ht.le]
  exact hw.2.1 i (hm.trans hi) ht _
end Multi

/-- Choose this if using the  etc pricing of stops (align at the
origin; m beyond ref enough).

All fiscal requirements
in `Joint` operate on the SAME C and copies and normalization throughout
all these calls.

Proofs may assume sufficient working scale thresholds
through `m` eventuality and sufficient separation for the array down to r
.

Also need continuity after losses across many steps at same j
stage for funding `hop`. -/
def Grids (S : Solo C F d) (P : Prices) (f : Extraction.Order) :=
    ∀ᶠ m : ℕ in atTop, ∀ r, C.ref d ≤ m → ∀ h : Tabs.opens C.path.levels P.sep m r,
      f.late fun N p => ∃ hr : r ≤ N, ticket C P.sep N p m r (h.1.trans hr) → Joint S P h.1 hr p

variable {S : Solo C F d} {P : Prices} {W : Worth}

lemma many_bill (K : G.Simple) : ∀ᶠ i in atTop, 8 ≤ C.path.levels.clock.coverSize i := by
  have ht : Tendsto C.path.levels.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _
    (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos K))
  exact ht.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop 8)

/-- Issue center estimates.

Preserve the same F and C. -/
theorem grid_centers (h : C.Makes) (K : G.Simple) (ht : Tabs C.path.levels)
    (hJ : Grids S P f) (hW : S.Priced W f) (hg : roomCost C.path.levels W) (hb : Bank W C.path.levels)
    (hp : ∀ᶠ i in atTop, P.buys C i) (hF : Stencilled f F) : Centers C f S.diff d S.uniform := by
  have hs : Stencilled f S.diff := (Stencilled.upper h _).sub hF
  constructor
  intro j
  obtain ⟨m,hm⟩ := eventually_atTop.mp (((many_bill (C:=C) K).and hp).and
    (hJ.and ((eventually_ge_atTop (C.ref d)).and (eventually_ge_atTop j))))
  obtain ⟨r,hr⟩ := ht.mayOpen C.path.levels P.sep m
  obtain ⟨-,hh,hd,hj⟩ := hm m le_rfl
  let a := P.coin r / (Nat.factorial (C.path.levels.params r).order:ℝ)
  have he : 0 < a := div_pos (P.legal _) (by positivity)
  refine ⟨m,hj,r,hr.1,a,he,?_⟩
  have hv := hh r hd hr
  have hc := (Order.fused f _).mp hW.every
  have hs' := (Order.fused f _).mp (hs.fits m)
  unfold Order.late at hc hs' hv ⊢
  filter_upwards [hv,hc,hs'] with k hk hk' hk''
  filter_upwards [hk,hk',hk''] with i hi hi' hi''
  obtain ⟨hN,hv⟩ := hi
  let N := f.mesh i; let p := f.per k
  have he := Work.I03.answer G C P.sep P.separation ht m r hr _ hN p (hr.1.trans hN)
  obtain ⟨L,hE,B,hL⟩ := hv he
  obtain ⟨he',hR⟩ := lane_pass h hi'.1 hi'.2 hg hb (hd.trans hr.1) hE hL he (fun i hi => (hm i (hr.1.trans hi)).1.1)
    (fun i hi => (hm i (hr.1.trans hi)).1.2) (hi''.choose_spec 0)
  refine ⟨hr.1.trans hN,Solo.uniform_pos hi'.1,L,he',?_,fun i => (hE.distributed i).1,fun i => (hE.distributed i).2⟩
  rw [show a/escrow C N r (S.uniform (N,p))=rent S P N p r / (Nat.factorial (C.path.levels.params r).order:ℝ)
       from div_right_comm ..]
  exact
    hR r le_rfl hN
end YM.Push.RelayDifference
