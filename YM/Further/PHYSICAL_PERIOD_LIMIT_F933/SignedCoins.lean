import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.EquationFoothold
import YM.Push.RELAY_DIFFERENCE.Finite

/-!
# Spending one set of aligned transfer majorants for Compares and erased Provisions

E J154xx and comparison at d. This version asks the singular-comparison
job's `Woke` fees EARLIER at per-level `LocalBounds` (plus separate
solo RemBound). Strong enough to pay both it and the erase-Solo bills
on the *same* subtractions, with positive `total` still available for the
latter. Necessary if trying to spend the Compares work inside a RelayDifference
Provisions call; `Subtracts` alone wouldn't specify the address labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Equations
open Function Filter Set MeasureTheory Lattice RG Wilson Extraction Extraction.Lease
  Push.CutoffProjectors Push.RelayDifference Packet Source Bid
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {C : Family G} {W : Worth} {f : Extraction.Order}
  (A : Campaign C) {N p d : ℕ} (w : Campaign.Descriptions C d)

abbrev guard (_ : Campaign C) (d : ℕ) := equationSpace (C.labels.level d)
/-- The b-bound from Compares. -/
private def amount (d N p : ℕ) (w : guard A d) := 8 * (1+(C.path.levels.params N).columns) * (C.labels.level d).coeffSize ((A.packet d N p).topEquation w)
private lemma amount_nn (d N p : ℕ) (w : guard A d) : 0 ≤ amount A d N p w := by
  have h := (C.path.levels.params N).columns_ge
  have hz := coeff_pos (C.labels.level d) ((A.packet d N p).topEquation w)
  unfold amount; positivity

/-- Assigned on the very same E. Fees at levels for actual component
chain, not only in distribution norm. -/
structure Sheet (d : ℕ) where
  term (N p m : ℕ) (w : guard A d) : ℝ
  join (N p m : ℕ) (w : guard A d) : ℝ

variable (P : Sheet A d)

def billed (η : ℝ) : Solo C (A.equationTrial w) d where
  source N p m := (A.packet d N p).chain m (w (N,p))
  ticket N p m := P.term N p m (w (N,p))
  deltaFee N p m := P.join N p m (w (N,p))
  -- Strictly positive for `Encoded` even in equation rank-zero.
  total j := amount A d j.1 j.2 (w j) + η

/-- Note that `signedFee` asks on Solo.duet=combine of the actual component
chains.

Need arrange the regular addresses used by E BEFORE commissioning
this account else won't get comparison discount from triangle; and when
matching later at the Euler calls, keep this `source` for each mode together,
not separately combining `.Substracts`-witnesses of unknown alphabet.

When v
has zero top input coefficient norm, zero solo top reserves are required
(incl. forced).

On masked reads with misaligned supports, `combine`
won't give free cancellation (rightly). -/
structure Account (P : Sheet A d) (W : Worth) (N p : ℕ) : Prop where
  use : A.start d p ≤ N
  source (v : guard A d) (m : ℕ) : C.ref d ≤ m → m ≤ N →
    let Z := (A.packet d N p).chain m v
    Z.remBound 0 (C.path.rep N p m) (Real.sqrt (C.path.levels.clock.forcedAllowance m)) (P.term N p m v)
  signedFee (v : guard A d) : (billed A (fun _ => v) P 0).LocalBounds W N p
  cap (v : guard A d) : P.term N p N v + (C.labels.level d).coeffSize ((A.packet d N p).topEquation v) ≤ amount A d N p v

variable {A w P}
lemma Account.pays {η : ℝ} (H : Account A P W N p) (w : Campaign.Descriptions C d) (ha : 0 < η) :
    (billed A w P η).Encoded N p ∧ (billed A w P η).LocalBounds W N p := by
  have hv := A.uses d N p H.use
  let X := w (N,p)
  have hX := amount_nn A d N p X
  refine ⟨⟨hv.fit,fun m hm hh => hv.format m hm hh X,H.source X,?_,fun m hm hh => hv.transfer m hm hh X,add_pos_of_nonneg_of_pos hX ha,(H.cap X).trans (le_add_of_nonneg_right ha.le)⟩,?_⟩
  · intro U
    let E := A.packet d N p
    change (E.chain N _).density _ _ _ _ = ((C.S.a N:ℂ)^d) * _ * E.J _ 0 U
    rw [Packet.J,show Lattice.translate 0 U=U from by unfold Lattice.translate; simp,(A.cutoff.wilson.starts ..).2.symm,hv.encode]
  -- LocalBounds at exactly the constant letter (N,p) so is the same Duet at N p.
  constructor
  · intro i hI hi
    let v := w (N,p)
    have hs := (H.signedFee v).income i hI hi
    simpa only [Solo.duet,Solo.column,Solo.top,Solo.row,billed,v] using hs
  · intro i hI hi
    let v := w (N,p)
    have hs := (H.signedFee v).one i hI hi
    simpa only [Solo.duet,Solo.column,Solo.top,Solo.row,Solo.primaryBill,billed,v] using hs

private abbrev neutral (P : Sheet A d) (x : guard A d) (N p : ℕ) := (billed A (fun _ => x) P 0).duet N p

/-- Don't spend a positive Solo.total floor at the Compares port.
The extraction price and the top price are different. -/
lemma Account.compares (H : Account A P W N p) : (A.packet d N p).Compares W := by
  intro x
  let E := A.packet d N p
  let B := E.topEquation x
  let T := neutral P x N p
  have he η (hp : 0 < η) : T.Woke C.params W (C.localSection d) (amount A d N p x + η) :=
    let hh := H.pays (fun _ => x) hp; hh.1.woke A.cutoff hh.2
  refine ⟨T,amount A d N p x,fun m h1 h2 => ⟨rfl,?_,rfl⟩, ?_,amount_nn A d N p x,le_rfl⟩
  · exact (H.pays (fun _ => x) one_pos).1.sub A.cutoff h1 h2
  refine { he 1 one_pos with spread := ?_ }
  let A₀ := (C.path.levels.params N).columns
  have hl : Filter.Tendsto (fun q : ℝ => amount A d N p x + q + A₀*
      (amount A d N p x+q+ (C.labels.level d).coeffSize (T.voice N).x)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝
        (amount A d N p x + A₀*(amount A d N p x + (C.labels.level d).coeffSize (T.voice N).x))) := by
    set a := (C.labels.level d).coeffSize (T.voice N).x
    conv_rhs => rw [← add_zero (amount A d N p x)] -- adds at first or all?
    exact ((continuousAt_const.add continuousAt_id).add
      (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).add continuousAt_const))
        : ContinuousAt (fun q : ℝ => amount A d N p x + q + A₀*(amount A d N p x+q+a)) 0).continuousWithinAt (s:=Set.Ioi 0)
  exact ge_of_tendsto hl (eventually_nhdsWithin_of_forall fun t ht => (he t ht).spread)

lemma sized (b : ℕ → ℕ → ℝ) (hn : ∀ N p,0≤b N p) (h : Subexp C f b) : Slow C f fun i => b i.1 i.2 := by
  intro η hη
  rw [Extraction.Order.fused]
  simpa only [flight,Real.norm_of_nonneg (hn _ _)] using h η hη

lemma needle_description (A : Campaign C) (j : Fields C d) : ∃ w : Campaign.Descriptions C d,
    needles A.presentation d j = A.fromRow w := by
  have hx (i : Cutoffs) := (A.equation_iff_zero (N:=i.1) (p:=i.2) (needles A.presentation d j i)).1 (needles_drop ..)
  choose w hw using hx
  exact ⟨w,funext fun i => (hw i).symm⟩

variable (w : Campaign.Descriptions C d)

lemma solo_price (hb : Bank W C.path.levels) (hh : roomCost C.path.levels W)
    (h : f.late fun N p => Account A P W (d:=d) N p) (hr : dollar C f (A.fromRow w)) :
    (billed A w P 1).Priced W f := by
  have he : f.late fun N p => (A.packet d N p).Compares W := h.mono fun i hi => hi.mono fun _ hh => hh.compares
  have hv := Campaign.top_budget hb hh he w hr
  have hl := (sized (C:=C) (f:=f) (fun N p => (C.labels.level d).coeffSize ((A.packet d N p).topEquation (w (N,p)))) (fun i j => coeff_pos (C.labels.level d) ((A.packet d i j).topEquation (w (i,j)))) hv)
  have hA : Slow C f fun i => 1+(C.path.levels.params i.1).columns :=
    sized (C:=C) (f:=f) (fun N _ => 1+(C.path.levels.params N).columns) (fun N _ => add_nonneg zero_le_one (zero_le_one.trans (C.path.levels.params N).columns_ge)) (subexp_columns C f)
  exact ⟨(((Slow.const (C:=C) (f:=f) (8:ℝ)).mul hA).mul hl).add (Slow.const (C:=C) (f:=f) (1:ℝ)),
    ((Extraction.Order.fused f (fun j => Account A P W (d:=d) j.1 j.2)).mpr h).mono (by rintro ⟨N,p⟩ hi; exact hi.pays w one_pos)⟩

variable (A : Campaign C) (P : Sheet A d)

/-- PhysicalPeriodLimitF933 input per erased basis and weight lift (the remaining
Solo/copy propagation and estimate gates; NO exactOnSep or rank assumption).
Only one common campaign. Can move further DOWN from Provisions on lift/pace
(e.g. choosing Solo on the source-print recursion) when available. Here
no deriving it from emergence of fields in a different history. -/
structure Invoices (d : ℕ) (P : Sheet A d) (f : Extraction.Order) (W : Worth) : Prop where
  paper : f.late fun N p => Account A P W N p
  erase (i : Fields C d) (w : Campaign.Descriptions C d) :
    -- w needn't be bounded without an extra Separation purchase; but these
    -- specific ones are if needed (Subexp A from `preimage_budget`)
    needles A.presentation d i = A.fromRow w →
    ∃ Q : Push.RelayDifference.Prices, Grids (billed A w P 1) Q f ∧ ∀ᶠ i in atTop, Q.buys C i
  lift (e : ℕ) : e < d → ∀ i : Fields C e, ∃ T : Solo C (Bid.visits C e (needle C e i)) d, Provisions T W f
  farther (a : Axis) (i : Fields C d) : ∃ T : Solo C (Bid.heighten C d (needle C d i) a) (d+1), Provisions T W f

lemma Invoices.purchased (hb : Bank W C.path.levels) (hh : roomCost C.path.levels W) (hp : Invoices A d P f W) : Tickets A.presentation f W d := by
  refine ⟨fun j => ?_,hp.lift,hp.farther⟩
  obtain ⟨w,hw⟩ := needle_description A j
  obtain ⟨a,b⟩ := delivers (f:=f) A w
  exact ⟨_,a,b,billed A w P 1,hw ▸ .of_forall (fun (_ : Cutoffs) => rfl),
    solo_price w hb hh hp.paper (hw ▸ needles_pay A.presentation j),hp.erase j w hw⟩

end YM.Further.PhysicalPeriodLimitF933.Equations
