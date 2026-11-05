import YM.AnalyticNext.CUBIC_MATCH.Remainder

set_option warningAsError false

/-!
# Budget the incoming and outgoing widths

No hidden dependence on figures when buying
emitting widths. Include the worst-case path estimate for cubic payment
(including self→self) in `Figures`. Also retain the *intrinsic* price
`changeBill` and width `coupon.σ` prior to compiling estimates together;
they can be useful in bidding downstream (in particular an output service
can further thin `emits` to pay for quartic work with these paths).

Scalar direct and K locked. Can take `finish` after these (incl selector
relaxation). These are pre-quotes that suffice for the cubic items. Payment
for all desired **other** physics does NOT follow from this interface.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch.Ledger
open Function Filter Lattice Laurent RG Precision Exterior Bid Next
open YM.Progress.StationaryScenes YM.Progress.Joint
open Next.Scheduling
open scoped Topology ContDiff BigOperators

variable {G : Gauge}

/-- Rates from K. Don't charge the row at the maximum working cap. `scribe`
paths give this regardless of the other arrays. -/
def border (K : MapPrices) (j : ℕ) := min 1 (K.α j)
lemma border_pos (K : MapPrices) (j : ℕ) : 0 < border K j := lt_min zero_lt_one (K.alpha_pos _)


/-- Upstream contour request to estimate the difference (coarse units).
Positive before ANY L costs. -/
def surplus (K : MapPrices) (j i : ℕ) := min (border K j) (border K i)/4
lemma surplus_pos (K : MapPrices) (j i : ℕ) : 0 < surplus K j i := div_pos (lt_min (border_pos K j) (border_pos K i)) (by norm_num)




/-- Keep prices even after joint calendar demands. -/
def reserve (K : MapPrices) (j : ℕ) := max 1 (K.Ω j)


def startNum (G : Gauge) (K : MapPrices) (d : ℝ) (j : ℕ) := crestPrice G (surplus K j j) (rowBill K j) (border K j) d


def stableNum (G : Gauge) (K : MapPrices) (d u k : ℝ) (j i : ℕ) :=
    preCover G (surplus K j i) (reserve K j) (rowBill K j) (rowBill K i) (border K j) (border K i) d u k j

def coarseNum (K : MapPrices) (j i : ℕ) := fineCap (reserve K j) (surplus K j i)



structure Coupon (G : Gauge) (θ : ℝ) where
  σ : ℝ
  A : ℝ
  width : 0<σ
  price : 0<A
  tear (n : ℕ → Side) : Tendsto (fun i => (n i).val) atTop atTop → ∀ (q : Clip) (P : PathData G) b v z,
    P.Bounds q b v z → ∀ F : ∀ i, Dir G (n i) → ℝ, (∀ i,Checks (n i) (F i)) →
    (∀ i, SameJet 1 (F i) (baseline q P)) → (∀ i, SameJet 2 (F i) (baseline q P)) →
    ∀ C : ℝ, TotalRep n 3 θ C (fun p x => term 3 (fun t : ℝ => (F p-baseline q P : Dir G (n p) → ℝ) (t • x))) →
      ∃ R : ℕ → Atom G 3, Flies σ (A*C) R ∧ ∀ σ B Λ (T : PathData G), T.Bounds q σ B Λ → T.row=P.row → T.cubic=R →
        ∀ i, SameJet 3 (F i) fun x => mainTerm q T (represent x)

lemma available (G : Gauge) {θ : ℝ} (h : 0<θ) : Nonempty (Coupon G θ) := by
  obtain ⟨σ,A,hσ,hC,hB⟩ := invoice G h
  exact ⟨⟨σ,A,hσ,hC,hB⟩⟩

def ticket (G : Gauge) (K : MapPrices) (j i : ℕ) : Coupon G (surplus K j i) :=
    Classical.choice (available G (surplus_pos K j i))

variable {s : Survey G} {q : Quote} {K : MapPrices}

/-- usable *before* `finish`. -/
def initialBill (G : Gauge) (K : MapPrices) (d : ℝ) (j : ℕ) := (ticket G K j j).A * startNum G K d j





def stageFee (G : Gauge) (K : MapPrices) (d u k : ℝ) (j i : ℕ) :=
    (ticket G K j i).A * max (stableNum G K d u k j i) (coarseNum K j i)



/-- Sufficient pre-L bids *for this construction*. `d` from the actual melt's direct, k actual kernel penalty.
Obtain these estimates even before finishing other bids. Don't assume monotonicity of any other estimates. -/
structure InTill (G : Gauge) (K : MapPrices) (d : ℕ → ℝ) (k : ℝ) (q : Quote) : Prop extends Designing K q where
  first j : q.widths.launch j ≤ (ticket G K j j).σ
  issues j i : Adj j i → q.widths.emits j i ≤ (ticket G K j i).σ
  mounts j i : Adj j i → surplus K j i ≤ q.widths.loads j i
  once j : initialBill G K (d j) j ≤ q.classicalCost.beginCost j
  transfers j i : Adj j i → stageFee G K (d j) (d i) k j i ≤ q.classicalCost.classic j i











variable {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
open RG.Supply
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {a : Levels G}





end YM.CubicMatch.Ledger
