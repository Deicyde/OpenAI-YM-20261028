import YM.Pressure.Rows

/-!
# Single oriented sector

Seeds ARE records, even if coincident, and actual flags are tested. Assumes
only local pattern through H5 (written pointwise, even when differentiated
with sector indicators fixed). Regions use true projected location incl
incident sites for component definition. A.Written covers candidates isolated
in any other components; all rows of the oriented channel whose ANCHORS
lie in twoB are paid by A. Does not need threshold on input X,I outside. Use
only cuts; projection marks affine subtractions occur elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ComplexOrder

variable {G : Gauge} {c f : Side}

def radiusB (x : ℝ) := Nat.ceil ((Real.log x)^2)
def betaF (G : Gauge) (x : ℝ) (L : Side) := x+G.slopeConstant*Real.log L.val

def temp (x : ℝ) := (Real.sqrt x)⁻¹ * Real.exp ((Real.log (Real.log x))^2)
def fiery (G : Gauge) (x : ℝ) (L : Side) := temp (betaF G x L)
def largeT (G : Gauge) (x : ℝ) (L : Side) := ((Real.sqrt (betaF G x L))⁻¹)^((98:ℝ)/100)

variable (S : StepData c f)

def startPos (x : Cell f) := (touched x).image S.ratio.parent
def pinPos (x : Bond c) : Support c := {x.1,x.1 + step x.2}

structure Stores (S : StepData c f) where
  costs : Finset (Cell f)
  aisles : Finset (Bond c)
  flags : Support c

namespace Stores
variable {S} (A : Stores S)

def place := A.costs.biUnion (startPos S) ∪ A.aisles.biUnion pinPos ∪ A.flags

def dome (b : ℕ) := halo b A.place

def shares := A.costs.card + A.aisles.card + A.flags.card

def SliceSet (S : StepData c f) (F : Forest S.ratio) (U : Config G f) := ∀ e∈F.trunks,U e=1

-- choose ϑ=1/4 for these estimates. REAL margins. x = coarse HAT.
structure Plot (U : Config G f) (k : S.Choices) (V : Config G c) (x w : ℝ) : Prop where
  consumes : ∀ p, ¬ Disjoint (A.dome (5*radiusB x)) (startPos S p) →
      ((p ∈ A.costs → fiery G x S.patch.L/4 ≤ toll U p) ∧ (p∉A.costs → toll U p ≤ fiery G x S.patch.L/2))
  drive b : ¬ Disjoint (A.dome (5*radiusB x)) (pinPos b) →
      ((b ∈ A.aisles → w*fiery G x S.patch.L ≤ wire (S.prediction U k) V b) ∧
      (b∉A.aisles → wire (S.prediction U k) V b ≤ 2*w*fiery G x S.patch.L))
  precise i : i∈A.dome (5*radiusB x) → (i∈A.flags ↔ i∈RG.flags (temp x) V)
  list i : i∈A.dome (5*radiusB x) → 0<S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i)

def limit (x : ℝ) := (univ : Finset (Cell f)).filter fun a => S.ratio.parent a.1 ∈ A.dome (2*radiusB x)
def outs (x : ℝ) := (univ : Finset (Cell c)).filter fun a => a.1∈A.dome (2*radiusB x)
def intern (x : ℝ) := (univ : Finset (Bond c)).filter fun a => a.1∈A.dome (2*radiusB x)
def coordN (x : ℝ) := (univ : Finset (Co c Gain)).filter fun i => i.1∈A.dome (2*radiusB x)
def swell (U : Config G f) (x : ℝ) := A.costs.filter fun p => x<toll U p
def drives (Q V : Config G c) (x : ℝ) := A.aisles.filter fun p => x<wire Q V p

def spend (U : Config G f) (Q V : Config G c) (x : ℝ) : Stores S :=
    { A with costs := A.swell U (largeT G x S.patch.L), aisles := A.drives Q V (largeT G x S.patch.L), flags := ∅ }

def tides (V : Config G c) (x : ℝ) (δ : ℝ) := (A.outs x).filter fun p => toll V p>δ

def hit (U : Config G f) (Q V : Config G c) (x : ℝ) :=
    (A.outs x).filter fun i => i.1∈(A.spend U Q V x).dome (4*radiusB x/5)

variable (T : Tube G S) (x : ℝ) (U : Config G f) (Q V : Config G c)

def till := radiusB x/100000

def tally := ∑ i∈A.limit x, T.workF (till x) U V (fiery G x S.patch.L) (temp x) i
def talli := ∑ i∈A.intern x,T.workI (till x) Q V (temp x) i
def tallc := ∑ i∈ A.outs x,T.workC (till x) V (temp x) i
def talln := ∑ i∈ A.coordN x,T.workN (till x) V (temp x) i
def talll (s : Finset (Cell c)) := ∑ i∈ s,(T.workL (till x) U Q V (temp x) i+T.workD (till x) V (temp x) i)

def assessed := A.tally T x U V + A.talli T x Q V + A.tallc T x V + A.talln T x V + talll T x U Q V (A.outs x)
end Stores

/-- One call, prices & inputs. Price is pre-L in all requirements. -/
structure Teller (G : Gauge) where
  bind : KernelChoices
  top : Stage
  below : Stage
  j : ℕ
  η : ℝ
  C : ℝ
  width : 0 < η

namespace Teller
variable (P : Teller G)

structure Funds {c f : Side} (S : StepData c f) (T : Tube G S) : Prop where
  knobs : S.kernel=P.bind
  atStep : S.patch.J=P.j
  kernel : S.patch.Branches P.bind G
  crosses : T.R.Deep P.η P.C (P.j-2)
  low : T.low=P.below.clip
  high : T.high=P.top.clip
  feeds : ∃ a b,T.up.Bounds P.top.clip P.top.width P.top.paths a ∧ T.down.Bounds P.below.clip P.below.width P.below.paths b
  tilts : ∃ H H', Attached H T.up ∧ Attached H' T.down ∧ Towers.Roll S H H' T.R T.high T.low

/-- trigger work through `Beta` monitor: proof for all sufficiently large
coarse HAT protocol; wait threshold independent actual period. This stronger
request uses only outputs in this Teller (other args in hypotheses). -/
def live (L : Side) (W : ℝ) (Q : ∀ {c f : Side}, (S : StepData c f) → Tube G S → Forest S.ratio → Stores S → ℝ →
    Config G f → S.Choices → Config G c → Prop) (x : ℝ) := ∀ (c f : Side) (S : StepData c f), S.patch.L=L →
    100*(1+radiusB x) ≤ c.val → ∀ T : Tube G S, P.Funds S T →
    ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      Stores.SliceSet S F U → Stores.Plot A U k V x W → Q S T F A x U k V

structure Serves (L : Side) (W : ℝ) (Q : ∀ {c f : Side}, (S : StepData c f) → Tube G S → Forest S.ratio → Stores S → ℝ →
    Config G f → S.Choices → Config G c → Prop) : Prop where
  late : ∀ᶠ x : ℝ in atTop, live P L W Q x

def cash (L : Side) (W κ : ℝ) := P.Serves L W fun S T _ A x U k V =>
      κ*(fiery G x L)^2 * A.shares ≤ A.assessed T x U (S.prediction U k) V

/-- energy per seed, before tails in output channels and before reusing
Θ for any E input extension. This alone NOT enough to start expansion. -/
structure Grants (P : Teller G) : Prop where
  precedes : ∃ i : ℕ, ∀ L : Side, i ≤ L.val → ∀ᶠ W : ℝ in atTop,
    ∃ κ : ℝ, 0<κ ∧ P.cash L W κ
end Teller

open Input
namespace Testing
variable {C : Supply.Sheet G} {D : Supply.Rolls C} {Θ : Supply.Protection D} {W : Supply.Delays Θ}
variable {Y : Supply.Bar W} {I : Supply.Wait Y}
variable {Z : ChartRatio G} {K : MapPrices} {Q : PostCost D} (B : Directed G I Z K Q)

-- This choice pre-L. Supply.P.Budget.closed

def query {G : Gauge} (C : Supply.Sheet G) (K : MapPrices) (j i : ℕ) : Teller G := ⟨C.kernel,C.profile j,C.profile i,j,K.α j,K.Ω j,K.alpha_pos j⟩

def ships (N i p : ℕ) : Tube G (B.a.clock.op i p) :=
    ⟨B.M.towers N i, B.kin.path N (i+1), (B.a.params (i+1)).clip, B.kin.path N i, (B.a.params i).clip⟩

lemma proceeds (N i p : ℕ) (hh : i<N) : Teller.Funds (query C K (B.a.clock.J (i+1)) (B.a.clock.J i)) _ (ships B N i p) := by
  have hx := B.valid
  refine ⟨hx.kernel,rfl,C.has _, B.plan.costs N i hh,?_,?_,?_,⟨_,_,B.support.links N (i+1) hh,B.support.links N i hh.le,B.plan.stack N i p hh⟩⟩
  · unfold ships query; simp only [Levels.params,Calendar.params,hx.stage]
  · unfold ships query; simp only [Levels.params,Calendar.params,hx.stage]
  unfold query ships; simp only [← hx.stage]; exact ⟨_,_, B.support.cap N (i+1) hh,B.support.cap N i hh.le⟩

-- called by upstream `Move` producer, not baking m separately per period.
structure Stamp {p : Supply.Sheet G} {D : Supply.Rolls p} (K : MapPrices) (j old : ℕ) (w x : ℝ) : Prop where
  pos : 0<w
  commission : ∃ μ, 0<μ ∧ ∀ b, x ≤ b → Teller.live (query p K j old) (D.L j) w (fun S T _ A x U k V =>
      μ*(fiery G x (D.L j))^2 * A.shares ≤ A.assessed T x U (S.prediction U k) V) b

-- Pre-L W0 not required, choose W.stage. For all pairs of adjacent ones.
structure Ringing {p : Supply.Sheet G} {D : Supply.Rolls p} {Θ : Supply.Protection D} (K : MapPrices)
    (H : ℕ → ℕ → ℝ) (W : Supply.Delays Θ) : Prop where
  receipts (j i : ℕ) (h : j ≤ i) (he : i ≤ j+1) (a : p.first ≤ j) : Stamp (D:=D) K i j (H i j) (W.betaEntry i)

/-- Use at exact Move location, outputs µ with currency through valuation. -/
lemma notation_ticket (K : MapPrices) (B : Directed G I Z K Q) (F : ℕ → ℕ → ℝ) (H : Ringing K F W) (j i : ℕ) (u : C.first ≤ i) (h : i ≤ j) (hv : j ≤ i+1) :
    ∃ μ : ℝ, 0<μ ∧∀ N m p : ℕ, m<N → B.a.clock.J (m+1)=j → B.a.clock.J m=i →
    let S := B.a.clock.op m p; let T := ships B N m p
    ∀ (X : Stores S) (Y : Config G _) (V : Config G _) (k : S.Choices) (A : Forest S.ratio), Stores.SliceSet S A Y →
      Stores.Plot X Y k V (B.a.clock.hatBeta m) (F j i) →
      μ*(B.a.clock.threshold (m+1))^2*X.shares ≤ X.assessed T (B.a.clock.hatBeta m) Y (S.prediction Y k) V := by
  obtain ⟨μ,hp,hZ⟩ := (H.receipts i j h hv u).commission
  refine ⟨μ,hp,?_⟩
  intro N m p hk ht hs S T X Y V k A Ha Hb
  have he : S.patch.L=D.L j := (B.a.fits.sameFactor m).symm.trans ((congr_fun B.valid.lengths _).trans (congr_arg D.L ht))
  have hy := proceeds B N m p hk; rw [ht,hs] at hy
  have hh := hZ (B.a.clock.hatBeta m) (ht ▸ B.valid.pays m) _ _ S he
    (show 100*(1+radiusB _ ) ≤ (B.a.S.side _ _).val by rw [add_comm 1]; exact B.a.fits.sizeT m p) T hy A X Y k V Ha Hb
  have hx : B.a.clock.hatBeta (m+1)=betaF G (B.a.clock.hatBeta m) (D.L j) := by unfold Calendar.hatBeta betaF; rw [Schedule.scale_succ,← he]; change _=_+_ * Real.log (B.a.clock.schedule.block m).val; ring
  change μ*(temp _)^2*X.shares ≤ X.assessed T (B.a.clock.hatBeta m) _ _ _
  rw [hx]; exact hh
end Testing
end YM.Pressure
