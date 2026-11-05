import YM.Integrated
import YM.Next.SCHEDULE.Salary

/-!
# Post-L hardware and delay issuance, before choosing a Bar

Choose `Beam` before any trajectory, before assigning `Postage` bills.
`Radios.transmit` opt-in (`PreGrant` available, conditional). Choose
protection AFTER all post-L powers. Regime carries post prices and band
delay incl startup; boosting after that allowed for further receipts,
even individual scaleEntry requirements (all entered after preceding
plateau), but still first-stage scale NOT tending to infinity. Paid Wait etc
later. No Directed, nor assumption that the bounds anticipated in Fees
are actual estimates. See application lemmas with those as input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter RG RG.Supply Function Precision Input Bid Lattice Pressure Pressure.Testing Source

variable {G : Gauge}

/-- The χ quotation at station chosen before any particular W's or work
steps. Uniform in admissible side, `Larger` priced too. -/
structure Beam {s : Sheet G} (K : MapPrices) (D : Rolls s) where
  η : ℕ → ℝ
  custody j : 0<η j
  uses j (c f : Side) (S : StepData c f) : S.kernel=s.kernel → S.patch.L=D.L j → S.patch.J=j → Larger (G:=G) S →
    ∀ (H : Tree.Forest S.ratio) (B C : Bed) (p q : Clip) (W : PathData G) (σ c₀ Λ m v u : ℝ) (T : Towers S.patch.L),
        Towers.Diagonal S B C T → Floor B p f (K.η j) m → W.Bounds p σ c₀ Λ → Attached B W → Sworn B f G →
          Floor C q c v u → PriceGap H p W (η j) ∧ ∃ ρ,Critical H p W ρ ∧ Guessed H (Bloch.installed S.ratio T.A0) ρ ∧ HeatG H p W ρ C

namespace Beam
variable {s : Sheet G} {K : MapPrices} {D : Rolls s}

theorem alight (K : MapPrices) (D : Rolls s) : Nonempty (Beam K D) := by
  choose η h hη using fun j => (Integrated.stationary_scene (G:=G) (D.L j) j s.kernel (K.η j) (K.eta_pos j)).χ
  exact ⟨η,h,hη⟩

/-- C3 after-cost fields. Take larger coeff and worst rates (minimum)
between the two calls. FiniteBound caps require Γ independently of volume.
-/
def price (B : Beam K D) (F : ℕ → ℕ → Postage) : PostCost D where
  η := B.η
  Γ i := max (F i i).H (F i (i-1)).H
  c i := min (F i i).rate (F i (i-1)).rate
  g i := min (F i i).rate (F i (i-1)).rate/8
  price := B.custody
  pos i := lt_of_lt_of_le zero_lt_one (le_max_of_le_left ((F i i).h_ge))
  posC i := lt_min (F i i).pos (F i (i-1)).pos
  posG i := div_pos (lt_min (F i i).pos (F i (i-1)).pos) (by norm_num)

lemma leg (B : Beam K D) (F : ℕ → ℕ → Postage) {j i} (h : Adj j i) :
    (F j i).H ≤ (B.price F).Γ j ∧ (B.price F).c j ≤ (F j i).rate ∧ (B.price F).g j ≤ (F j i).rate/8 := by
  rcases h.cases_back with rfl|rfl
  · exact ⟨le_max_left ..,min_le_left ..,div_le_div_of_nonneg_right (min_le_left ..) (by norm_num)⟩
  exact ⟨le_max_right ..,min_le_right ..,div_le_div_of_nonneg_right (min_le_right ..) (by norm_num)⟩
end Beam

/-- Arbitrariness BEFORE scheduling, componentwise. Not Paid monotonicity
if Bar would have to change! Use before Wait is fixed. -/
structure Boost {s : Sheet G} {D : Rolls s} {T : Protection D} (V W : Delays T) : Prop where
  beta : V.betaEntry ≤ W.betaEntry
  scale : V.scaleEntry ≤ W.scaleEntry
  shells : V.shells ≤ W.shells
  power : V.growth ≤ W.growth

lemma Boost.chain {s : Sheet G} {D : Rolls s} {T : Protection D} {V W W' : Delays T}
    (h : Boost V W) (hx : Boost W W') : Boost V W' :=
  ⟨h.beta.trans hx.beta,h.scale.trans hx.scale,h.shells.trans hx.shells,h.power.trans hx.power⟩

lemma Boost.priced {s : Sheet G} {D : Rolls s} {T : Protection D} {V W : Delays T}
    (h : Boost V W) (hx : Stock.Priced V) : Stock.Priced W :=
  ⟨fun j hj x hx' => hx.1 j hj x ((h.beta j).trans hx'), fun j hj a s hs he => hx.2 j hj a s hs ((h.scale j a).trans he)⟩

open Finset in
/-- Minimum shell floor to pay ALL stencils (even before a k-grid choice).
Enlargements specified with further `shells,growth` requests after L.
-/
def entrance (s : Survey G) (j : ℕ) :=
    (range (j+1)).sup (fun d => (s.B.entry d).stencil.sup fun x => univ.sup fun i => 20*((x i).natAbs+1))

/-- constant shell floor to put every larger-patch theorem on the same torus. -/
def required (j : ℕ) (L : ℕ) : ℕ := 100*((j+3)*L+4*L)+2

variable {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D}

def Duo (B : Beam K D) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (Θ : Protection D)
    (j i : ℕ) (c x : ℝ) :=
    BandGate s q (e j i) Instrument.plain (F j i) j i (D.L j).val (Θ.theta j) (Θ.theta i) ((B.price F).g j) c x ∧
    BandGate s q (e j i) Instrument.chorus (F j i) j i (D.L j).val (Θ.theta j) (Θ.theta i) ((B.price F).g j) c x

/-- Numeric results before a Bar. -/
structure Regime (B : Beam K D) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (V : Delays Θ) : Prop where
  prices : Stock.Priced V
  starts j : ∀ x ≥ V.betaEntry j, Duo B e F Θ j j 0 x
  all j i : Adj j i → ∀ x ≥ V.betaEntry j, Duo B e F Θ j i (G.slopeConstant * Real.log (D.L j).val) x
  big j : required j (D.L j).val ≤ V.shells j ∧ entrance s j ≤ V.shells j

lemma Regime.carry {B : Beam K D} {F : ℕ → ℕ → Postage} {V W : Delays Θ} (g : Regime B e F V) (h : Boost V W) : Regime B e F W :=
  ⟨h.priced g.prices,fun i b hh => g.starts i b ((h.beta i).trans hh),
    fun j i hx b hh => g.all j i hx b ((h.beta j).trans hh),
    fun j => ⟨(g.big j).1.trans (h.shells j), (g.big j).2.trans (h.shells j)⟩⟩

/-- Two calls to `BandGate.authorize`, different threshold shape
(same hatted β). -/
lemma Duo.sample (B : Beam K D) (F) (Θ : Protection D) (hw : ∀ i, Θ.theta i ≤ 1)
    (h : Prepaid s K q e v) (j i) (hh : Adj j i) (c : ℝ) : ∀ᶠ x in atTop,Duo B e F Θ j i c x := by
  let P := B.price F
  have he (M : Instrument) : ∀ᶠ x in atTop,
      BandGate s q (e j i) M (F j i) j i (D.L j).val (Θ.theta j) (Θ.theta i) (P.g j) c x :=
    BandGate.authorize j i _ _ _ _ c (h.each D j i hh) (Θ.pos j) (Θ.dec hh.1) (hw j) (P.posG j) (B.leg F hh).2.2
  exact (he Instrument.plain).and (he Instrument.chorus)

/-- Existence and upgrade over all bill requests phrased in `Delays`. May
therefore use with any other *post-L* β bills (e.g. threshold for the o_L term
in a transition, simultaneous restart data). -/
lemma Regime.issue (Gsimple : G.Simple) (B : Beam K D) (F : ℕ → ℕ → Postage)
    (hw : ∀ i, Θ.theta i ≤ 1) (V : Delays Θ) (h : Prepaid s K q e v) :
    ∃ W : Delays Θ, Boost V W ∧ Regime B e F W := by
  let c j := G.slopeConstant * Real.log (D.L j).val
  have hh := fun i j hg u => Duo.sample B F Θ hw h i j hg u
  have hi (j : ℕ) : Adj j j := ⟨le_rfl,Nat.le_succ _⟩
  have hj (j : ℕ) : Adj j (j-1) := by constructor <;> omega
  choose x hx using fun j => eventually_atTop.1 <| ((hh j j (hi j) (0:ℝ)).and
    ((hh j j (hi j) (c j)).and (hh j (j-1) (hj j) (c j))))
  let W : Delays Θ := { V with
    betaEntry := fun j => max (V.betaEntry j) (x j)
    shells := fun j => max (V.shells j) (max (required j (D.L j).val) (entrance s j)) }
  obtain ⟨U,hb,hv,hs,hg,Hu⟩ := Stock.raises W Gsimple
  have hU : Boost V U := Boost.chain (W:=W) ⟨fun i => le_max_left ..,le_rfl,fun i => le_max_left ..,le_rfl⟩ ⟨hb,hv,hs.le,hg.le⟩
  have hJ (j) (b : ℝ) (h : U.betaEntry j ≤ b) := hx j b ((le_max_right ..).trans ((hb j).trans h))
  refine ⟨U,hU,Hu,fun j b hh => (hJ j b hh).1,?_,?_⟩
  · intro j i hh b hV; rcases hh.cases_back with hi | hi <;> subst i
    · exact (hJ j _ hV).2.1
    exact (hJ j _ hV).2.2
  intro j; rw [← hs]; exact ⟨le_max_of_le_right (le_max_left ..),le_max_of_le_right (le_max_right ..)⟩

/-- Relative to RStep proofs needing Ringing. Use any actual prior
Radio assignment. -/
def Transmitting (R : Radios K D) (V : Delays Θ) := ∀ j i, Adj j i → R.floorBeta j i ≤ V.betaEntry j

lemma Transmitting.ringing {R : Radios K D} {V : Delays Θ} (h : Transmitting R V) : Ringing K R.W V :=
    ⟨fun i j ha hb hc => ⟨R.station _ _, R.strength j i, R.sound _ _, fun b ht =>
      R.reaches j i ⟨ha,hb⟩ hc b ((h j i ⟨ha,hb⟩).trans ht)⟩⟩

lemma Radios.transmit (Gsimple : G.Simple) (B : Beam K D) (F) (hw : ∀ i, Θ.theta i ≤ 1)
    (h : Prepaid s K q e v) (R : Radios K D) (V : Delays Θ) :
    ∃ W : Delays Θ, Boost V W ∧ Regime B e F W ∧ Transmitting R W := by
  let Q : Delays Θ := { V with betaEntry := fun i => max (V.betaEntry i) (max (R.floorBeta i i) (R.floorBeta i (i-1))) }
  obtain ⟨W,H,hW⟩:=Regime.issue Gsimple B F hw Q h
  refine ⟨W, Boost.chain (W:=Q) ⟨fun j => le_max_left ..,le_rfl,le_rfl,le_rfl⟩ H,hW,fun j i hz => le_trans ?_ (H.beta j)⟩
  refine le_max_of_le_right ?_; rcases hz.cases_back with h|h <;> subst i
  · exact le_max_left ..
  exact le_max_right ..

/-- The ceiling `a` is arbitrary and may include all the requested post-L
powers for that pair of neighboring profiles (Λ envelope work). -/
lemma temper {P : Sheet G} (D : Rolls P) (a : ℕ → ℝ) (hh : ∀ j,0<a j) :
    ∃ Θ : Protection D,(∀ i, Θ.theta i ≤ 1) ∧ ∀ i, Θ.theta i ≤ a i := by
  obtain ⟨Θ,hΘ⟩ := Protection.exists_margin D (fun i => min 1 (a i)) fun i => lt_min zero_lt_one (hh i)
  exact ⟨Θ,fun i => (hΘ i).trans (min_le_left ..), fun i => (hΘ i).trans (min_le_right ..)⟩
end YM.Next.Scheduling
