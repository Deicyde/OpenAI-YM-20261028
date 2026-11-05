import Mathlib.Analysis.ODE.ExistUnique
import YM.Next.RANK.Coordinates
import YM.Next.RANK.Stamp
import YM.Next.RANK.StationMeter

/-!
# One E A comparison demand

The stopping (few marks per cell) query asks for local estimates on the
unnormalized marker density after exact push along `c`. Indexing: given
k fixed (level **number**, may not be cutoff), p actual period NUMBER,
N cutoff, l/m the middle and width determined by A.height/surplus at k.
`M` is the hard maximum slots per probes cell, independent of periods and
size of torus. All witnesses from the same ledger. Explicit even level m
where restoration has to pay k markers. No labels forgotten to a future
`S` until the output of these methods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ship
open Function Set Filter RG MeasureTheory Wilson Cells Glyph Exponential Lattice Read Station
open scoped Topology BigOperators

variable {G : Gauge} (A : Levels G) (M k : ℕ)

def pot := Real.log (A.clock.monitor k)/(16*M)
def allowance := Real.exp (2*pot A M k)
def budget := Real.exp (-pot A M k)

lemma fixed : 1 ≤ allowance A M k := Real.one_le_exp (by
  have hz : 1 ≤ A.clock.monitor k := Real.one_le_exp (sq_nonneg _)
  have he := Real.log_nonneg hz; dsimp only [pot]; positivity)
lemma budget_pos : 0 < budget A M k := Real.exp_pos _
lemma diminishes (h : G.Simple) (hm : 0<M) : Tendsto (budget A M) atTop (𝓝 0) := by
  have hx : Tendsto A.clock.monitor atTop atTop := (Station.mag_rate A h (show (0:ℝ)<1 from zero_lt_one)).congr (fun i => Real.rpow_one _)
  have he : Tendsto (pot A M) atTop atTop := (Real.tendsto_log_atTop.comp hx).atTop_div_const (by positivity : 0 < 16*(M:ℝ))
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr he)

-- Needed universally only at the memory allocation for *this* query; entirely numeric.
def bank (O : HaarBudget G) (A : Levels G) (m : ℕ) : Prop := ∀ p (P : Rep G (A.S.side m p)) (g Λ δ X : ℝ) (k : ℕ),
    Station.Meets A m p P g Λ δ → X ≤ 1+k → protection O P (A.params m).paths Λ δ X g - 4*G.lieDim*Real.log g/(Fintype.card (Site (A.S.side m p)):ℝ) ≤ ticket O (A.params m) k
lemma banking (O : HaarBudget G) (h : G.Simple) : ∀ᶠ m in atTop, bank O A m := Station.affordable O A h

-- Bench allocation before usage. Also paying *other* numerical and estimate gates
-- at C is still needed in practice! RRequirements.
structure Allocated (O : HaarBudget G) (b : ℝ) : Prop where
  permitted : Allowed A b k
  charge : ticket O (A.params k) M ≤ pot A M k

variable {C : Family G} (b : ℝ)

def yard (C : Family G) {k N : ℕ} (b : ℝ) (hN : k ≤ N) (p : ℕ) : Tiling (C.side N p) :=
  let A := C.path.levels
  center C.S (m:=width A b k) p (((Station.wider A b k).trans (before A b k)).trans hN) 0


section
variable {M k b} {N p m n : ℕ} {x : Points n}

lemma fitting {a : Levels G} (h : Fit a b k x) : tested a b k x ∈ conf _ := by
  apply generic_conf
  exact Market.vision _ (inv_pos.mpr (gap_pos a ..)) _ h.usable

def targets (C : Family G) (B : Fin n → (standard C).Tag) (hx : Fit C.path.levels b k x) :=
    cumulants C (tested C.path.levels b k x) B (fitting hx)

def clients (C : Family G) (w : Fin n→ C.book.Token) (b : ℝ) (k N p : ℕ) (x : Points n) :=
    probes C N p k (Station.choose C.path.levels b k x) w

def invoice (B : Fin n → (standard C).Tag) (t : Fin n → C.book.Token) (hx : Fit C.path.levels b k x) (N p : ℕ) : Config G (C.side N p) → veil (Fin n) :=
  Read.cylinder (targets C B hx) (clients C t b k N p x)

lemma bill_cont (B : Fin n → (standard C).Tag) (t : Fin n → C.book.Token) (hx : Fit C.path.levels b k x) (N p) (s) : Continuous
    fun U => (invoice B t hx N p U).part s := Read.cylinder_cont _ (fun i => Read.probes_cont i) s _

/-- A propagated marker purchase on the given course. Notice is value-local,
with any necessary exponent on that `Rep`. -/
def estimate (P : Rep G (C.side (width C.path.levels b k) p)) (c : Course C N p k) (hN : k≤N)
    (x : Points n) (Y : Config G (C.side N p) → veil (Fin n)) (e L l r : ℝ) :=
    let A := C.path.levels
    let T := yard C b hN p
    let hi : width A b k ≤ N := ((wider A b k).trans (before A b k)).trans hN
    Value.Notice P (fun z => ancestor C.S p (width A b k) hi (stampSite C b x hN p z))
      (c.flow (Array.stamp T (C.beta N p) Y) _ hi) (fun _ => r) e L l

/-- An end query on the *same* denominator & trajectory as will be used for
each marker estimate. -/
structure Settled (O : Rep G (C.side m p)) (c : Course C N p k) (hm : m ≤ N) : Prop where
  tied : c.Uses m hm O
  proper : ∃ σ g Λ δ w : ℝ, Station.Meets C.path.levels m p O g Λ δ ∧
    O.Lawful σ (C.path.levels.params m).paths Λ δ w

/-- Full-root output per slot subset on this placement. `s` never treated as a
choice of independent laws. Applied to the correction itself. -/
theorem rebate (O : HaarBudget G) (hc : Allocated C.path.levels M k O b) (hb : bank O C.path.levels (width C.path.levels b k))
    {P : Rep G (C.side (width C.path.levels b k) p)} {u : Course C N p k} {hN : k ≤ N} {q : width C.path.levels b k ≤ N}
    (hp : Settled P u q) (t : Fin n → C.book.Token)
    (B : Fin n → (standard C).Tag) (hx : Fit C.path.levels b k x) (hn : n ≤ M)
    {e c d : ℝ} (he : 0 ≤ e) (hE : c≤1) (hC : d ≤ 1) (hv : estimate P u hN x (invoice B t hx N p) e c d (allowance C.path.levels M k))
    (s : modes (Fin n)) (sh : s.val.Nonempty) :
    let T := yard C b hN p
    T.rootTest (C.beta N p) (fun U => (invoice B t hx N p U).part s) ≤ budget C.path.levels M k := by
  intro T
  let A:= C.path.levels; let r:= width A b k
  obtain ⟨H,σ,g,Λ,δ,w,hD,hd⟩ := hp
  have hea := Array.postage (X:=invoice B t hx N p) (T:=T) u q O H hd hD.positive hD.entrance hD.assigned rfl (Real.exp_pos _) he (bill_cont _ _ hx N p) hv s
  have hc1 := hc.permitted.plateau r le_rfl ((wider A b k).trans (before A b k))
  have hQ : A.params r=A.params k := congr_arg A.clock.stage hc1
  let Z := Fintype.card (Site (A.S.side r p))
  rw [Fintype.card_fin, show Fintype.card T.Cell=Z from rfl] at hea
  have hs : d+n*c ≤ 1+(M:ℝ) := by
    refine add_le_add hC ((mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _ : 0 ≤ (n:ℝ))).trans ?_)
    rw [mul_one]; exact_mod_cast hn
  let I := pot A M k
  have hi : protection O P (A.params r).paths Λ δ (d+n*c) g - 4*G.lieDim*Real.log g/(Z:ℝ) ≤ I := by
    apply (hb p P g Λ δ (d+n*c) M hD hs).trans
    change ticket O (A.params r) M ≤ I; rw [hQ]; exact hc.charge
  apply hea.trans
  let a := allowance A M k
  have ha : 1 ≤ a := fixed ..
  calc
    _ ≤ Real.exp I / a^s.val.card := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hi) (pow_nonneg (zero_le_one.trans ha) _)
    _ ≤ Real.exp I / a := by
      gcongr
      calc
        a = a^1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ ha (Finset.card_pos.mpr sh)
    _ = _ := by change Real.exp I / Real.exp (2*I)=Real.exp (-I); rw [← Real.exp_sub]; congr 1; ring
end
end YM.Next.Rank.Ship
