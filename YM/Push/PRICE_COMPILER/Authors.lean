import YM.Next.EXTRACTION.Base
import YM.Next.FOUNDATIONS.Primary
import YM.Next.FOUNDATIONS.TestBounds
import YM.Push.PRICE_COMPILER.Basic

/-!
# Pre-L ordering for RAuthors

Use the actual
producers from YM.Next.FOUNDATIONS; one system fixed at all weights. Handle
all weights, though at each smoothing index only a finite collection is
budgeted. Stage `j` can pay d=0; no need for a separate unit argument. No
arrays of insertions/propagation here. In particular payment of a column of
the **section** is different from producing PSREC/Paper for it.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply Labels Source Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- Maximum engineering weight budgeted. Retain that weight at every
higher smoothing index. -/
structure Admission where
  cap : ℕ → ℕ
  grow : Monotone cap
  active j : 4 ≤ j → cap j + 3 ≤ j
  deep : Tendsto cap atTop atTop



/-- First-stage parameters. Choose for the desired finite requests, not
from a particular trajectory. The strength (all the inequalities here)
makes this part easy to use for RefLi. -/
structure OrderPlan where
  degrees : Admission
  k : ℕ → ℕ
  P : ℕ → ℕ
  A : ℕ → ℝ -- support exponent
  kmono : Monotone k
  Pmono : Monotone P
  Amono : Monotone A
  kbase i : 6 ≤ k i
  Pbase i : 2 ≤ P i
  Apos i : 0 < A i
  kpay i : degrees.cap i+1 ≤ k i
  Ppay i : degrees.cap i ≤ P i



variable (G : Gauge) (m : OrderPlan)
/-- The table used also for minimum period requests. -/
def stencilNeed (j : ℕ) : ℕ := prefixHi (minSide G) (m.degrees.cap j)
lemma stencilNeed_mono : Monotone (stencilNeed G m) := (prefixHi_mono _).comp m.degrees.grow
lemma minSide_le {j d : ℕ} (h : d ≤ m.degrees.cap j) : minSide G d ≤ stencilNeed G m j :=
  le_prefixHi _ h

/-- E.L.10442 -/
def supPrice (d : ℕ) := (full_value_bound G d).choose
/-- (B70 conventions, including the reads at wrapping X). -/
def readPrice (d : ℕ) := (price_of_readout (hol G) ((Labels.frames G).level d)).choose

def degreeFee (d : ℕ) : ℝ := max (supPrice G d) (readPrice G d)

/-- Include BOTH the next-integration and auxiliary local projection needs
at this point, but no unbudgeted propagation constants. Larger numerical
requests are allowed. `price` in this declaration is exactly the monotone
pre-price from FOUNDATIONS. -/
def authorFee (j : ℕ) : ℝ := max (price G (max (m.k j) (m.P j)))
  (max (prefixHi (degreeFee G) (m.degrees.cap j)) (stencilNeed G m j : ℝ))

/-- Use also for G08/G09 when the extra prices are given. The mathematical
producers of those extra prices (e.g., leading matrix norms & actual
matching) are red. -/
def worth (extra : ℕ → ℝ) : Bid.Worth :=
  let u (j : ℕ) := max (authorFee G m j) (extra j)
  ⟨payHi u, payHi_one u, payHi_mono u⟩

variable {G m}

lemma worth_pays (extra : ℕ → ℝ) : authorFee G m ≤ (worth G m extra).K := fun i =>
  (le_max_left (authorFee G m i) _).trans (le_payHi (fun i => max (authorFee G m i) (extra i)) i)

/-- Can choose columns even larger. The `64` next-price reserve is the
one in `Bid.Loan`. Factorial payment ties to `Bid.Fuels`. Thus pre-L only. -/
def columnFee (v : Bid.Worth) (m : OrderPlan) (extra : ℕ → ℝ) := prefixHi (fun i =>
  max (64*(v.K (i+1))^(2:ℕ)) (max ((Nat.factorial (m.k i)):ℝ) (extra i)))

lemma columnFee_requirements (v : Bid.Worth) (m : OrderPlan) (extra : ℕ → ℝ) :
    let f := columnFee v m extra
    Monotone f ∧ extra ≤ f ∧ (∀ i, 64*(v.K (i+1))^(2:ℕ) ≤ f i) ∧
      ∀ i, ((Nat.factorial (m.k i)):ℝ) ≤ f i := by
  intro f
  refine ⟨prefixHi_mono _, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
    apply le_trans _ (le_prefixHi (f:=fun j =>
      max (64*(v.K (j+1))^(2:ℕ)) (max (Nat.factorial (m.k j) : ℝ) (extra j))) (le_refl i))
  · exact le_max_of_le_right (le_max_right ..)
  · exact le_max_left ..
  exact le_max_of_le_right (le_max_left ..)

lemma worth_le_room (v : Bid.Worth) {i : ℕ} {c : ℝ} (hw : 64*(v.K (i+1))^(2:ℕ) ≤ c) :
    v.K i ≤ c := by
  have hz := v.growth (Nat.le_succ i)
  have ht := v.prices (i+1)
  nlinarith

section Delivery
variable {v : Bid.Worth} (hp : authorFee G m ≤ v.K)
include hp

lemma source_fee (j : ℕ) : price G (max (m.k j) (m.P j)) ≤ v.K j :=
  (le_max_left ..).trans (hp j)








end Delivery

lemma reference_levels (m : Admission) (a : Levels G) (wait : ℕ → ℕ) :
    ∃ r : ℕ → ℕ, Monotone r ∧ wait ≤ r ∧ ∀ d N, r d ≤ N → d ≤ m.cap (a.clock.J N) := by
  choose k hk using (tendsto_atTop_atTop.mp (m.deep.comp a.fits.deep))
  let f (d : ℕ) := max (k d) (wait d)
  exact ⟨prefixHi f, prefixHi_mono _, fun _ => (le_max_right ..).trans (le_prefixHi f le_rfl),
    fun d i hi => hk d i ((le_max_left ..).trans ((le_prefixHi f le_rfl).trans hi))⟩

/-- Read the conditional history cuts with the **same** profile. For RefLi
`r` can be chosen regardless of any periods/β run because `side m p`
already fits the stencil budget at its stage, for every m,p on such levels.

`clock J (r d) ≥ d+3` etc; `clock.J (m+1)=clock.J m` allowed;
level zero included. No claim Paper/clocks or selected from these prices. -/
theorem refs_paid {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W}
    {I : Wait Y} {v : Bid.Worth} {H : History G}
    (hp : authorFee G m ≤ v.K) (hk : ∀ j, (p.profile j).order = m.k j)
    (hP : ∀ j, (p.profile j).power = m.P j)
    (hr : ∀ j, 64*(v.K (j+1))^(2:ℕ) ≤ (p.profile j).columns)
    (hs : stencilNeed G m ≤ W.shells) (hH : Paid I H.levels) (r : ℕ → ℕ)
    (hb : ∀ d i, r d ≤ i → d ≤ m.degrees.cap (H.levels.clock.J i)) :
    Bid.RefLi H (Labels.frames G) (localSection G) (hol G) r := by
  let J := H.levels.clock.J
  apply refLi G
  · intro d
    have hw := m.degrees.active (J (r d)) (H.levels.clock.adm _)
    have hi := hb d _ le_rfl
    refine ⟨Nat.le_trans (Nat.add_le_add_right hi _) hw, fun i hz => ?_⟩
    rw [params_eq hH, hk, hP]
    exact ⟨(Nat.add_le_add_right (hb d i hz) _).trans (m.kpay _), (hb d i hz).trans (m.Ppay _)⟩
  · intro d N i hw
    exact (minSide_le G m (hb d N hw)).trans ((stencilNeed_mono G m ((step_paid H.levels N).1)).trans
      ((hs _).trans (side_ge_shell hH N i)))
  intro d i _
  rw [params_eq hH, hk, hP]
  exact (source_fee hp _).trans (worth_le_room v (hr _))
end YM.Push.PriceCompiler
