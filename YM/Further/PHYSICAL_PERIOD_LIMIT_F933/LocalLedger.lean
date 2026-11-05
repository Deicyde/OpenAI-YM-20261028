import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Homeland
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Symphony


/-!
# Pricing the Quay raw obligations BEFORE-L on the one Ledger

Where there ARE estimates after Payroll.

Uniform (across adjacent level) pricing can even depend on stage
thanks to the *common* planner sequence.

Test on this type: if can't fit θ or
price at these apertures, **don't assume** it's ok to just choose a higher L ex
post.

Reissue with higher cofers (bigger V.source) earlier, revising ALL
uses such as .Awaken weak-cal or Mult leases.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Rerequests
open Function Set Filter Lattice Wilson RG Supply Precision Pressure Bid
    Labels Source Push.Local Extra.Histories
    Homeland Sectioning Disk Bay World Bourse
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

-- Torque: arithmetic estimates BEFORE-L. MS tariffs can still buy by boost revenue latter (earlier calculations treat no such Stock as given).
variable {G : Gauge} {M : History G} {d N p l : ℕ} {F : Labels.Frame G d}

-- template fare and drift C per transition j := J(i+1) fixed. width & slots earlier from authorPrice G. choose enough for down-steps j to same or pred.
structure Caps (G : Gauge) where
  σ : ℕ → ℕ → ℕ → ℝ
  b : ℕ → ℕ → ℕ → ℝ
  seed d j k : 0 ≤ b d j k

abbrev issuer (G : Gauge) (z : Stage) := Next.Foundations.price G (max z.order z.power)
variable (T : Caps G)
open Next.Foundations
abbrev atomsDesk (u : ℕ → Stage) (d _j k : ℕ) :=
    (2* Push.Local.factor (hol G) (localSection G d) (u k).supportExponent (issuer G (u k)) + 1)
  -- T omitted

abbrev ticket (u : ℕ → Stage) (d j k : ℕ) := max (errorPrice (hol G) ((frames G).level d))
    (max (triangularPrice ((frames G).level d) (T.σ d j k)) ((atomsDesk (G:=G) u d j k)*(max 1 (T.b d j k))))

def bidders (u : ℕ → Stage) (j : ℕ) := max 1 ((Finset.range (j+1)).sup' ⟨j, Finset.mem_range.mpr j.lt_succ_self⟩ (fun d=> max (ticket T u d j j) (ticket T u d j (j-1))))

-- transfer across this timeline L.{grown}; don't need `V` parameter profiles during rebuild.


lemma paid (u : ℕ → Stage) (d j k) (h : d≤j) (hk : k=j ∨ k=j-1) : ticket T u d j k ≤ bidders T u j := by
  let p:= fun d=> max (ticket T u d j j) (ticket T u d j (j-1))
  refine le_trans (b:=p d) ?_ ((Finset.le_sup' p (Finset.mem_range.mpr (Nat.lt_succ_of_le h))).trans (le_max_right ..))
  rcases hk with h|h
  · rw [h]; exact le_max_left ..
  rw [h]; exact le_max_right ..

variable {z : ℕ → Stage} {W : Worth}
-- also fits Shrinks import at a slightly weakened L power (here choose stronger L^-1/2 ask than L^-2/5; can adjust .More, h geometry leaves 1/8 slack vs actual quote)


section poll
variable {T}
-- Prices before-L on upgraded capsule. W.* must be true for every d≤J. Enough with LayOut.W (not choose for PSREC later).


structure Requests (A : Ink M N p) (B : Goods A (localSection G d) (hol G) l) (T : Caps G) (P : Bay.Roads G) : Prop where
  head : l ≤ N
  ward : A.raw N 0 = WardBin.footprint (P.art d).cover (0 : Site (M.S.side N p))
  linear (i : ℕ) (h : l ≤ i) (ht : i<N) : Binding (B.yields i h ht)
  compares s u : ∃ e : ℕ→Equiv.Perm ℕ, e N 0=0 ∧
    ∀ i, ∀ hl : l ≤ i, ∀ hi : i<N, (∀ j, A.raw i (e i j)=(A.raw i j).image (affine s 0)) ∧
    ∀ x y : Users A (localSection G d) (hol G) (i+1), cardBound ((frames G).level d) u s (M.rep N p (i+1)).activities (e (i+1)) x.val y.val →
      callback ((frames G).level d) u s (M.rep N p i).activities (e i) (B.yields i hl hi x) (B.yields i hl hi y)
  rates i (hl : l ≤ i) (hi : i<N) (x : Users A (localSection G d) (hol G) (i+1)) (r : ℝ) : Meeting A (localSection G d) (hol G) (i+1) x.val r →
    let j:= M.levels.clock.J (i+1); let k:=M.levels.clock.J i; let q:= (puffs (M.S.block i))⁻¹^ (4:ℕ)
    Output (hol G) (localSection G d) M N p i 0 (WardBin.castAt (A.roles (i+1) (localSection G d)) x.val) r (A.raw i) (B.yields i hl hi x) (T.σ d j k) (T.b d j k) q q


end poll

-- Cleaning clocks. Proof only at i sufficiently high (choose r AFTER M of one reading), or prepare from direct `delay` before commissioning. Doesn't generate
-- arbitrary high supportPrices from nothing!


-- reference ports can't presume that changing l after acquiring Rosters stays compatible.
-- This calls bay after getting fiscal clocks, then allow estimates *for compatible l* even if end.N missing otherwise. For application replace l hypothesis in
-- `Symphony.joining`/`Requests` analogously. Authored premises are the genuine `Rates` request on prices
-- enforced in this proposal. Keep exact σ cost field from MONE. Want physical proof that they're available
-- and Φ convolution/spin formulas on those inputs, do not infer from clocks.


-- Can also always build dormant portions for these leads; not necessary in h source gates later.
variable {α : ℕ → ℝ}





end YM.Further.PhysicalPeriodLimitF933.Rerequests
