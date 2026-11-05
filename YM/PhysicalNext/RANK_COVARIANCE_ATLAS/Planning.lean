import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.RANK.Prepaid
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Gates
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Push.FREE_RESOLVENT.ListJets



/-!
# Paying on the chosen stretches

Optional use with Prepaid. Even across all families, lengths BEFORE
post-L waits. Explicit extra `SizeBook` allows an extra floor
chosen with the other Panel requests. Wait is still *before* buying
Levels/M family. NO getting a new calendar after receiving incompatible
ancestors or claiming this constructs a family. Protect also the upstream
post-L costs/gates at Width uses; give `Paid` on THAT path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Filter Lattice Laurent Bloch Exterior Matrix Precision RG RG.Supply FreeResolvent Tree Bid
open Next.Rank Next.Rank.Atlas Next.Rank.Tapes Next.Rank.Peak Next.Rank.Station Next.Rank.Perch Next.Rank.Spindle
open Finset Marker Glyph Wilson Value Ac Cells Edition Dash Extraction Org Spec OS OS.Ground Analysis
open scoped Topology BigOperators ComplexConjugate Matrix.Norms.Frobenius ContDiff ENNReal NNReal Classical

variable {G : Gauge} {X : Sheet G}

/-- Both votes for a charged weak call. Ticket includes d+3, not a
requirement imposed on some arbitrary weak Call where `ref d` does not fit.
An Assignment purchases only finitely many families at a given J. -/
def SizeBook (X : Sheet G) (k : ℕ → Finset ℕ) (P : ∀ i, Panel i) (M : ℕ→ℕ) := ∀ d j, d∈k j → d+3 ≤ j ∧
    ∀ (L : Side), M j ≤ L.val → Regiment ((P d).bag j) (X.profile j) L ∧ reserve (prepared X.kernel) j (P d).θ (P d).arc L.val

/-- Order & growth per family come before choosing L for J. This is
for the fee being applied HERE; larger floors of all precursor procedures
have to be paid too (hence `floorL`). Does not claim that *physical*
requests in Interaction or Entry costs fit. -/
lemma growth (S : ∀ (_ j : ℕ), Entry (X.profile j)) (b : ℕ→ℝ) (h : ∀ d, d+6≤b d) (hu : Tendsto (fun j=>(X.profile j).order) atTop atTop) :
    ∃ (P : ∀ d : ℕ, Panel d) (k : ℕ → Finset ℕ) (M : ℕ → ℕ),
      (∀ i,(P i).arc=b i ∧ ∀ᶠ j in atTop,i∈k j) ∧ (∀ j i,i∈k j→Compatible (P i) j (S i j)) ∧
        (X.floorL ≤ M) ∧ SizeBook X k P M := by
  obtain ⟨P,k,M,H,hK⟩:= all_preSheet (X:=X) S b h hu
  let s (j:ℕ):= (k j).filter fun i=>i+3 ≤ j ∧ 4≤j
  have ha (i j : ℕ) := reserving (prepared X.kernel) j (P i).θ (show 0≤(P i).arc by linarith only [(P i).huge,Nat.cast_nonneg (α:=ℝ) i])
  have he (j) := (eventually_all_finset (s j)).2 (fun i _=> tendsto_natCast_atTop_atTop.eventually (ha i j))
  choose L ht using fun j=> eventually_atTop.mp (he j)
  let e (j:ℕ):= max (X.floorL j) (max (M j) (L j))
  refine ⟨P,s,e,?_,fun i j hv=> (hK i j (mem_filter.mp hv).1).1,fun j=> le_max_left ..,?_⟩
  · intro i; refine ⟨(H i).1,?_⟩
    filter_upwards [(H i).2,eventually_ge_atTop (i+4)] with j ha hj; exact mem_filter.mpr ⟨ha,by omega⟩
  intro i j hx
  have hr (A : Side) (hh : e j ≤ A.val) : M j ≤ A.val ∧ L j ≤ A.val := max_le_iff.mp ((le_max_right ..).trans hh)
  exact ⟨(mem_filter.mp hx).2.1,fun c hc=> ⟨(hK j i (mem_filter.mp hx).1).2 c (hr c hc).1,ht j c (hr c hc).2 i hx⟩⟩

-- Buying this size along with other `Large` proofs can still issue
-- monotone L. Does *not* pick new matching ProofPorts.


/- Actual weak costs after L, plateau funded in same wait as Metering
(in particular clearance and charge at COMMON epochs). Used for example
with panel from `growth`. Doesn't itself integrate with the vacuum purchase;
 must arrange w.L meets M, and take stronger resulting Wait BEFORE creating
Levels, even if wait bumps still required elsewhere. -/
variable {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}
variable (O : HaarBudget G)





/-- Additional Sector etc work can pay more, preserving the
fact that these numerical calls are allowed on this B. The *single* actual
call at all matching costs from all branches must still be produced. -/
lemma retains_budget {W F : Wait Z} {A : Levels G} (hs : F.minLength ≤ W.minLength) (h : ∀ i,F.readyHere i ≤ W.readyHere i ∧ ∀ s,F.window i s≤ W.window i s) (hp : Paid W A) : Paid F A := by
  refine ⟨hp.kernel,hp.bar,hp.stage,hp.firstZero,hp.firstOne,hp.lengths,hp.theta,hp.pays,hp.paysHigher,fun i=> hs.trans (hp.periods i),hp.volume,?_⟩
  intro j hj; obtain ⟨k,h₁,h₂,h₃⟩:=hp.run j hj; have hf:= (h j).2 (A.S.scale k); exact ⟨k,(h j).1.trans h₁,hf.trans h₂,fun i hi hi'=> h₃ i (by omega) (by omega)⟩


end YM.PhysicalNext.RankCovariance
