import YM.Next.WARD_BIN.Rack
import YM.Next.WARD_BIN.Volley

/-!
# Funding through the quota at actual costs, geometry stamps

Output discrepancies via subexponential top **bankroll**; each stop class from
one-step Volley inputs and THAT same catalogue for Woke. `K`-ticket repeated
losses use G09 only on the singleton costs themselves, then issue width to the
multimarker code through those numbers. No applying scalar lease to high modes.
Keep explicitly p-dependent top initialization (combined order via fused nets).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Array
open Function Filter Topology MeasureTheory Lattice Wilson RG Marker Overlay Bid Wheels Crest
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G} {W : Worth} {d ℓ N p i : ℕ} {c u w b : ℝ} {n : Side} {A : Chart C d}
  {Z : Shelf A} {D : Page C d N p} {F : Extraction.Order} {S : Finset Cover}

/-- Need these for the RBin requests. First choose all pre-L constants
including tariffs, then assign quota relative to that L and pay upon stage
transitions too. Retain on Shelf. Quota may serve current orders only.
-/
structure Forts (Z : Shelf A) : Prop where
  tarp : ∀ᶠ i in atTop, tariff (C.path.levels.budget i) ≤ rentAt C i
  path : ∃ b : ℕ → ℝ, ∀ᶠ i in atTop, Quota C d (b i) i ∧
    ∀ (N p : ℕ), ∀ h : Z.horizon ≤ N, i < N → Volley (Z.page N p h) (b i) i

section Credit
open Real
def weather (C : Family G) (i : ℕ) := (1+tariff (C.path.levels.budget i))*(1+ Real.exp (C.path.levels.params i).supportExponent*rentAt C i)
def inflation (C : Family G) (i : ℕ) := weather C i / cap₁ C i




def peak (f : ℕ→ℝ) (n : ℕ) := (Finset.range (n+1)).sup' ⟨n,Finset.mem_range.mpr n.lt_succ_self⟩ f



def bankroll (A : Chart C d) (b c : ℝ) (k : ℕ) :=
    1+Real.exp ((C.path.levels.params k).supportExponent)*((1+A.ush k)*‖c‖)*(C.path.levels.clock.threshold k)⁻¹^d +
    4*(1+rentAt C k)*‖b‖ * peak (inflation C) k

def ready (A : Chart C d) (b c : ℝ) (N i : ℕ) := gainChart C.path N i / bankroll A b c N






end Credit





/- stage geography. Enforce separation only for steps used and coarse retros,
keep charges anchored. no pretending `coverSize` constant for all i≤N. -/
structure Door (C : Family G) (ℓ i d : ℕ) : Prop where
  chief p : Hollow (C.path.levels.budget i) (zone C ℓ i p)
  home p : coverNumber (C.path.levels.clock.coverSize i) ((C.localSection d).footprint (0:Site (C.side i p))) ≤ 1



instance caste : Nontrivial (Cast C ℓ p) := by
  apply Fintype.one_lt_card_iff_nontrivial.mp
  change 1< Fintype.card (Site (C.side ℓ p)); rw [site_card]; apply one_lt_pow₀
  · exact lt_of_lt_of_le (by decide : 1< (4:ℕ)) (Nat.le_of_dvd (C.side ℓ p).property (C.S.side_four ℓ p))
  decide


end YM.WardBin.Array
