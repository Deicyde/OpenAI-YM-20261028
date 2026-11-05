import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.LapCount
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Monitors
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount
import YM.Next.FREE_KERNELS.Differences

/-!
# Counting/weight on fixed B-tiles. Sparse price tool

Periods possibly wrap; estimates at every Hit. Built for assembly of
all Bills, enrol overlap under ENLARGEMENTS, not just literal radius of
product formulas. Report eventual powers post-L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Jewels
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- halo cost can be bought (all pre-L). e support rule. `increment(x)`
-- directions polynomial controlled at future stage separately.
def den (o : Site c) (l b : ℕ) := halo (l*b) ({o}:Support c)

def amend (G : Gauge) (D : Patch) (x r : ℝ) := betaF G x D.L ^ (-r)
lemma pos_ac (G : Gauge) (D : Patch) (x r : ℝ) (hp : 0<betaF G x D.L) :
    0 < amend G D x r := Real.rpow_pos_of_pos hp (-r)

lemma seed_count (H : ℝ) (l : ℕ) (hH : 0≤H) : ∀ᶠ x : ℝ in atTop,
    ∀ {c : Side} (y : Site c) (n : Type) (_f : Fintype n) (p : n → Site c) (s : Finset n),
      governs p H → (∀ i∈s, y∈ den (p i) l (radiusB x)) → (s.card:ℝ) ≤ pieces x 5 := by
  have ht : Tendsto (fun x : ℝ => (radiusB x:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
  filter_upwards [ht.eventually_ge_atTop 1,ht.eventually_ge_atTop (H*(1+(l:ℝ))^4)] with x hh hv c y n f p s hg hs
  let b : ℝ := radiusB x
  apply le_trans (le_trans (show (s.card:ℝ) ≤ (card (reaches p (l*radiusB x) y):ℝ) from Nat.cast_le.mpr
    (Finset.card_le_card fun i hi => ?_)) (hg y (l*radiusB x)))
  · push_cast
    calc
      _ ≤ H*((1+(l:ℝ))*b)^4 := by gcongr; unfold b; linarith
      _ = H*(1+(l:ℝ))^4 * b^4 := by ring
      _ ≤ b*b^4 := mul_le_mul_of_nonneg_right hv (by positivity)
      _ = pieces x 5 := by unfold pieces b; ring
  obtain ⟨z,hz,h⟩ := halo_spec.mp (hs i hi); rw [mem_singleton.mp hz,separation_comm] at h; exact mem_filter.mpr ⟨mem_univ _,h⟩

lemma instills (G : Gauge) (D : Patch) (C a b : ℝ) (p : ℕ) (hC : 0≤C) (hp : a<b) : ∀ᶠ x in atTop,
    C*tab G D x^p*amend G D x b ≤ amend G D x a := by
  filter_upwards [Fees.growth G D.L (sub_pos.mpr hp) hC 0 p,Delay.shift_pos G D.L] with x hx h
  simp only [Real.rpow_zero,mul_one] at hx
  have ht := (pos_ac G D x b h).le
  apply le_trans (mul_le_mul_of_nonneg_right hx ht)
  unfold amend; rw [← Real.rpow_add h,show b-a + -b = -a by ring]

-- fixed-size vertices in one alphabet, same inclusion on output moves.
-- Note this is for raw weights. Use after building the actual expenses;
-- multiply any Books shifts separately and apply to all offsets.


-- trivial tickets (important that envelope is of same type)

def without (r : ℝ) (n : Type*) : Tilt n := ⟨r, fun _ => 0⟩
lemma zero_spend {r : ℝ} (h : 0≤r) (n : Type*) : (without r n).Sound := ⟨h,fun _=>le_rfl⟩
lemma door {r : ℝ} {n : Type*} [Fintype n] (z : n→ℝ) : Ticket (without r n) z = r := by
  simp [Ticket,without,tilt]
lemma sway (r : ℝ) (n : Type*) [Fintype n] (b : Till) : b.sale (without r n) = r := by
  simp [sale,without]
/-- User rate for the final tree sensor, any real between 0 and 1/2.
Above it two intermediate rates STILL in that range. -/
structure Tempo where
  rate : ℝ
  pays : 0<rate
  open_ : rate<1/2

def Tempo.up (t : Tempo) : Tempo := ⟨(t.rate+1/2)/2,by linarith [t.pays],by linarith [t.open_]⟩


end YM.AnalyticNext.ConnectedActivity.Jewels
