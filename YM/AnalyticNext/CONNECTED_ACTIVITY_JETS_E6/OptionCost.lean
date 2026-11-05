import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Depot
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.ResponsePrice
import YM.Next.BOUNDARY.Assembly
import YM.Next.EXTRACTION.Base
import YM.Next.FOUNDATIONS.Primary
import YM.Push.ABSOLUTE_SUMS.Buy


/-!
# The optional alphabet

Do not collapse labels by equal support. This is one spelling variant,
keeps compulsory inventories with their own reservation. `Issued` per labels
from true Ops. To charge Buy.sectors epsilon normalize with exponent `head`.
Value not all derivatives; exposes logarithmic inventory marks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Coat Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

/-- ι optional on a Letter from a sector. !!! Occurrences of frozen
inputs/packets vs this alphabet require same X as y; tags are shared. -/
abbrev Alphabet (c f : Side) := ℕ ⊕ LogIndex c f ⊕ WarningAt c f

def footprints (T : Tube G S) (R : Rep G f) (l B : ℕ) : Alphabet c f → Support c :=
    Sum.elim (Raw.forcedFoot S.ratio l B R) (Sum.elim (roadway T R B l) (field_support S B l))
def lengths (T : Tube G S) (R : Rep G f) : Alphabet c f → ℝ := fun i =>
    ((Sum.elim (Raw.forcedExtra R) (Sum.elim (exCharge T R) (fun _ => 0)) i : ℕ):ℝ)

def rates (z : ℕ → ℝ) (w : LogIndex c f → ℝ) (K : ℝ) : Alphabet c f → ℝ :=
    Sum.elim z (Sum.elim w (fun _ => K))

lemma ratesCombine {R : Rep G f} {l B : ℕ} {A ε V C Y D : ℝ} {v : ℕ → ℝ} {w : LogIndex c f → ℝ}
    (hV : Sales B A ε (Raw.forcedFoot S.ratio l B R) v (Raw.forcedExtra R) V)
    (hW : Sales B A ε (roadway T R B l) w (exCharge T R) C)
    (h : Sales B A ε (field_support S B l) (fun _ => D) (fun _ => 0) Y) :
    Sales B A ε (footprints T R l B) (rates v w D) (Sum.elim (Raw.forcedExtra R)
      (Sum.elim (exCharge T R) (fun _ => 0))) (V+(C+Y)) := hV.together (hW.together h)

lemma exponent_fee (G : Gauge) (L : Side) (l : ℕ) (a ε b t : ℝ) (hA : 0≤a) (E : ℝ→ℝ) (h : Rate G L b E) :
    ∃ W : ℝ → ℝ, Rate G L b W ∧ ∀ x : ℝ, ∀ (c f : Side) (S : StepData c f), let B:=radiusB x
      S.patch.L=L → 0<B → 0≤t*E x →
        Sales B a ε (field_support S B l) (fun _ => t*E x) (fun _=>0) (W x) := by
  let u := warning_count L
  let W x := ((Animals.ballCost ((l+1)*radiusB x):ℝ)*u)*(t*E x*Real.exp (a*Animals.ballCost (l+1)))
  have hv := Census.width_rate G L (l+1) 0; simp only [add_zero] at hv
  refine ⟨W, (by convert ((hv.mul_right u).mul ((h.mul_left t).mul_right _)) using 1; ring), ?_⟩
  intro x c f S B hL hp hn
  refine fixed (B:=B) (A:=a) (C:=t*E x) (hL ▸ staffed S) hp _ ?_ hA hn
  intro i y hy; apply (Animals.neighbors_mem ..).mpr
  exact (sigh S i y B l hy).trans (by rw [Nat.add_mul,one_mul]; omega)

/-- Structuring actual pre-input pre-L hypothesis cleanly: no analytic
R lemma. Need ε precede L and allowed marks d,l. `Spec` post-W(except
for P,Π below). Larger `l` (500 chosen) for overlap. -/
structure Target (G : Gauge) (P : Teller G) where
  ε : ℝ
  exp : ℝ
  δ : ℝ
  rate : ℝ -- exponent goal Hat, leaves amplitude wiggle for trees
  halo : ℕ
  buys : 500≤halo
  table : ChartRatio G
  table_exists : LocalRatio table
  usable : 0<ε
  pos : 0<δ
  bound : 0 ≤ exp
  start : -(1/2:ℝ) < rate
  stop : rate < 0
  grants : 4*ε < P.top.supportExponent ∧ 8*ε<P.top.width ∧ 8*ε<P.below.width
namespace Target
variable (R : Target G P)

def relative := R.exp+2*R.ε+R.δ
def goal (L : Side) (x : ℝ) := betaF G x L ^ R.rate

def costs (L : Side) (μ β x C : ℝ) := Buy.quote G L μ (1/2) R.exp R.ε R.δ β x 1 0
    (C*Delay.bill G L x ^ 5) (R.goal L x)

lemma pay_for (L : Side) {μ C : ℝ} (hμ : 0<μ) (hC : 0 ≤ C) :
    ∀ᶠ x in atTop, ∀ β ∈ Set.Ici (betaF G x L/2), (R.costs L μ β x C).Buy L R.halo (radiusB x) := by
  have hc := Buy.quoted G L hμ (show (0:ℝ)<1/2 by norm_num) R.pos R.bound R.usable hC (by norm_num : (0:ℝ)<2) 5 R.halo
  have he := Census.width_rate G L 1 0; simp only [one_mul,add_zero] at he
  have ht := ((Rate.power (G:=G) (L:=L) (a:=R.rate)).mul (he.mul_left 16)).below (by rw [add_zero]; exact R.stop) _ R.pos
  filter_upwards [hc,ht] with x hx hu β hh
  obtain ⟨hF,hx⟩ := hx
  refine hx _ _ _ _ _ (show (1/2:ℝ)*betaF G x L ≤ β from by
    change _/2 ≤ β at hh; linarith) le_rfl zero_le_one ?_ ?_ ?_ ?_
  · refine Real.one_le_exp ?_; have he := Delay.bill_ge G L x; rw [Real.rpow_zero]; positivity
  · rw [mul_zero,add_zero,Real.rpow_zero,mul_one]
  · unfold goal; positivity
  apply (le_div_iff₀ (show 0 < 16*(Animals.ballCost (radiusB x):ℝ) from by
    have hn := Animals.neighbors_ge (radiusB x); positivity)).mpr
  exact (le_abs_self _).trans hu
end Target
end YM.ConnectedActivityE6
