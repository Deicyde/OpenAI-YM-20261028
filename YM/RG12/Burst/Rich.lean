import YM.RG12.Burst.Thin
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "t!" => Q.goal L x+ value10 Q L μ x s B j n
-- Fragrances of any class. Need no special Prince budget. supply on whole supported with pivotal mark. Holds also pour.M signatures, possible application to forcing via analogous methods.
def brush10 (y:Site c)(i:ℕ)(p:H.fragrances):= if speaks M H p then d0*oval M H N p*potY M H y i (j:=j) p else 0
lemma brushN (y:Site c)(p:H.fragrances){i:ℕ}:0 ≤ brush10 M H N y i p:=by
  unfold brush10; split; apply mul_nonneg (mul_nonneg (dew M H|>.2.1) (oval_pos ..)); unfold potY flareC March.shiftG; positivity
  exact le_rfl
local notation "Z!" => locus M H
lemma supply (hR:Herd H N.conduit A B n)(U : BudgetPoint){y:Site c}(hy:y∈M.crest.image S.ratio.parent)(hU':U.threshold=Pressure.temp x)(hU:U.order≤j):
    ∀ p:H.fragrances, U.Regular (locus M H y p) (matin M H p χ) ∧ U.supBounds y (locus M H y p) (matin M H p χ) (brush10 M H N y U.power p):=by
   intro p; refine ⟨scops M H N hR U hy hU' hU p,?_⟩; by_cases he:speaks M H p <;> simpa only [brush10,he,potY,locus,ite_true,ite_false, not_false_eq_true] using! (aliveY M H N hR U hy hU' hU p) -- split serves

def paint10 (Q : ConnectedActivityE6.Target G P)(L:Side)(μ x s B:ℝ)(j n:ℕ)(E:ℝ)(i:ℕ):ℝ:= collars G E x j i*((Q.goal L x+ value10 Q L μ x s B j n)*(1-1/2)⁻¹)
local notation "w!" i => paint10 Q L μ x s B j n E i
lemma front10 (hs:1≤ s)(hv:Bikes Q L μ x a E B j n)(hr:Ready H.smallAt (radiusB x) (gold M H N (s:=s)) (a+E) t! E (1/2)) {y:Site c}(hy:y∈M.crest.image S.ratio.parent)(i:ℕ):
    SumBudget (fun p:H.fragrances=> s^hue H p*(brush10 M H N y i p)*Real.exp (a*coverNumber (radiusB x) (Z! y p))) (d0*w! i):=by
    have H':= ink M H N hv hr y
    have hD:= dew M H|>.2.1
    have he:=hv.allow
    have hC:0 ≤ collars G E x j i:=by unfold collars Reserves.polyPrice March.shiftG; positivity
    let t:= Q.goal L x+value10 Q L μ x s B j n
    change SumBudget _ (d0*(collars G E x j i*(t*(1-(1/2))⁻¹))); rw [← mul_assoc d0]
    refine budget_mono (budget_scale (mul_nonneg hD hC) H') (fun p=> by exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hs) _) (brushN ..)) (Real.exp_pos _).le) fun p=> ?_
    unfold brush10; split
    next hh =>
      have hp:=seatY M H y hy p; unfold locus at hp; rw [if_pos hh] at hp
      dsimp only; rw [if_pos hp]; unfold potY locus collars flareC; rw [if_pos hh, mul_pow]
      let t:ℝ:=coverNumber (radiusB x) (H.bookFoot (.inr p)); let k := i*j -- power! check flareC
      have hG:=polynomial_cost he (show 0≤t from Nat.cast_nonneg _) k
      have hL : 0≤ s^(hue H p)*(d0*oval M H N p)*(March.shiftG x)^k*Real.exp (a*t):=by unfold March.shiftG; have ho:= oval_pos M H N p; positivity
      change s ^ hue H p * (d0*oval M H N p*((March.shiftG x)^k*(1+t)^k))*Real.exp (a*t) ≤ (d0*((March.shiftG x)^k*_))*(s^hue H p*oval M H N p*Real.exp ((a+E)*t)) -- confirm
      calc
        _ = (s^hue H p*(d0*oval M H N p)*(March.shiftG x)^k*Real.exp (a*t))*(1+t)^k :=by ring
        _ ≤ (s^hue H p*(d0*oval M H N p)*(March.shiftG x)^k*Real.exp (a*t))*(E⁻¹^k * k.factorial*Real.exp E*Real.exp (E*t)) :=mul_le_mul_of_nonneg_left hG hL
        _ = _:=by rw [add_mul,Real.exp_add]; unfold Reserves.polyPrice; ring
    next hh=> rw [mul_zero,zero_mul]; exact (budget_scale (mul_nonneg hD hC) H').1 p

lemma bill10 (hs:1≤ s)(hv:Bikes Q L μ x a E B j n)(hr:Ready H.smallAt (radiusB x) (gold M H N (s:=s)) (a+E) t! E (1/2)) {y:Site c}(hy:y∈M.crest.image S.ratio.parent) (i m:ℕ):
    SumBudget (fun p:H.fragrances=> if m≤hue H p then (brush10 M H N y i p)*Real.exp (a*coverNumber (radiusB x) (Z! y p)) else 0)
       ((s^m)⁻¹ * d0*w! i):=by
   have hc:=zero_lt_one.trans_le hs
   rw [mul_assoc]
   refine budget_mono (budget_scale (inv_nonneg.mpr (pow_nonneg hc.le m)) (front10 M H N hs hv hr hy i)) (fun p=>?_) (fun p=> ?_)
   · split; exact mul_nonneg (brushN ..) (Real.exp_pos _).le; exact le_rfl
   let t:=Real.exp (a*coverNumber (radiusB x) (Z! y p))
   let b:=brush10 M H N y i p
   have he:0≤ b*t:=mul_nonneg (brushN M H N y p) (Real.exp_pos _).le
   rw [show s^hue H p * b *t= s^hue H p*(b*t) from mul_assoc .., ← mul_assoc]
   split; next hh =>exact le_mul_of_one_le_left he (one_le_inv_mul₀ (pow_pos hc m) |>.mpr (pow_le_pow_right₀ hs hh))
   exact mul_nonneg (by positivity) he
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
