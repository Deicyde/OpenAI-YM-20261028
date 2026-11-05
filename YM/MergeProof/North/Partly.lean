import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Assure
/-!
 # η power with reserved Mass transfer. small price oracle only Matins.d additional. Arc works both and MARK clocks.C.Struct.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak Greenbelt WardBin.Lies March
open Gas Ursell Trees Daisy Daisy.Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
    {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {W μ x C' : ℝ} {R : Rep G f}
    {p j n m k : ℕ} {L : Side} {Q: ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {d A t C w M N z β r η v b Y' q: ℝ}{C₀ : Libretto G n}
variable {H' : ℝ} (H: Cash W x μ L Q o C T R)(M': Lotus.Leaf R) (i : ℕ)(hi:M'.turn=.logKey i)(hN: Captain H p C' d v t A b r M q m Chi.canonical)
local notation "s"=> H.fragrances
local notation "k'" => Brim.icon H i
local notation "o'" => (plate H i)
variable {g a e:ℝ}(h: Herd H hN.conduit A M m) (hB:Bikes Q L μ x a e M p m)(hS: B.supportExponent + 3 ≤ a)(hw:foam Q L)
include hi h hB hN hS hw
lemma haze (y:Site c)(hb:y∈M'.crest.image S.ratio.parent)(hp:B.order=p)(he:B.threshold=Pressure.temp x)(hm:B.B=radiusB x):
    ∃ C:ℝ,B.supBounds y (plate H i).support (matin M' H (icon H i) Chi.canonical) C∧ Push.Local.reservedMass B (plate H i).support C ≤ (volt x p B.power*(Q.goal L x)⁻¹) * R.p.mass M'.crest M'.weight:=by
    have hz:= hB.paid; have hK:= raindance M' H hN hw hB; let W:= (o').site; let Y:= (o').support; let F:= Charity.matin M' H k' Chi.canonical
    have hv:= aliveY M' H hN h B hb he hp.le (p:=k'); rw [grinchY H M' i hi] at hv
    have hf := (grinch H M' i hi).1
    have hh : speaks M' H k':= ⟨none,(by rw [hf.2.1]; simp),hf.2.2⟩
    rw [if_pos hh,sites_icon] at hv
    have ht := Charity.ticks M' H hN hK 0 W
    let o0:=oval M' H hN k'; have hd:0≤ o0:=oval_pos M' H hN _
    have hT:= budget_single ht k'; dsimp only at hT; rw [if_pos (show W∈ H.bookFoot (.inr k') from (sites_icon H i).symm ▸ (o').anchor),sites_icon,if_pos (Nat.zero_le _),pow_zero,mul_one] at hT
    let D:ℝ:=coverNumber B.B Y
    have hD:0≤D:=by unfold D; positivity
    let Qe:= Reserves.polyPrice (1/2:ℝ) (B.power*p)
    let t:= volt x p B.power
    have hx : t≥0:= mul_nonneg (by unfold shiftG; positivity) (by unfold Reserves.polyPrice; positivity)
    have ha: o0 * Real.exp ((a+e)*D) ≤ 1:=by
       unfold D; rw [hm]; apply hT.trans; have he' := hK.earns.trans hK.price
       let δc:= Q.mark L μ x
       let t:=daisD Q L μ x m
       have hu:0≤t:=budget_nonneg (hK.second W)
       have hd:0≤Real.exp δc * t:= mul_nonneg (Real.exp_nonneg _) hu
       linarith only [he',hd] -- t.A shape
    let d1:= jewelDebt M' Q L x
    have hξ:0≤d1:=dew M' H |>.2.1
    have hg: Charity.flareC (x:=x) (j:=p) B.power Y ≤ t* Real.exp ((1/2)*D):=by
       unfold t volt; unfold Charity.flareC D; rw [hm,mul_pow,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by unfold shiftG; positivity)
       exact polynomial_cost (by norm_num : (0:ℝ)< 1/2) (by positivity) _
    refine ⟨_,hv,?_⟩
    let f := R.p.mass M'.crest M'.weight
    have hp :0≤f:= M'.profit.trans (R.p.loMass _ _ M'.profit)
    have ho:d1≤(Q.goal L x)⁻¹*f:=by
       have he: Real.exp (-Q.ε*coverNumber R.p.B M'.crest) ≤1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Q.usable.le) (by positivity))
       unfold d1 jewelDebt; rw [div_eq_mul_inv,mul_comm _ _⁻¹]; exact mul_le_mul_of_nonneg_left (le_trans (mul_le_of_le_one_right hp he) le_rfl) (inv_nonneg.mpr (Real.rpow_nonneg hz.le _))
    have hF: Real.exp ((B.supportExponent+2)*D) * Real.exp ((1/2)*D) ≤ Real.exp ((a+e)*D) := by
       rw [← Real.exp_add]; apply Real.exp_monotone
       linarith only [mul_le_mul_of_nonneg_right hS hD, mul_nonneg hK.post.le hD,hD]
    unfold Push.Local.reservedMass
    calc
      _ ≤ Real.exp ((B.supportExponent+2)*D)*((d1*o0)*(t*Real.exp ((1/2)*D))) := by
           apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; exact mul_le_mul_of_nonneg_left hg (mul_nonneg hξ hd)
      _=(d1*t)*(o0*(Real.exp ((B.supportExponent+2)*D)*Real.exp ((1/2)*D))):=by ring
      _ ≤ (d1*t)*((o0*Real.exp ((a+e)*D))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hd) (mul_nonneg hξ hx)
      _ ≤ (d1*t) := mul_le_of_le_one_right (mul_nonneg hξ hx) ha
      _ ≤ (((Q.goal L x)⁻¹*f)*t) := by gcongr
      _ = (volt x p B.power*(Q.goal L x)⁻¹) * R.p.mass M'.crest M'.weight:=by unfold t f; ring
end YM.PhysicalNext.Repeat.Mercury

