import YM.RemainderComparison.Sagas.Canine
/-! # Concrete thresholds.Height.θ in Pose certificates. Exponential width receipts.
Inputs extra affine norm/assertion retained by RU3. In these grants permit gauges of any rank through N. OPEN general WΦ.Structural Authenticity. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sagas
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Portal Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{L:Side}{α:Type*}
variable {R:Rep G f} -- edit {R : }
variable (p:BudgetPoint)(β:ℝ)
namespace Packet
variable {αP δ' t b η x B:ℝ}{n k r:ℕ}
open Time WickReps
variable {p}
lemma fee (p:BudgetPoint)(Q:Packet G f α)(β:ℝ) : 0 ≤ Q.eats β p:=by unfold Packet.eats; have hp:0 ≤ gStep β:= inv_nonneg.mpr (Real.sqrt_nonneg _); have he:0 ≤ Q.rent p:= mul_nonneg (fare_aux ..) (pow_nonneg (by positivity) _); have ht:= Q.suspension; have hv:=p.threshold_pos; positivity
-- E stationary. Spine Ω invoices from Perse.Weft.Mark 
variable {V:Set ℕ}(P : ℕ→Packet G f Unit)
local notation "S" => R.activities
local notation "X"=> gStep R.beta
local notation "B₁"=> R.p
variable (F:RG.Stage)(h: Time.Same F R.p) (hp:0<R.beta)(hβ:gStep R.beta≤1){ξ:ℝ}
variable (he:0<ξ)(hd: t + R.p.supportExponent*δ'+ξ ≤ η)
-- Verify producers.Supply input ancestors any given req. R.Rite.Good.
structure Sown (V:Set ℕ) (k n r:ℕ)(x κ d η B:ℝ): Prop where
   footprints : ∀ i∈V, (P i).postage=(R.activities.reg i)
   encodes : ∀ i∈V,(R.activities.E i)= (P i).send R.beta ()
   height (i:ℕ) : i∈V→ (coverNumber R.p.B (P i).postage.support:ℝ) ≤ κ + d*(P i).length
   geometry i : i∈V → (P i).length< Stores.till x → (P i).postage.support⊆ neighbors r (P i).postage.site
   rank : ∀ i∈V,(P i).rank≤k
   entrances : ∀ i∈ V,n≤(P i).grade
   cost (y: Site f) : SumBudget (fun i=> if i∈V ∧ (P i).postage.site=y then (P i).weight*Real.exp (η*(P i).length) else 0) B
variable (hC:Packet.Sown P (R:=R) V k n r x αP δ' η B)
local notation "μW"=> music G F ξ R.p.supportExponent αP n k R.beta R.p.threshold
set_option quotPrecheck false
local notation "fK"=> fun i:ℕ=> if i∈V then (P i).eats R.beta R.p else 0
include h hβ hC hp he hd
lemma seats_le : Nursery.Kraft (x:=x) (R:=R) Vᶜ (fun i=>(P i).length) r t (μW*B):=by
    let q :ℕ→ℝ:= fK; let Hv:= μW
    have hx:0 ≤ Hv:=by have hz:= (Fare.gS _ hp).1; have hq:= Packet.tolls G F ξ k; have he:= R.p.threshold_pos; unfold Hv music; positivity
    have hn :∀ i,0 ≤q i:=fun i=>by unfold q; split; exact Packet.fee ..; exact le_rfl
    refine ⟨fun i hi hu=>?_,q,hn,fun i hi=>?_,fun j=>?_⟩
    · by_contra hx; obtain ⟨y,hy,hx'⟩:= hu; have he:= hC.footprints i (Classical.byContradiction hi); rw [←he] at hy hx'; exact hx' ((neighbors_mem ..).1 (hC.geometry i (Classical.byContradiction hi) (by omega) hy))
    · rw [hC.encodes i (Classical.byContradiction hi), ← hC.footprints i (Classical.byContradiction hi),show q i = _ from if_pos (show i∈V from Classical.byContradiction hi)]; exact (Packet.solo R.beta (P i) R.p () hp).2 -- implicit inspect
    have he':= Cost.scale (hC.cost j) Hv hx
    apply budget_mono he'; · intro i; split; exact mul_nonneg (mul_nonneg (hn i) (Real.exp_pos _).le) (Real.exp_pos _).le; exact le_rfl
    intro i; dsimp only; split; next hi=>
      by_cases hi':i∈V
      · rw [if_pos (show i ∈ V ∧ _ from ⟨hi',(congr_arg RG.RegularAddress.site (hC.footprints i hi')).trans hi⟩),show q i= _ from if_pos (show i∈V from hi'),mul_assoc]; unfold Raw.regularExtra; rw [← hC.footprints i hi']; exact @Packet.glow G f Unit R.p R.beta (P i) ξ αP δ' t R.p.supportExponent η n k F h hp hβ he (hC.rank i hi') (hC.entrances i hi') (R.p.exponent_pos.le) (hC.height i hi') hd -- edit
      rw [show q i = 0 from if_neg hi',zero_mul,zero_mul]; exact he'.1 i
    next=> exact he'.1 _
end Packet
end YM.RemainderComparison.Sagas
