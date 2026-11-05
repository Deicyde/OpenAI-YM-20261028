import YM.FullVolume.Florid.Hearts
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' fq:ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
variable (D: dust j o χ L x₀ d fq)
open Lyre Charity Blaze.March
variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
variable {V':ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V' k)
variable (Y':Margin G L x₀ α δ) (w:Rung) (η:ℝ) (hh : ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ η)
set_option quotPrecheck false
local notation "τ"=> V.pole.turn.badge S
local notation "Q'" => Empire.stella Q
local notation "Φ"=> jewelDebt V.pole (Empire.stella Q) L x₀
local notation "B₀" => radiusB x₀
local notation "π"=> Lyre.spicesF G (r+fq) L' (V' x₀) K j
-- selected under stellar props. Keep Φ factors integrated outside tree.
local notation "hτ" => lushE M V α ν (π) p (k+j)
open Greenbelt
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March Match
local notation "π₀"=> Lyre.spicesF G r L' (V' x₀) K j
local notation "e₁"=> hopes M V (spicesF G r L' (V' x₀) K j) (π) α ν (k+j) p
local notation "X"=> fun i:H.ThinP=> chargeM M V (spicesF G r L' (V' x₀) K j) (π) α ν (k+j) p i
local notation "X₀" z=> H.bookFoot (.inr z)
variable (hp:foam Q L)(hb:R.p.B≤2*radiusB x₀)(hA:(Daisy.swing (stella Q) L μ R.beta x₀ ν).Buy S.patch.L Q.halo (radiusB x₀))(hv:2≤v)
set_option quotPrecheck false
abbrev billsD (Q:Target G P)(b c:ℝ)(L:Side)(μ x:ℝ)(j k:ℕ):ℝ:= (2:ℝ)^(j+2)*( (1+2*b)*(stella Q|>.overture L μ x k)+2*c*(Daisy.swing (stella Q) L μ 1 x 0).ceiling 0 k 0 0)
local notation "δ₀"=> billsD Q (π₀) (π) L μ x₀ j (k+j)
local notation "P₀"=>FullVolume.Ray.Weigh.pattern j
abbrev ruby (n:ℕ)(i:H.fragrances):ℝ:= if speaks V.pole H i then (shiftG x₀*(1+(coverNumber B₀ (H.bookFoot (.inr i)):ℝ)))^(n*j)*P₀*(Φ*(e₁ i)) else 0
include D hp hb hA hc hr W' Y' hv M V
lemma marginalS {e:ℝ} (he:0≤e)(ht:e+3*α≤ Q.exp)(hg: Trees.degreePrice B₀ δ₀ α ≤ 1/2)(y:Site c)(hy:y∈ V.pole.crest.image S.ratio.parent)(n:ℕ):
    SumBudget (fun i:H.fragrances=>ruby (fq:=fq) (V':=V') (k:=k) (p:=p) (ν:=ν) (α:=α) M V n i * Real.exp (e*(coverNumber B₀ (locus V.pole H y i)))) (Φ*( P₀*(March.collars G α x₀ j n *(δ₀*(1-1/2)⁻¹)))):=by
  let u(i:H.ThinP):= (2:ℝ)^(j+2)*(X) i
  have ht':0 < α:=Y'.hp; let a:=Φ; have ha:0 ≤ a:= scentL V.pole H|>.2.1
  let b:= (π₀)* (stella Q|>.overture L μ x₀ (k+j)); let c:= (π)* (Daisy.swing Q' L μ 1 x₀ 0).ceiling 0 (k+j) 0 0
  have hx':0< (stella Q|>.overture L μ x₀ (k+j)):=by
     apply Target.overture_pos; have h:=H.laws.intake.height;rw [H.laws.data.funds.length_eq] at h;linarith
  have hs:=M.spicesF_sound (V' x₀); have hx := buoyant M (V' x₀) D; have hC: Ac.Hit H.smallAt B₀ (hτ) (Q.exp-α) c:= stipend M V D hc hp hb hA (k+j) (π) hx
  have htK: Ac.Hit H.smallAt B₀ (X) (Q.exp-α) (2*b+2*c):= by
     intro i; have he:= budget_plus (budget_scale zero_le_two (M.purchases (α:=α) (k:=k) (V:=V') hc i)) (budget_scale zero_le_two (hC i));convert! he using 2; rename_i j; split; unfold chargeM; ring; ring
  have hE(i:H.ThinP): 0 ≤ (X) i:= add_nonneg (mul_nonneg zero_le_two (M.paid_sky ..)) (mul_nonneg zero_le_two (prosp M V D hc hp hb hA _)); have hu i:0≤u i:=mul_nonneg (by positivity) (hE i)
  have hB:0≤b:=mul_nonneg hs hx'.le; have hx:0≤c:=budget_nonneg (hC y)
  have hz:δ₀=(2:ℝ)^(j+2)*((stella Q|>.overture L μ x₀ (k+j))+(2*b+2*c)):=by unfold billsD b c; ring
  have hR: Trees.Ready H.smallAt B₀ u (e+α) δ₀ α (1/2) := by
     refine ⟨by rw [hz]; positivity,ht',hg,by norm_num,hu,fun z=>?_⟩; let t:=(2:ℝ)^(j+2); have hh:0≤t:=by unfold t; positivity
     refine budget_loosen (budget_mono (budget_scale hh (htK z)) ?_ ?_) ?_
     · intro i; split
       · exact mul_nonneg (hu _) (Real.exp_pos _).le
       rfl
     · intro i; split
       next hx=> change t*((X) i)*Real.exp _ ≤ t*(_ * _); rw [mul_assoc]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hE _)) hh; exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
       rw [mul_zero]
     rw [hz]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx'.le) hh
  have hP:0 ≤ P₀:= Finset.sum_nonneg fun _ _=> zero_le_one.trans (Planned.AtomRegular.polar_one _)
  let x:= March.collars G α x₀ j n; have hX:0 ≤ x:=by unfold x March.collars shiftG Reserves.polyPrice; positivity
  have hF:= Ursell.log_hit_tail _ _ _ H.testS hR (add_nonneg he ht'.le) 0 y; rw [pow_zero,mul_one] at hF
  have hY:= budget_scale ha (budget_scale hP (budget_scale hX hF)); refine budget_mono hY (?_) fun i=> ?_
  · intro i; unfold ruby; split; · exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by unfold shiftG; positivity) _) hP) (mul_nonneg ha (energy M V D hc hr W' Y' hp hb hA hv _))) (Real.exp_pos _).le
    rw [zero_mul]
  unfold locus ruby; split
  next h=>
    have hf : y∈H.bookFoot (.inr i):=by have hx:= seatY V.pole H _ hy i; rwa [Charity.locus,if_pos h] at hx
    rw [if_pos (show 0 ≤ i.fst ∧ y∈ unionOf H.smallAt i.snd from ⟨Nat.zero_le _,hf⟩)];
    let d:ℝ:=coverNumber B₀ (H.bookFoot (.inr i)); have hd:0≤d:=Nat.cast_nonneg _
    change (shiftG x₀*(1+d))^(n*j)*P₀*(a*(e₁ i))*Real.exp (e*d) ≤ a* ( P₀ * (x *((e₁ i)*Real.exp ((e+α)*d))))
    rw [mul_pow]; unfold x March.collars; rw [add_mul,Real.exp_add]
    have hvK : (1+d)^(n*j) ≤ Reserves.polyPrice α (n*j)* Real.exp (α*d):= polynomial_cost ht' hd _
    apply (le_trans (?_ : _ ≤ shiftG x₀^(n*j)*( Reserves.polyPrice α (n*j)* Real.exp (α*d)) *P₀*(a*(e₁ i))*Real.exp (e*d)) (le_of_eq (by ring))); have hu:= energy (Y':=Y') M V D hc hr W' hp hb hA hv i; have hh:0≤ shiftG x₀:=by unfold shiftG; positivity
    gcongr
  rw [zero_mul]; exact hY.1 i
lemma resumes {cv:ℝ}{B:BudgetPoint}(he:B.order=j)(hT:B.threshold=Pressure.temp x₀)(hg:Sailor G B.threshold cv j)(h:0≤ cv)(hn:j*cv ≤ u) (y:Site c)(hy:y∈ V.pole.crest.image S.ratio.parent)(i:H.fragrances)(w:Rung)(η:ℝ)(hK:Stripe w (v/2) η): B.supBounds y (locus V.pole H y i) (fun x=> Jams.mix w (fun t=> signalAt V χ t i x)) (η* ruby (fq:=fq) (V':=V') (p:=p) (α:=α) (ν:=ν) (k:=k) M V B.power i):=by
  unfold Charity.locus ruby; split
  swap; next hx=>
     rw [show (fun x=> Jams.mix w (fun t=> signalAt V χ t i x))=0 from ?_,mul_zero]; swap;· funext U; refine sum_eq_zero fun t _=>smul_eq_zero.mpr (Or.inr (congr_fun (quiet (V.flies t) _ χ _ (fun hp=> hx ((V.reached t i).2 hp))) _))
     exact AnalyticBridge.VerifiedReset.sup_le (p:=B) (AnalyticBridge.VerifiedReset.sup_const _) (le_of_eq abs_zero)
  next hx=>
  let r:=coverNumber B₀ (Captain.reachability i); let z':= (shiftG x₀*(1+r)); have hs :1≤ shiftG x₀:=by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x₀)]
  have hz:1≤z':= one_le_mul_of_one_le_of_one_le hs (by simp); have hh':0≤η:= stripe_pos hK
  have hQ:0≤FullVolume.Ray.Weigh.pattern j := Finset.sum_nonneg fun i _=> zero_le_one.trans (Planned.AtomRegular.polar_one i)
  refine ⟨mul_nonneg hh' (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hz) _) hQ) (mul_nonneg (scentL V.pole H|>.2.1) (energy M V D hc hr W' Y' hp hb hA hv i))),?_⟩
  have hf : y∈ Captain.reachability i:=by have hv' := seatY V.pole H y hy i; rwa [Charity.locus,if_pos hx] at hv'
  intro A hA l hl hl₀; have hu:= celia M V D hc hr W' Y' hp hb ‹_› hv i A (hT ▸ hA) w η hK
  let f x:= Jams.mix w (fun t=> signalAt V χ t i x); refine (March.costsD (g:=f) (Z:=Captain.reachability i) ?_ hg h y _ hn hu («Y»:=z') ?_ hz l (hl.trans he.le) hl₀).trans_eq ?_
  · intro C D ha; apply Finset.sum_congr rfl; intro t _; apply congr_arg (fun x:ℝ=>w t*x)
    let Y:= V.flies t
    apply historic (H:=U.beams _ (U.lay t.property)) Y ((recital U t).furrow i) C D; rw [reaches]; exact ha
  · intro x hx; have ht':(separation x y:ℝ) ≤ r * (4*(radiusB x₀:ℝ)+2)+2*(radiusB x₀:ℝ) := by unfold r; exact_mod_cast Lattice.Corona.extent _ _ hx hf
    unfold z' shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) (radiusB x₀)]
  change z'^(B.power*j)* _ = η*(z'^(B.power*j)*P₀*(Φ*(e₁ i))); ring
end Mill
end YM.ConnectedActivityE6.Empire.Imago
