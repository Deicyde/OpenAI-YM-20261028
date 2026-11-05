import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Regale
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Sage
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Stocks
/-!
# `Pitch` payment for the unmarked assembly

After-L epistemic suppliers submitted alongside schedule here, buy them separately.
Only one chart. `Ancestor` already actually buys E pricing all path classes.
Hefts spend and slab bounds at Playing; Borel requirements
 on Matched throughout (clamp Books to get uniform visible charges).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew Pot Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk Coffer Port Physical Barge EndpointLoadF16.DetLong
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x y W a e L C u d ε η g b : ℝ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S} {hQ : Chips v P W x}
open Next.Rank.Perch
def tenders (v : Dyed G S) (p:Pilot G S x):= penury v p+tallyQ v p+froth v p+(nightly v p+(introTax v p+showTax v p))+lining v p+ Ancestor.terra v p

def posting (v : Dyed G S) (r:Core S x) (p:Pilot G S x):= center r v p + rents r v p
lemma issued (h : Chips v P W x) (he : 0≤ e) (hV : Matched p) (hm : Certified S v.things x g C η b)
    (h0 : Physical.parcel G S 20 e g C b d (radiusB x) 0) (h1 : Physical.parcel G S 20 e g C b d (radiusB x) 1) : v.spoolLift p=(∑ j∈owners p.key x, posting v j p)+tenders v p:= by
  unfold posting tenders Dyed.spoolLift; dsimp only; rw [sum_add_distrib,rate_pass h hm hV he h0 h1]
  rw [Port.results v p|>.1, Port.results v p|>.2, froth,(voyage hm h.boost hV).tsum_eq]
  have hl:= Coffer.reindex v p; unfold dues at hl; simp_rw [←mul_sum] at hl
  unfold Ancestor.terra; change _=_
  -- align levy
  simp only [Dyed.combo] at hl; rw [hl]
  unfold Dyed.tapeAt displaced; ring
-- risk Event cash tap for logdet
private lemma discounts {a : ℝ} (ha : 0<a) :∀ᶠ x in atTop,currency a (radiusB x) ≤ x^(-(5:ℝ)):= by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (5/a)),eventually_gt_atTop (0:ℝ)] with x hx he
  let p:=Real.log x; let f:ℝ:=radiusB x
  have ha : 5 ≤ a*p:=by simpa only [mul_comm] using ((div_le_iff₀ ha).1 ((le_max_right ..).trans hx))
  rw [Real.rpow_def_of_pos he]; refine Real.exp_le_exp.mpr ?_
  have hl: 0 ≤ p:= zero_le_one.trans ((le_max_left ..).trans hx);
  change -a*f ≤ p*(-5); linarith only [mul_le_mul_of_nonneg_left (show p^2 ≤ f from Nat.le_ceil (p^2)) (show 0 ≤ a from ‹0<a›.le),mul_le_mul_of_nonneg_right ha hl]
private lemma drives (D : Patch) (e : ℝ) (he : 0≤e) : ∀ᶠ x in atTop,∀ {c f : Side} (S : StepData c f),S.patch=D→
    Ac.Hit (pond S x) (radiusB x) (fun _=>4*Aff.weight*x^(-(1/4):ℝ)) e (x^(-(1/8):ℝ)):= by
  let H:= Aff.densityRack D.L; let v:= 4*Aff.weight; have hv:0≤v:= mul_nonneg zero_le_four Aff.weight_pos.le
  have hh:0≤H:=by unfold H Aff.densityRack Aff.densityF Aff.densityC; positivity
  filter_upwards [Grid.poly_hit hh hv (show (1/8:ℝ)<1/4 by norm_num) he 420,eventually_gt_atTop (0:ℝ)] with x hx h c f S hS
  subst D; refine hx _ (grantPlace S) _ ?_ (fun i=>Finset.Subset.refl (pond S x i)) _ (fun i=>⟨mul_nonneg hv (by positivity),le_rfl⟩)
  convert! Aff.governs_booth S using 1; funext i; rcases i with ⟨s,i|i|i|i⟩ <;> rfl
-- combine clamping supports incl mask-excluded addresses
lemma paltry (h : Chips v P W x) (h₁ : 100*(1+radiusB x) ≤ c.val) (_hv : Certified S v.things x g C η b) (hg : Bid.LaneCounts v.things.up x v.source.p.threshold v.things.high e 1 S.ratio.parent)
    (hM : Hefts S P x L v.source.p.threshold a W) (hw : v.arc=L*fiery G x S.patch.L) (ha : 0≤a) (hl : noises v u x) (hL : ∀ i p,Matched p → v.Playing W p → |lapse v i (p:Pilot G S x)| ≤ ε)
    (hR : ∀ (p:Pilot G S x),Matched p → ∀ i,|rents i v p|≤ y * (i:Core S x).val.shares) {r : ℝ} (ht : y+r ≤ v.source.beta*(a*v.source.p.threshold^2)) :
      ∃ f : Core S x→ Pilot G S x→ℝ, (∀ i, Pulled (f i) (acre i)) ∧ (∀ i,Opaque (f i)) ∧
        (∀ p i, Matched p → f i p≤ -r*i.val.shares) ∧ ∀ p i, Matched p → v.Playing W p → i∈owners p.key x → f i p = posting v i p:= by
  obtain ⟨u,hm⟩:= minimum h ha h₁ hM rfl hw hl hL
  let A (i:Core S x):=-r*i.val.shares; let B i:= min (A i) (u-y*(i:Core S x).val.shares); let f i p:= max (B i) (min (A i) (posting v i p))
  have he i p : B i ≤ f i p ∧ f i p≤ A i := ⟨le_max_left ..,max_le (min_le_left ..) (min_le_left ..)⟩
  refine ⟨f,fun i=> ((center_read h hg i).plus (rents_read i h.boost)).twine ((continuous_const.max (continuous_const.min continuous_id)).measurable),fun i=>⟨|B i|+|A i|,fun p _=> abs_le.mpr ⟨?_,?_⟩⟩,fun i p he'=> (he p i).2,fun p i hx hh hi=>?_⟩
  · linarith only [(he i p).1,neg_le_abs (B i),abs_nonneg (A i)]
  · linarith only [(he i p).2,le_abs_self (A i),abs_nonneg (B i)]
  obtain ⟨h',hr⟩:= abs_le.mp (hR p hx i); unfold f; rw [min_eq_right,max_eq_right]
  · apply (min_le_right ..).trans; change u-y* (i.val.shares:ℝ) ≤ center i v p + rents i v p; linarith only [h',hm p hx hh i hi]
  unfold posting A; linarith only [ranked h h₁ hM rfl hw hx hh i hi,mul_le_mul_of_nonneg_right ht (show 0 ≤ (i.val.shares:ℝ) by positivity),hr]

private lemma drought :∀ᶠ x:ℝ in atTop,let q:= x^(-(1/8):ℝ); let a:= x^(-(1/24):ℝ)
    let u:= x^(-(5:ℝ)); let l:= q+q+x^4*u+(q+(u+u))+q+a
    2*l ≤ Grid.garlic x ∧ l≤1:= by
  filter_upwards [slack 16 (by norm_num:(-(1/24):ℝ) < -(1/48)),eventually_ge_atTop (1:ℝ)] with x hx he
  intro q a u l; have h0:0<x:= zero_lt_one.trans_le he
  have hv : x^4*u≤q:= by
    nth_rw 1 [← Real.rpow_natCast (_:ℝ) 4]; unfold u; rw [← Real.rpow_add h0]; apply Real.rpow_le_rpow_of_exponent_le he; norm_num
  have hz:2*l ≤ Grid.garlic x:= by
    refine le_trans ?_ hx; change 2*l ≤ 16*a; have hx:u ≤ x^4*u:= le_mul_of_one_le_left (Real.rpow_pos_of_pos h0 _).le (one_le_pow₀ he)
    unfold l; linarith only [hx,hv,show q≤a from Real.rpow_le_rpow_of_exponent_le he (by norm_num)]
  exact ⟨hz,by linarith only [hz,show Grid.garlic x≤1 from Real.rpow_le_one_of_one_le_of_nonpos he (by norm_num)]⟩

/-- Per step on the weak retimed panel. `Hefts` already built after-L still has all-A
hypotheses. Prop-specific proof: `Lantern` not chosen here. No comparison on `Resin` or
summing determinant voices across chart profiles. -/
structure Helps (v : Dyed G S) (P : Teller G) (W L x a t e : ℝ) :Prop where
  hats : Chips v P W (retime x)
  larger : Bid.Larger (G:=G) S
  counts : 100*(1+radiusB (retime x)) ≤ c.val
  grown : ∃ H K, Aff.Alongside H K v.things
  width : v.arc = L * fiery G (retime x) S.patch.L
  heights : v.source.beta ∈ Set.Icc (betaF G x S.patch.L/2) (2*betaF G x S.patch.L)
  feet : v.source.p.threshold= Next.Rank.Paint.phase (betaF G x S.patch.L)
  flag : v.source.p.threshold ∈ Set.Icc (fiery G (retime x) S.patch.L/2) (2*fiery G (retime x) S.patch.L)
  heft : Hefts S P (retime x) L v.source.p.threshold a W
  budget : Footprint.reserve v.source.p.supportExponent e (Footprint.conversion S.ratio 1) t
  can : v.bp.B ≤ walls (retime x) ∧ v.source.p.B≤2*v.bp.B ∧ 25*radiusB (retime x)+30 ≤ v.bp.B
  funds : ∃ Γ δ w, v.source.Lawful P.top.width P.top.paths Γ δ w ∧ Γ ≤ betaF G (retime x) S.patch.L ^(1/8:ℝ) ∧ δ ≤ (retime x)^(-(1/2):ℝ)
  lanes : ∃ m,Bid.LaneCounts v.source.path (retime x) v.source.p.threshold v.source.clip m 1 S.ratio.parent
lemma foreshadows {η' t α : ℝ} (P : Teller G) (Q : Fund) (J : ChartRatio G) (hJ : LocalRatio J) (D : Patch) (hD : D.Branches P.bind G)
    (he : 0≤ e) (hC : 0≤ C) (hg : 0< g) (hb : 0< b) (hd : 0<d) (ht :0<t) (hv :0≤L) (ha : 0<a) (hA :0<α) (h : 2*α≤ a/2) : ∀ᶠ x in atTop,
      ∀ {c f : Side} (S : StepData c f) (v:Dyed G S) (W u : ℝ), S.patch=D → v.ratio=J → Helps v P W L x a t e →
        let y:=retime x; let B:=radiusB y; let z:= betaF G x S.patch.L
        Q.Stock P D 20 2 1 e y → noises v u y → Certified S v.things y g C η' b →
        Physical.parcel G S 20 e g C b d B 0 → Physical.parcel G S 20 e g C b d B 1 →
        ∃ M : Plate v y W,(∀ p i,Matched p → M.base i p ≤ -(α*hot z^2) * (i:Core S y).val.shares) ∧
          ∃ f:Glade c →ℝ,(∀ i,0 ≤ f i)∧ Ac.Hit (fun i:Glade c=> i.val) v.bp.B f e (Grid.garlic y) ∧∀ i p,Matched p→ |Real.exp (M.aux i p)-1|≤f i:= by
  let R:= Work.E01.radiusB_tendsto
  filter_upwards [tall_limit.eventually (Ancestor.abound P D e t he ht), tall_limit.eventually (margin P D hD L hv), tall_limit.eventually (bolsters D J hJ L hv e he), tall_limit.eventually (bills P D Q e he), wages D J C hC α hA,
    tall_limit.eventually (R.eventually (embark he hb hg hC G D 40 (by norm_num))), tall_limit.eventually (discounts hd),tall_limit.eventually (discounts (show 0<b/3 by positivity)),tall_limit.eventually (drives D e he),tall_limit.eventually drought, burst_limit, eventually_ge_atTop (G.slopeConstant*Real.log D.L.val), eventually_gt_atTop (0:ℝ)] with x hE hm ht' hL hw he' h1 h2 hc hU hx hω hy c f S v W u hP hJ' hp
  intro y B z ht H H' h0 hb'
  subst D J; let w:= v.source.beta; let s:=v.source.p.threshold
  have he : 0<z := hy.trans_le (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)); have hz:0<y:= hy.trans_le hx.1
  have hy : w ≤4*y := by
    have hl:z≤2*x:=by unfold z betaF; linarith only [hω]
    have hb:w ≤ 2*z:= hp.heights.2; linarith only [hb,hl,show x ≤ y from hx.1]
  obtain ⟨H₁,H₂,hH⟩:= hp.grown; have hh := hm S v rfl W hp.hats hp.counts hp.larger H₁ H₂ hH hy hp.width.le hp.flag.1
  obtain ⟨u',hu⟩:= hp.lanes; have hG : Bid.LaneCounts v.things.up y s v.things.high u' 1 S.ratio.parent := by rw [hp.hats.paths,hp.hats.clips]; exact hu
  let C₀:=α*hot z^2
  have hK:0 ≤ C₀:=mul_nonneg hA.le (sq_nonneg _)
  have hKok : C₀+C₀ ≤ w*(a*s^2):= by
    have hg : z*s^2=hot z^2:= by unfold s; rw [hp.feet,Next.Rank.Paint.phase]; change z*((Real.sqrt z)⁻¹*hot z)^2= _; rw [mul_pow,← mul_assoc]; rw [inv_pow,Real.sq_sqrt he.le,mul_inv_cancel₀ he.ne',one_mul]
    have hb:z/2 ≤ w:= hp.heights.1; refine le_trans ?_ (mul_le_mul_of_nonneg_right hb (mul_nonneg ha.le (sq_nonneg (s:ℝ)))); unfold C₀; linarith only [mul_le_mul_of_nonneg_right h (sq_nonneg (hot z)),show a*(z*(s^2))=a*hot z^2 from congr_arg _ hg] -- assoc
  obtain ⟨p,hm,hᵤ,hv,hR⟩:= paltry hp.hats hp.counts H' hG hp.heft hp.width ha.le H hh (hw S v _ _ _ rfl rfl hJ hp.heights H') hKok
  have h₀ : ∀ r, Matched r → v.Playing W r → v.spoolLift r = (∑ i∈owners r.key y,p i r)+tenders v r:=by
    intro r hQ hf; rw [issued hp.hats ‹0≤e› hQ H' h0 hb']; exact congr_arg (· + tenders v r) (sum_congr rfl (fun i hi=> (hR _ _ hQ hf hi).symm))
  let q:= y^(-(1/8):ℝ); let bX:= y^(-(1/24):ℝ); let ν:= y^(-(5:ℝ)); let l:= q+q+y^4*ν+(q+(ν+ν))+q+bX
  obtain ⟨h5,h6⟩:= billIt hp.hats H' hC ‹0 ≤ e› h0 hb'; obtain ⟨h8,h9⟩:= ht' S v rfl rfl P W u H hp.hats hp.width.le
  obtain ⟨Γ,δ,w,hV,hΔ,hδ⟩:=hp.funds
  have hF:= hE c f S v W u' rfl hp.hats hu hp.can.1 hp.budget hp.can.2.1 hp.can.2.2 hy hp.flag.2 Γ δ w hV hΔ hδ
  have hvF : B≤v.bp.B:=by change radiusB (retime x) ≤ _; have ht:=hp.can.2.2; omega
  have hl:= hL S v.things v W g C η' b rfl rfl hp.hats hp.counts ht H'
  have hP : Petty v W B e q (penury v (x:=y)):= Petty.acceptsList (L:=lapse v) (ι:= Grain S) (fun i=>lapse_read hp.hats hG i)
    (fun i=> ⟨_,halo_subset _ _ (mem_singleton_self _)⟩) (fun _=> mul_nonneg (mul_nonneg zero_le_four Aff.weight_pos.le) (Real.rpow_pos_of_pos hz _).le) (hc S rfl) ‹0≤e› hh
  have he₁:= paid_froth hp.hats H' H hC ‹0 ≤ e› (he' S rfl)
  have hT : Petty v W v.bp.B e l (tenders v (x:=y)):= by
    exact (((hP.plus h9).plus (he₁.across (mul_le_mul_of_nonneg_left h2 (by positivity))) |>.plus (hl.plus ((h5.across h1).plus (h6.across h1))) |>.plus h8).walk ‹0≤e› hvF).plus hF
  obtain ⟨M,hM,f,ht,hk,hA⟩:=issue_invoice hp.hats H' p hm hᵤ hU.2 ‹0≤e› hv h₀ hT; exact ⟨M,(fun i p hP=> hM p i hP),f,ht,fun i=>budget_loosen (hk i) hU.1,hA⟩
end YM.PhysicalNext.InteractingRank.Pump
