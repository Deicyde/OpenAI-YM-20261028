import YM.UVExtension.Tide.Lagoon
import YM.MergeProof.Baskets
/-! # Real one-field rapid comparison on grid-scaled layouts. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tide
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (hG:G.Simple)(A:Levels G)
open Stock
local notation "S"=> A.S
local notation "p!"=> A.params
local notation "b0"=> A.clock
variable (h:Tabs A)
private def stepX (m:ℕ):= (A.params m).columns
private lemma oneStep (a d:ℝ)(ha:0<a): ∀ᶠ i in atTop, Real.exp (Work.D01.columnLogs A i)*(1+stepX A i)*d ≤ expS A.S a i:=by
    let H(i):=Real.exp (a/4*A.S.scale i); have ht:Tendsto (fun i=> H i) atTop atTop:= Real.tendsto_exp_atTop.comp (A.S.divergent.const_mul_atTop (by positivity))
    have hl(m:ℕ)(hm:0< m) : Real.log (p! m).columns ≤ Work.D01.columnLogs A m:=by
       cases m with| zero=> omega| succ m => rw [Work.D01.columnLogs_succ]; exact le_add_of_nonneg_left (Work.D01.columnLogs_nonneg ..)
    filter_upwards [ht.eventually_ge_atTop 2,Work.D01.columnLogs_le A (a/4) (by positivity), ht.eventually_ge_atTop d,eventually_gt_atTop 0] with i hh hk he hK
    have hs:H i>0:=Real.exp_pos _; have h₁:Real.exp (Work.D01.columnLogs A i)≤H i:= Real.exp_monotone hk; have hx: 0 ≤ stepX A i:= zero_le_one.trans (p! i).columns_ge
    have hX : 1+stepX A i ≤ H i* H i:= by
        apply le_trans (b:=H i+ H i); swap; · nlinarith only [hh,hs]
        refine add_le_add (le_trans one_le_two hh) ?_; nth_rw 1 [← Real.exp_log (zero_lt_one.trans_le (show _≤ stepX A i from (p! i).columns_ge))]; exact Real.exp_monotone ((hl _ hK).trans hk)
    apply (mul_le_mul_of_nonneg_left he (mul_nonneg (Real.exp_pos _).le (by linarith only [hx]))).trans; apply (mul_le_mul_of_nonneg_right (mul_le_mul h₁ hX (by linarith only [hx]) hs.le) hs.le).trans; unfold H expS; apply le_of_eq; simp_rw [← Real.exp_add]; ring_nf
set_option quotPrecheck false
local notation "κ"=> Tabs.chosen A 1 h
include hG
lemma scaleLoan : ∀ᶠ j in atTop, A.S.scale (Tabs.chosen A 1 h j) ≤ 2*A.S.scale j ∧ (A.S.a j/A.S.a (Tabs.chosen A 1 h j)) ^ (4:ℕ)*Vac.treasury A (Tabs.chosen A 1 h j) ≤ A.S.scale j := by
    let t:=κ; have hh(i:ℕ):i≤t i:= (Tabs.opened ..).1; have ht : Tendsto t atTop atTop:= tendsto_atTop_mono hh tendsto_id
    filter_upwards [h.pay A 1 le_rfl (1/2) (by norm_num),ht.eventually (Vac.treasury_stage A hG)] with i hi hT
    let r:= t i; let w:= A.S.a i/A.S.a r; let q:= Vac.fiat G (A.params r) (A.clock.hatBeta r); have he: w^4*q≤ 1/2*A.S.scale r:= hi
    have hf: 1≤ w:= (one_le_div (A.S.a_pos r)).2 (A.S.strictAnti.antitone (hh i))
    have hQ:1≤ q:=by
       unfold q Vac.fiat; have he := (A.params r).paths_pos; have ha := (A.params r).clip.quadratic_pos
       have hp : 0≤ (Fintype.card PlaqAxes:ℝ)*((A.params r).clip.direct + (A.params r).paths^2) + 4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log (A.clock.hatBeta r)/2) := by
          have hu := Real.log_pos (A.fits.delayed r); positivity
       linarith only [hp,he]
    have h₁: A.S.scale r ≤ 2*A.S.scale i:=by
       have hz: A.S.scale r - A.S.scale i ≤ (1/2)*A.S.scale r := by
           apply le_trans _ he; rw [show A.S.scale r - A.S.scale i= Real.log w by unfold Schedule.scale w; rw [Real.log_div (A.S.a_pos i).ne' (A.S.a_pos _).ne', Real.log_inv, Real.log_inv]; ring]; exact (Real.log_le_self (zero_le_one.trans hf)).trans (le_trans ((pow_one w).symm.trans_le (pow_le_pow_right₀ hf (show 1 ≤ 4 by norm_num))) (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hf) _) hQ))
       linarith only [hz]
    exact ⟨h₁,(mul_le_mul_of_nonneg_left hT (pow_nonneg (zero_le_one.trans hf) 4)).trans (he.trans (by change 1/2* A.S.scale r ≤_; linarith only [h₁]))⟩
omit hG
lemma flyP (d:ℕ): (∀ m,0 < Bandage.fly A d m)∧ PolyB (S) (fun m=>(Bandage.fly A d m)⁻¹):=by
   refine ⟨fun i=> inv_pos.mpr (pow_pos (zero_lt_one.trans (A.fits.delayed i)) _),?_⟩; simp_rw [Bandage.fly,fog,inv_inv]; apply PolyB.pow; exact (PolyB.const A.S A.clock.bar).add ((PolyB.const ..).mul (PolyB.stretch A.S))
-- transfer polynomial prices to chosen.Scale proof.Weight generalized
include h hG
lemma waveLet (a:ℕ→ℝ)(he:PolyB A.S a):PolyB A.S (fun i=>a (Tabs.chosen A 1 h i)):=by
    let t:=κ; have hh(i:ℕ):i≤t i:= (Tabs.opened ..).1; have ht:Tendsto t atTop atTop:=tendsto_atTop_mono hh tendsto_id
    obtain ⟨v,hv,hV⟩:= he; refine ⟨v*2,mul_pos hv two_pos,?_⟩; filter_upwards [ht.eventually hV,scaleLoan hG A h] with i hi hx; apply hi.trans; apply Real.exp_monotone; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hx.1 hv.le
omit h A
variable (F:Family G)(B:Stock.Tabs F.path.levels)
include B
local notation "𝕊"=> F.path.levels
local notation "H0"=> F.path
local notation "λ'"=> Stock.Tabs.chosen F.path.levels 1 B
lemma peony (d:ℕ)(x:F.label d) : ∃ b:ℝ, 4≤b ∧∀ᶠ j in atTop,∀ k≥j, b*F.S.scale j ≤ F.S.scale k → let m:= Stock.Tabs.chosen F.path.levels 1 B j; m≤ k ∧ ∃ w:ℝ, 0<w ∧ w*‖alto F.path m d‖*(4*(1+(F.path.levels.params k).columns)/Bid.gainChart F.path k m) ≤ Bandage.fly F.path.levels d m/2 ∧ stockK F k d x*(stakes F j m/w) ≤ expS F.S (-1/16) k := by
    let t:= λ'; let Q:=𝕊; let f(m):= Bandage.fly Q d m; let v k:= (F.path.levels.params k).columns; let z:=(F.labels.level d).coeffSize x; have hh:0≤ z:= WilsonStartup.Mark.coeff_nn x; let g(i):= (f i/2)⁻¹* ‖alto F.path i d‖ * Real.exp ((1/8)*F.S.scale i)
    have ha:= flyP Q d; have hG1(i):0 < ‖alto F.path i d‖:= by rw [alto_norm]; exact inv_pos.mpr (pow_pos (F.S.a_pos _) _)
    have hB:PolyB Q.S (fun j=> g (t j)* stakes F j (t j)):=by
       refine PolyB.mul (waveLet hG Q B g ?_) ?_
       · have hx : PolyB Q.S (fun i=>‖alto F.path i d‖):= by simp_rw [alto_norm,←inv_pow]; exact (PolyB.inverse Q.S).pow d
         unfold g; simp_rw [div_eq_mul_inv,mul_inv_rev,inv_inv]; exact (((PolyB.const (Q.S) _).mul ha.2).mul hx).mul (PolyB.fromNote (Note.bell_exp (F.S) (1/8)))
       apply ((PolyB.fromNote (Note.bell_exp (F.S) 1)).mul (PolyB.const _ (Real.exp 5))).mono
       filter_upwards [scaleLoan hG Q B] with i hi; change ‖stakes F i (t i)‖ ≤ ‖_*_‖; unfold stakes; rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_add]; exact (mul_le_mul_of_nonneg_right (Real.exp_monotone ((show _ ≤ _ from hi.2).trans (one_mul (Q.S.scale i)).symm.le)) (Real.exp_pos _).le).trans (le_abs_self _)
    obtain ⟨b,hb,hF⟩:=hB
    obtain ⟨N,hN⟩:= eventually_atTop.mp (oneStep Q (1/32) (8*z) (by norm_num)); let C:=max 4 (b*32); have hc : 4≤C:=le_max_left ..
    refine ⟨C,hc,?_⟩; filter_upwards [eventually_ge_atTop N,hF,(F.S.divergent.eventually_gt_atTop 0),scaleLoan hG Q B] with i hi hh' he ht k hk hx; let m:= t i; let u:= f m/2
    have hℓ : m ≤ k:= (bob F.S).le_iff_le.mp (ht.1.trans ((mul_le_mul_of_nonneg_right (le_trans (by norm_num : (2:ℝ)≤4) hc) he.le).trans hx))
    let H:= ‖alto F.path m d‖*(4*(1+v k)/Bid.gainChart F.path k m); let w:= u/H; have hp:0<H:=by unfold H; have he:1 ≤ v k:= (Q.params k).columns_ge; have ht :0<v k:=zero_lt_one.trans_le he; exact mul_pos (hG1 m) (div_pos (by positivity) (Real.exp_pos _))
    have hv : w*H=u:= div_mul_cancel₀ _ hp.ne'
    let V(j):= F.S.scale j; let p:=Real.exp (Work.D01.columnLogs F.path.levels k)*(1+v k)*(8*z)
    have hP: p ≤ expS (F.S) (1/32) k:= hN k (hi.trans hk)
    let l:=g m*stakes F i m; have hl : 0 ≤ l:=mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (half_pos (ha.1 m)).le) (norm_nonneg _)) (Real.exp_pos _).le) (Real.exp_pos _).le
    refine ⟨hℓ,w,div_pos (half_pos (ha.1 m)) hp,?_,?_⟩
    · rw [mul_assoc]; exact hv.le
    have hGx:p * l * Real.exp (-(1/8)*V k) ≤ expS F.S (-1/16) k:=by
       have hz:l ≤ expS F.S b i:= (le_abs_self _).trans hh'
       apply (mul_le_mul_of_nonneg_right (mul_le_mul hP hz hl (Real.exp_pos _).le) (Real.exp_pos _).le).trans; unfold expS; rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; have hu:b*32 ≤ C:= le_max_right ..; unfold V; linarith only [hx,mul_le_mul_of_nonneg_right hu he.le]
    refine (le_of_eq (show stockK F k d x * (stakes F i m / w) = p*l*Real.exp (-(1/8)*V k) from ?_)).trans hGx
    unfold w H p l g f u v stockK z V Bid.gainChart; rw [mul_sub,Real.exp_sub]; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; rw [neg_mul,Real.exp_neg]; ring
end YM.UVExtension.Tide
