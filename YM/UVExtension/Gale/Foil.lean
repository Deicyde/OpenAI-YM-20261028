import YM.UVExtension.Cloud.Desks
import YM.Extra.ITERATION_NO_LOSS.Scales
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Real Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
noncomputable def shill (x:ℝ):= (x^ (1/100:ℝ))
noncomputable def convoy (x:ℝ):= exp (- (1/2:ℝ)*shill x)
private lemma slides (c:ℝ): Tendsto (fun x:ℝ=> x^c*convoy x) atTop (𝓝 0):=by
    have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c/(1/100:ℝ)) (1/2) (by norm_num)).comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100))
    refine H.congr' ((eventually_gt_atTop 0).mono (fun x hx=> ?_)); change ((x^(1/100:ℝ))^(c/(1/100:ℝ)))*_=_; rw [← Real.rpow_mul (by positivity : 0≤x), show (1/100:ℝ)*(c/(1/100:ℝ))=c by ring]; rfl
noncomputable def stroke (x:ℝ):= (Blush.glyph x)⁻¹* convoy x
private lemma margins : ∀ᶠ x:ℝ in atTop, 0≤ stroke x∧ stroke x ≤ 1:=by
    have h := Vac.Numbers.cost ((1:ℝ)/5) _ (by norm_num : 0<(1/100:ℝ))
    filter_upwards [h] with x hx
    unfold stroke; refine ⟨mul_nonneg (inv_pos.mpr (Blush.glyphpos _)).le (Real.exp_pos _).le,?_⟩
    rw [inv_mul_le_iff₀ (Blush.glyphpos _),mul_one]; unfold Blush.glyph convoy; rw [Real.sqrt_eq_rpow,←Real.exp_mul]; refine exp_monotone ?_; unfold shill; change -(1/2:ℝ) * x^(1/100:ℝ) ≤ - (Vac.Numbers.P x^((1:ℝ)/5))*(1/2); linarith only [hx]
-- log exp sign.No positivity quirks
lemma plato (i:ℝ) : Tendsto (fun x:ℝ=> x^i*(Blush.glyph x)⁻¹/exp (shill x)) atTop (𝓝 0):= by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (slides i) ?_ ?_ -- g arg check
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; have h:= Blush.glyphpos x; positivity
    filter_upwards [margins,eventually_gt_atTop (0:ℝ)] with x ⟨hp,hx⟩ he
    rw [div_eq_mul_inv]; let t:=shill x; rw [show (exp t)⁻¹= convoy x*convoy x from ?_]
    · calc
        _= (x^i* convoy x)*stroke x:=by unfold stroke; ring
        _≤ _:=(mul_le_of_le_one_right (show 0≤ x^i*convoy x from mul_nonneg (Real.rpow_nonneg he.le _) (Real.exp_pos _).le) hx)
    rw [←exp_neg,convoy,←exp_add]; apply congr_arg; unfold t; ring
private lemma swapS(f:ℝ→ℝ): (fun x:ℝ=> f x / exp (shill x)) = fun x=> f x*convoy x*convoy x:= by
    funext x; rw [div_eq_mul_inv, mul_assoc,← Real.exp_neg,convoy,← Real.exp_add]; congr 2; ring
lemma calling (t p q h r:ℝ) : Tendsto (fun x:ℝ=> reflux (x+p) h t (Blush.glyph x) r q / exp (shill x)) atTop (𝓝 0):= by -- max exactly. scale all.
    let y(x:ℝ):= r*(4*(x+p));let P(x:ℝ):=4*t*y x; let e(x:ℝ):= exp (shill x); let b:ℝ:=r*(48*h)
    have hc:Tendsto (fun x:ℝ=> convoy x) atTop (𝓝 0):=by simpa using slides 0
    have hs:Tendsto (fun x:ℝ=> x*convoy x) atTop (𝓝 0):=by simpa using slides 1
    have hy:Tendsto (fun x:ℝ=> y x/e x) atTop (𝓝 0):=by
       change Tendsto _ _ _; unfold e; rw [swapS]; unfold y; simp_rw [mul_assoc, add_mul]
       simpa only [Function.comp_def,mul_assoc,mul_zero,zero_add] using ((((hs.mul hc).add ((hc.mul hc).const_mul p)).const_mul 4).const_mul r) -- associativity
    let f(x:ℝ):= (Blush.glyph x)⁻¹/e x; have hF:Tendsto f atTop (𝓝 0):=by simpa using! plato 0
    have hg:Tendsto (fun x:ℝ=> x*f x) atTop (𝓝 0):=by simpa only [Real.rpow_one,mul_div_assoc,f,e] using! plato 1
    let A x:=2*q*(y x/e x); let B x:= 2*1*(4*t)*(y x/e x); let C x:= 2*(b*f x + 4*t*(r*(4*(x*f x+p*f x))))
    have he:(fun x=> reflux (x+p) h t (Blush.glyph x) r q /exp (shill x))= fun x=>max (A x) (max (B x) (C x)):=by
       funext x; unfold A B C reflux f b y e; dsimp only; rw [←max_div_div_right (Real.exp_pos (shill x)).le,←max_div_div_right (Real.exp_pos (shill x)).le]; congr 1 ; · ring
       congr 1 <;> ring
    rw [he]; let W:= ((hF.const_mul b).add ((( (hg.add (hF.const_mul p)).const_mul 4).const_mul r).const_mul (4*t))).const_mul 2
    simpa only [mul_zero,add_zero,max_self] using ((hy.const_mul (2*q)).max ((hy.const_mul (2*1*(4*t))).max W))
end YM.UVExtension.Cloud
