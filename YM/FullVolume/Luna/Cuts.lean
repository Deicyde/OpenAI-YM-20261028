import YM.FullVolume.Glitz.Beryl
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Next.Foundations Jams YM.Source Labels
section partition
variable (k:ℕ){q v:ℝ}
structure Tableau (q:ℝ)(k:ℕ) where
  wide : 1≤q
  p: Fin (k+1)→ sun
  unique: Injective p
  u: Fin (k+1)→ℝ
  hp i: 0≤ u i
  use: ∀ w:Rung,∀ η,Stripe w q η→∀ i,|mix w (gloss k p i)| ≤ η*u i
namespace Tableau
lemma access (h:1≤q): Nonempty (Tableau q k):=by obtain ⟨u,hu,H⟩:= toys k (sampleP k) q h; exact ⟨⟨h, _, samples_in k,u,hu,H⟩⟩
variable {k} (T:Tableau q k)
def cuts (w:Rung):=crate k T.p w
def price := ∑ i, T.u i
abbrev liftT (v:ℝ):= (1+T.price) * (q/v)^(k+1)
variable (h:q≤v){w:Rung}{η:ℝ} (hs:Stripe w q η)
lemma sane : 0≤T.price:=sum_nonneg fun i _=> T.hp i
include T
lemma splitK {E:Type*}[AddCommGroup E][Module ℝ E](w:Rung)(f:sun→E): mix w f=mix (T.cuts w) f +mix (w-T.cuts w) f:=by simp_rw [←combo_eq,map_sub]; abel
lemma lapse (hr:q ≤ v){w:Rung}{η:ℝ}(hs:Stripe w q η):Stripe (w-T.cuts w) v (η*T.liftT v):=by
  obtain ⟨hv,p,he,u,hu,hh⟩:= T; have hq:=zero_lt_one.trans_le hv; have hp':=hq.trans_le hr; let y:= q/v; have hy:0≤y:=div_nonneg hq.le hp'.le; have h0 : 0 ≤ ∑ i,u i:= sum_nonneg fun i _=>hu i
  let d w:=crate k p w; have hU:= stripe_pos hs
  have hz : Stripe (w-d w) v (η*(1+∑ i,u i)*y^(k+1)):=by
    intro j; let f(x:ℝ):=(x/v)^j; let g(x:ℝ):=(x/q)^j; rw [← mix_id]; by_cases h':j≤k; · rw [plays_exact k p he w v j h',norm_zero]; positivity
    let h₁(x:sun):=g x; have hx:mix (w-d w) (fun x:sun=>(x.val/v)^j)= y^j*mix (w-d w) h₁:=by
      unfold mix; rw [mul_sum]; apply sum_congr rfl; intro i hi
      have h': (i.val/v)^j=y^j*h₁ i:=by unfold h₁ g; rw [←mul_pow]; congr 1; unfold y; field_simp
      change _* (_/v)^j=_*(_*_); rw [h']; ring
    rw [hx,norm_mul,Real.norm_of_nonneg (pow_nonneg hy j), mul_comm (y^j), ← combo_eq,map_sub,combo_eq,combo_eq]; refine mul_le_mul ?_ (pow_le_pow_of_le_one hy ((div_le_one hp').2 hr) (by omega)) (pow_nonneg hy j) (by positivity)
    apply (norm_sub_le ..).trans; refine (add_le_add (show ‖mix w h₁‖≤η from hs j) ?_).trans_eq (show η+η*∑ i,u i=η*(1+∑ i,u i) from (by ring))
    rw [show d w=crate k p w from rfl,incomes,mul_sum]; apply (norm_sum_le ..).trans; refine sum_le_sum fun i _=>?_
    rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (show ‖h₁ (p i)‖≤1 from by unfold h₁ g; rw [Real.norm_eq_abs,abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ratio_le hv (p i).property) )).trans (hh _ _ hs i)
  change Stripe _ v (η*((1+∑ i,u i)*y^(k+1))); rw [← mul_assoc]; exact hz
end Tableau
end partition
end YM.PhysicalNext.Repeat.Luna
