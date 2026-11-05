import YM.UVExtension.Flake.Twist
import YM.UVExtension.Crown.Sides
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- any constant transfer factor=2. Can change.
set_option quotPrecheck false
local notation "r!"=> UVExtension.Spire.spatial
local notation "Z'"=> spreadK.span
local notation "T!"=> spreadK.call
noncomputable def fringe:= Camp.rad/32
lemma fringe_pos : 0 < fringe:=by norm_num [fringe,Camp.rad,Oriel.rim]
structure Speed (M:ℝ)(z:ℂ): Prop where
   positive:0≤ M
   slab : |z.re| +3*fringe < UVExtension.Spire.spatial
   earns : |z.im|≤ fringe
   turns : 4*(|z.im|/fringe)*M≤ Real.log 2
variable {G:Gauge}{E:Type}[NormedAddCommGroup E][NormedSpace ℂ E] {a M b:ℝ}{z:ℂ}(h: Speed M z)
include h
lemma trusts (hb:0≤b)(f:ℂ→ E)(hf:Bumps spreadK.span f)(hp:∀ i,‖f (spreadK.call i)‖≤ b)(hz:∀ z∈spreadK.span,‖f z‖≤b*Real.exp M): ‖f z‖≤ 2*b:=by
   have hh:DifferentiableOn ℂ f (ball 0 r!):= hf _ id Metric.isOpen_ball (Set.mapsTo_id (spreadK.span)) differentiableOn_id
   refine (Sides.peak f hb h.positive (by norm_num [Spire.spatial, Camp.rad,Oriel.rim] : (0:ℝ) < UVExtension.Spire.spatial) hh hz (fun v he=> hp (⟨v,he⟩:Shade)) z fringe_pos h.slab h.earns).trans ?_
   have ht:=Real.exp_monotone h.turns; rw [Real.exp_log (by norm_num)] at ht; exact (mul_le_mul_of_nonneg_left ht hb).trans_eq (mul_comm ..)
lemma costly (hb:0≤b)(c:ℝ)(hr:0≤c)(f:ℂ→ E)(hf:Bumps Z' f)(hp:∀ i,c*‖f (T! i)‖≤ b)(hz:∀ z∈Z',c*‖f z‖≤b*Real.exp M): c*‖f z‖≤2*b:=by
    let F z:=(c:ℂ) • f z; have hh z:‖F z‖= c*‖f z‖:= (norm_smul ..).trans (congr_arg (·*_) (show ‖(c:ℂ)‖=c from (Complex.norm_real c).trans (Real.norm_of_nonneg hr))); exact (hh z|>.symm).trans_le (trusts h hb F (fun _ _ w h g=> (hf _ _ w h g).const_smul _) (fun i=>(hh _).trans_le (hp i)) (fun z h=> (hh _).trans_le (hz z h)))
variable {d:ℕ}(F:Frame G d)
lemma bucks (hb:0≤b)(c:ℝ)(hr:0≤c)(f:ℂ→ F.Coeff)(hf:Bumps Z' f)(hp:∀ i,c*F.coeffSize (f (T! i))≤ b)(hz:∀ z∈Z',c*F.coeffSize (f z)≤b*Real.exp M): c*F.coeffSize (f z)≤2*b:=by
    have hv:∀ i:F.Index,∃ w:ℂ, ‖w‖≤1 ∧ w*f z i=↑(‖f z i‖):=by
        intro i; let t:= f z i; by_cases ht:t=0; exact ⟨0,by simp,by rw [show f z i=0 from ht]; simp⟩
        refine ⟨(↑‖t‖:ℂ) * t⁻¹,?_ ,by change _*t=_; rw [mul_assoc,inv_mul_cancel₀ ht,mul_one]⟩; rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_inv_cancel₀ (norm_ne_zero_iff.mpr ht)];
    choose w hw using hv
    let g(a:ℂ):= ∑ i,w i*f a i; have hg:Bumps Z' g:= bend_finset _ _ fun i _ U p hs hV ht=> (fun x hx => DifferentiableWithinAt.const_mul (differentiableWithinAt_pi.mp (hf U p hs hV ht x hx) i) _)
    have he(a):‖g a‖≤F.coeffSize (f a):=(norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> (norm_mul ..).trans_le (mul_le_of_le_one_left (norm_nonneg _) (hw i|>.1))))
    have ht(a): c*‖g a‖≤ c*F.coeffSize (f a):=mul_le_mul_of_nonneg_left (he _) hr
    have hA : g z=↑(F.coeffSize (f z)):=by unfold g Frame.coeffSize; rw [Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _=> (hw i).2
    have h:= costly h hb c hr g hg (fun i=> (ht ..).trans (hp i)) (fun z hz'=>(ht _).trans (hz z hz')); rwa [hA,Complex.norm_real,Real.norm_of_nonneg (Work.G08.size_nonneg ..)] at h
end YM.UVExtension.Cloud
