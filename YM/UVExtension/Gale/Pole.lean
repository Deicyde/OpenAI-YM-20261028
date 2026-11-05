import YM.UVExtension.Gale.Stacks
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{s:Levels G}{n N r k:ℕ}
variable (L:∀ i:ℕ,ℂ→ Lacing.Banner s F A n i)
local notation "O'"=> s.clock
local notation "D"=> F.Coeff
local notation "H"=> Lacing.Card s F A n
local notation "X₀"=> s.params
local notation "l'"=> s.S.block
local notation "κ"=> s.clock.forcedAllowance
local notation "S"=> s.S
local notation "g₀"=> fun i=> Lacing.glaring s i n
variable (i N:ℕ)
variable (U:ℂ→ Card s F A n N)
local notation "Ψ"=> fire L N U
variable (v c q w:ℕ→ℝ)(ρ:ℕ→ℝ)
-- inverse columns.A canon.B.Anal weights expansion.Back.U axis not ψ.
noncomputable def deckS (i j:ℕ)(h:i≤j)(z:ℂ)(k:F.Index):= let x:=shuttle L N U j z k i h; tether L N U i j h z x.2
-- full canonical lens expansion; estimates.Poly s_j. Shape test.Any d.
noncomputable def wind (i j:ℕ)(h:i≤j)(z:ℂ): F.Coeff→L[ℂ] F.Coeff := ({toFun:=fun y:F.Coeff=>∑ k,y k • deckS L N U i j h z k,map_add':=fun x y=>by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib],map_smul':=fun x y=>by simp only [Pi.smul_apply,smul_smul,Finset.smul_sum]; rfl}: F.Coeff→ₗ[ℂ] F.Coeff).toContinuousLinearMap
noncomputable def viss (i:ℕ)(h:r≤ i)(z:ℂ)(x:F.Coeff) : F.Coeff := (steers (wind L N U r i h z)).symm (tether L N U r i h z x)
variable {L N U v c q w}{a:ℝ}(R:Rotor s F A n N r a L v c q w)(P:Booked L N U v c q w R)
local notation "Z"=>ball (0:ℂ) a
variable {z:ℂ}(hz:z∈Metric.ball 0 a)
include P hz
lemma landing (k:ℕ)(h:r ≤ k)(hi:k≤ N)(x:F.Coeff): F.coeffSize x≤ 2*F.coeffSize (wind L N U r k h z x):=by
   let f i:= deckS L N U r k h z i; let y:= wind L N U r k h z x
   have he:y-x=∑ i,x i • (f i-Size.axis F i):=by simp_rw [smul_sub, Finset.sum_sub_distrib, Size.sum_axes];rfl
   have ht: F.coeffSize (y-x)≤F.coeffSize x * (1/4):=by
      rw [he]; apply (Size.finite ..).trans; unfold Frame.coeffSize; rw [Finset.sum_mul]; refine Finset.sum_le_sum (fun i _=>?_); change F.coeffSize _ ≤ _; rw [Size.smul]; exact mul_le_mul_of_nonneg_left (bill R P hz i h hi) (norm_nonneg _)
   have hx:F.coeffSize (x-y)=F.coeffSize (y-x):=by unfold Frame.coeffSize; apply Finset.sum_congr rfl; intro i hi; exact norm_sub_rev ..
   have hw:= size_triangle F x y; rw [hx] at hw; change _ ≤ 2*F.coeffSize y; linarith only [hw,ht,size_nonneg F y]
lemma few (k:ℕ)(h:r≤ k)(hi:k≤N): Bijective (wind L N U r k h z):= by
   let F':= (wind L N U r k h z).toLinearMap
   have hv: Injective F':= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun x hx=> size_separates _ x ( (landing R P hz k h hi x).trans (by rw [show _= (0:F.Coeff) from (show wind L N U r k h z x= _ from hx)]; simp [Frame.coeffSize]))))
   exact ⟨hv,LinearMap.injective_iff_surjective.mp hv⟩
lemma wagon (k:ℕ)(h:r ≤ k)(hi:k ≤ N)(x:F.Coeff): let V:= viss L N U k h z x;
    x = ∑ i:F.Index,V i • (shuttle L N U k z i r h).2 ∧ F.coeffSize V ≤ 2*F.coeffSize (tether L N U r k h z x):=by -- sum outputs at r.Cast.Ack.
   intro V; let T:= tether L N U r k h z; have he:wind L N U r k h z V=T x:=by rw [←steers_eq (wind L N U r k h z) (few R P hz k h hi)]; exact (steers _).apply_symm_apply _ -- V= inv cov.OK.
   refine ⟨T.injective ?_,(landing R P hz k h hi V).trans_eq (congr_arg (fun x=>2*F.coeffSize x) he)⟩; rw [map_sum]; simp_rw [map_smul]; exact he.symm

omit hz
lemma puts (k:ℕ)(h:r≤ k)(hi:k≤N)(x:F.Coeff): DifferentiableOn ℂ (fun z=> viss L N U k h z x) Z:=by
    let g(z:ℂ):=wind L N U r k h z
    have hx i:DifferentiableOn ℂ (fun z=>deckS L N U r k h z i) Z:= helix R P k h hi _ ((pumps R P k r h le_rfl hi i).snd)
    have h': DifferentiableOn ℂ g Z:= by
       apply curtains; intro x; change DifferentiableOn ℂ (fun z=>∑ i,x i • deckS L N U r k h z i) Z; exact DifferentiableOn.fun_sum (fun i _=> (hx i).const_smul (x i))
    exact keel g Metric.isOpen_ball h' (fun z hz=> few R P hz k h hi) (fun z=> tether L N U r k h z x) (helix R P k h hi _ (differentiableOn_const _))
omit P
lemma cheap (s:Levels G) (i:ℕ): (s.params (i+1)).columns ≤ (s.S.block i).val:=by
   let v:= (s.params (i+1)); let x:ℝ:=1+v.paths+v.width⁻¹+v.columns+v.clip.relaxation+v.supportExponent; let L:ℝ:= (s.S.block i).val
   have hy:x≥ v.columns:= by
      have hc:v.clip.relaxation≥0:=v.clip.radius_pos.le
      unfold x; linarith [v.paths_pos,inv_pos.mpr v.width_pos,v.price_pos]
   have h_L : (3:ℝ) ≤ ((s.S.block i).val:ℝ):=by exact_mod_cast s.S.block_large i
   have h:L > 1:= by unfold L; linarith
   have hp: Real.log x / Real.log L≤1:=by
       apply (s.fits.logCost i).trans; exact inv_le_one_of_one_le₀ (one_le_pow₀ (Nat.one_le_cast.mpr (by have hp:= s.clock.adm (i+1); omega)))
   have hz:1 ≤ v.columns:= v.columns_ge; exact hy.trans ((Real.log_le_log_iff (by linarith only [hz,hy]) (by linarith only [h])).1 ((div_le_one (Real.log_pos h)).1 hp))
include hz P
lemma water (i:ℕ)(h0:r≤ i)(hi:i≤ N)(hp:∀ i,r≤ i→ 2*q i≤ (s.params (i+1)).columns)(x:F.Coeff): F.coeffSize (tether L N U r i h0 z x) ≤ (((S).a i)⁻¹ * (F.coeffSize x)):=by
    induction h0 with
    | refl=> rw [flipI]; refine le_mul_of_one_le_left (size_nonneg F _) ?_; exact (one_le_inv₀ (S|>.a_pos r)).2 ((S|>.strictAnti.antitone (Nat.zero_le r)).trans (S|>.a_zero).le)
    | step h IH => rename_i j; rw [Gale.mirror _ _ _ _ _ h]; apply (funds U R P.dims P.hulls j h hi hz _).trans; rw [Schedule.a_step,inv_div,div_eq_mul_inv]; calc
        _ ≤ _:=mul_le_mul (le_trans (hp j h) (cheap s j)) (IH ((Nat.le_succ _).trans hi)) (size_nonneg ..) (Nat.cast_nonneg _)
        _ = _:= (mul_assoc ..).symm
end YM.UVExtension.Gale
