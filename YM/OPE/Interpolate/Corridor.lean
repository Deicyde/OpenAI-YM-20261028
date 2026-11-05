import YM.OPE.Interpolate.Leap
/-!
# High-order derivative bootstrap

Grading is crucial: an extra degree can lose one *finer-grid* power, so even
the first derivative comparison doesn't improve the formal power. But we can
start back from *high enough grade* where independently the cruder value
bounds are stronger than wanted. Works with arbitrary exterior widths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set MeasureTheory Lattice RG Metric
open scoped Topology BigOperators Classical ContDiff
variable {I L : Type}[Fintype I][DecidableEq I]{φ:Filter L}[φ.NeBot]{T:L→ℝ}{x y z:L→I→ E4}{S:Schedule}{r:L→ℕ}{a b c d:ℝ}
variable {G:Gauge}{R:Register G}{A:Table R}
variable (hT:Tendsto T φ atTop)(hs:Height S φ T r b)

section
variable (h:L→ (I → R.Token)→(I→ E4)→ℂ)
variable (P:DiffPlan A)

structure Corridor (φ:Filter L)(T:L→ℝ)(a:ℝ)(x:L→ I→E4): Prop where
    managed : Kept φ T a x
    room : extentWithin φ T x a

lemma Corridor.bump (hT:Tendsto T φ atTop)(hp:Corridor φ T a x)(he:RateLE φ T (fun i=>y i - x i) (-b))(hy:a<b) : Corridor φ T a y := ⟨hp.managed.bump hT he hy, hp.room.bump hT he (neg_le_neg hy.le)⟩

variable (hx:a<b) 
    (rough:∀ p:I→R.Token,∀ x:L→I→ E4, Corridor φ T a x → RateLE φ T (fun i=> h i p (x i)) (a*sigma p+c))
    (grid:∀ p:I→R.Token, ∀ g:L→ I→ Cover, (∀ i, Screen (S.gridPoint (r i) ∘ g i))→ Corridor φ T a (fun i=> S.gridPoint (r i) ∘ g i)→ RateLE φ T (fun i=> h i p (S.gridPoint (r i) ∘ g i)) (b*sigma p+d))
    (history:∀ p:I→R.Token,∀ y:L→I→ E4,Corridor φ T a y→ ∀ᶠ i in φ, DifferentiableAt ℝ (h i p) (y i) ∧ ∀ j c,fderiv ℝ (h i p) (y i) (kindle j c)= h i (touched p j c P) (y i))
include hT hs hx rough grid history
lemma interpolated (p:I→R.Token)(hc: Corridor φ T a x) : RateLE φ T (fun i=> h i p (x i)) (b*sigma p+d):=by
    obtain ⟨n,hn⟩ := eventually_atTop.mp ((tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hx)).eventually_ge_atTop (c-d));
    suffices hu:∀ k,∀ f:I→ R.Token,∀ x:L→I→ E4, Corridor φ T a x→ n ≤ sigma f+k → RateLE φ T (fun i=> h i f (x i)) (b*sigma f+d) by exact hu n p x hc (by omega)
    intro k; induction k with
    | zero=>
       intro f x hp he; apply (rough f x hp).mono; linarith only [(show c-d≤(b-a)*sigma f from hn (sigma f) he)]
    | succ k ih=>
       intro f x hp he
       obtain ⟨W,hW,hV⟩:= cloud_jump (x:=x) S hT hs
       let y i:= S.gridPoint (r i) ∘ W i; have hv:= grid f W hW (hp.bump hT hV hx); let R':ℝ:=b*(sigma f+1:ℝ)+d; have hK : RateLE φ T (fun i=>h i f (y i)-h i f (x i)) (R'-b):=by
          refine leap_cost hT hV (b:=R') ?_; intro z hz;
          have hl: Corridor φ T a z := hp.bump hT (hV.transfer (Eventually.of_forall fun i=> by exact (show ‖z i-x i‖ ≤‖ y i-x i‖ from by rw [← dist_eq_norm]; exact hz i))) hx
          have hG:=history f z hl; refine ⟨hG.mono (fun _ hi=> hi.1),?_⟩; apply rateOperator hT; intro j q; let p:= touched f j q P; have hk: sigma p=sigma f+1:= bumped ..; have ht := ih p z hl (by omega); apply (ht.mono (show _ ≤ R' from (by rw [hk]; unfold R'; push_cast; rfl))).congr; exact hG.mono (fun i hi=>(hi.2 ..).symm)
       apply (hv.sub (hK.mono (show R'-b ≤ b*(sigma f:ℝ)+d by unfold R'; linarith)) hT).congr; exact Eventually.of_forall fun i=> sub_sub_self _ _
end
end YM.OPE
