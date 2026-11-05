import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.MergeProof.Switch
import YM.Next.RANK.Alarm
import YM.Next.RANK.Mountain
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Reel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}{Q:Schedule}
structure Note (S:Schedule)(f:ℕ→ℝ)(c:ℝ):Prop where
   pos : ∀ i,0<f i
   pitch : Tendsto (fun i=> Real.log (f i)/S.scale i) atTop (𝓝 c)
namespace Note
variable (S:Schedule)
lemma note_a : Note S S.a (-1):= by
    refine ⟨S.a_pos,tendsto_const_nhds.congr' ((S.divergent.eventually_gt_atTop 0).mono fun i hi=> ?_)⟩
    dsimp only; rw [Stock.a_log S i,Real.log_exp,neg_div,div_self hi.ne']
lemma notes (c:ℝ)(hc:0<c): Note S (fun _=>c) 0:= ⟨fun _=>hc,tendsto_const_nhds.div_atTop S.divergent⟩
lemma bell_exp (c:ℝ): Note S (fun i=> Real.exp (c*S.scale i)) c:=by
   refine ⟨fun i=> Real.exp_pos _,tendsto_const_nhds.congr' ((S.divergent.eventually_gt_atTop 0).mono fun i hi=> ?_)⟩; dsimp only; rw [Real.log_exp,mul_div_cancel_right₀ _ hi.ne']
variable {S}{f g:ℕ→ℝ}{a b:ℝ} (h:Note S f a)(hh:Note S g b)
include h
lemma swapP (h':a=b):Note S f b:=h' ▸ h
lemma relay (j:ℕ→ℕ)(hj:Tendsto j atTop atTop)(hp:Tendsto (fun i=>S.scale (j i)/S.scale i) atTop (𝓝 b)):Note S (fun i=>f (j i)) (a*b):=by
   refine ⟨fun i=>h.pos _,((h.pitch.comp hj).mul hp).congr' ?_⟩; filter_upwards [(S.divergent.comp hj).eventually_gt_atTop 0] with i hi
   have hx:0<S.scale (j i):=hi; dsimp only [comp_apply]; field_simp
lemma scales (he : S.Gentle) : Note S (fun i=>f (i+1)) a:=by
   apply swapP (a:=a*1) _ (mul_one a); apply h.relay _ (tendsto_add_atTop_nat 1)
   refine ((tendsto_const_nhds (x:= (1:ℝ))).add he).congr' (?_) |> ((show (1:ℝ)+0=1 from add_zero _ ) ▸ ·)
   filter_upwards [S.divergent.eventually_gt_atTop 0] with i hi; rw [S.scale_succ,add_div,div_self hi.ne']
lemma mills (hh:Note S g b): Note S (fun i=>f i*g i) (a+b):=by
   refine ⟨fun i=> mul_pos (h.pos _) (hh.pos _),(h.pitch.add hh.pitch).congr' (Eventually.of_forall fun i=>?_)⟩; dsimp only; rw [Real.log_mul (h.pos _|>.ne') (hh.pos _|>.ne'),add_div]
lemma splits (hh:Note S g b): Note S (fun i=>f i/g i) (a-b):=by
   refine ⟨fun i=> div_pos (h.pos _) (hh.pos _),(h.pitch.sub hh.pitch).congr' (Eventually.of_forall fun i=>?_)⟩; dsimp only; rw [Real.log_div (h.pos _|>.ne') (hh.pos _|>.ne'),sub_div]
lemma powr (x:ℝ): Note S (fun i=>f i^x) (x*a):=by
   refine ⟨fun i=> Real.rpow_pos_of_pos (h.pos _) _,(h.pitch.const_mul x).congr' (Eventually.of_forall fun i=> ?_)⟩; dsimp only; rw [Real.log_rpow (h.pos _), mul_div_assoc]
lemma powerN (n:ℕ): Note S (fun i=>f i ^ n) (n*a):=by
   simpa only [Real.rpow_natCast] using h.powr (↑n)
lemma extra (hh: Note S g a): Note S (fun i=> f i+g i) a:=by
   let x i:= max (f i) (g i); have hx i:0<x i:= (h.pos i).trans_le (le_max_left ..)
   have hy : Note S x a :=by
       have he:a=max a a:= by simp
       refine ⟨hx,?_⟩; rw [he] -- maybe none
       refine (h.pitch.max hh.pitch).congr' ?_; filter_upwards [S.divergent.eventually_gt_atTop 0] with i hi
       by_cases hp:f i≤g i
       · rw [show x i=g i from max_eq_right hp,max_eq_right (div_le_div_of_nonneg_right (Real.log_le_log (h.pos _) hp) hi.le)]
       rw [show x i=f i from max_eq_left (not_le.mp hp).le, max_eq_left (div_le_div_of_nonneg_right (Real.log_le_log (hh.pos _) (not_le.mp hp).le) hi.le)]
   have hP: Note S (fun i=>2*x i) a:=by simpa only [zero_add] using! ((notes S 2 two_pos).mills hy)
   refine ⟨fun i=> add_pos (h.pos i) (hh.pos i),tendsto_of_tendsto_of_tendsto_of_le_of_le' hy.pitch hP.pitch ?_ ?_⟩
   · filter_upwards [S.divergent.eventually_gt_atTop 0] with i hi; exact div_le_div_of_nonneg_right (Real.log_le_log (hx i) (max_le (le_add_of_nonneg_right (hh.pos i|>.le)) (le_add_of_nonneg_left (h.pos i|>.le)))) hi.le
   filter_upwards [S.divergent.eventually_gt_atTop 0] with i hi
   exact div_le_div_of_nonneg_right (Real.log_le_log (add_pos (h.pos i) (hh.pos i)) ((add_le_add (show f i≤x i from le_max_left ..) (show g i≤x i from le_max_right ..)).trans_eq (two_mul (x i)).symm)) hi.le
lemma outweigh (hy:Note S g b)(ha:a<b):∀ᶠ i in atTop,f i≤g i:=by
    filter_upwards [h.pitch.eventually (gt_mem_nhds (show a<(a+b)/2 by linarith)), hy.pitch.eventually (lt_mem_nhds (show (a+b)/2<b by linarith)), S.divergent.eventually_gt_atTop 0] with i hi hj hS
    exact (Real.log_le_log_iff (h.pos i) (hy.pos i)).mp ((div_le_div_iff_of_pos_right hS).mp (le_trans hi.le hj.le))
lemma thins (ha:a<0):Tendsto f atTop (𝓝 0):= by
   have hx:a/2<0:= by linarith
   let g i:= Real.exp (a/2*S.scale i); have hg:Tendsto g atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (by exact Tendsto.const_mul_atTop_of_neg hx S.divergent)
   exact squeeze_zero' (Eventually.of_forall fun i=> (h.pos i).le) (h.outweigh (bell_exp S _) (by linarith)) hg
end Note
end YM.MergeProof.Ribbons
