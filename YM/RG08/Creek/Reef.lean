import YM.RG08.Creek.Bin
/-! # Estimates full unit centered tests (fixed Halo). Captured $exp$ continuity. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Analysis
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Summit Wings High Pill Taste Run PowerSeries Harvest MeasureTheory
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type}[Fintype I][DecidableEq I]{V:Type}[NormedAddCommGroup V]{G:Gauge}{X:Chain}{m N j i e E r D t k:ℕ}{R C w v A B:ℝ}{a b:I→ℕ}{p:List I}{ν:G.ColorIndex}{D':ChartRatio G}
section care
-- shape bounded exponential width $ω$. Explicit price through banner after profiles. Permitted halo K constants
abbrev cardsTell (P:Topaz I (Tale G))(C:Head I)(E:ℕ)(w:ℝ):Prop:= ∀ t,∀ i≤ E,∀ r, Quire.Lit (P t i r) w (C t)
lemma coer_lit {F:Layouts I G D R}(h:Sense a F){U:Head I}(hz:Fest w E 1 U F)(he:Crease U)(hv:0≤w)(hp:w≤1)(p:Places I)(hh:∀ i,size (p i) ≤ k)(φ:I→ Sight D R){Z:I→ℝ}(hr:∀ i,‖φ i‖≤ Z i)(hk:∀ i,vanes a i+E≤t): cardsTell (access φ (F p)) (fun V=>(∏ i∈V,Z i) * (Real.exp ((t*k:ℕ):ℝ)* U V)) E w := by
   intro T i hi r; have hx : 0≤ Z:= fun i=> (norm_nonneg _).trans (hr i); have hZ: 0 ≤ ∏ i∈T,Z i:=prod_nonneg fun i _=> hx i; have hU:= he.pos T
   by_cases hT:T=∅; · subst T; rw [access_nil φ (h.void _)]; exact Ink.raise (Ink.none _ _) (mul_nonneg hZ (mul_nonneg (Real.exp_pos _|>.le) hU))
   let r' := (h.style p T).cap
   have hq:Pail (p ((nonempty_iff_ne_empty.mpr hT).choose)) w (F p T i r) (U T):=by
      rw [← one_mul (U T)]; apply pail_of (hz i hi r T) hv p ⟨_,(nonempty_iff_ne_empty.mpr hT).choose_spec⟩
   by_cases ht:r≤t
   · exact Ink.raise ((roam_lit hq hv hp (hh _)).some (sampleK T φ) (fun i=>(Real.exp_pos _).le)) (mul_le_mul (spoke_mass T Z φ hx (fun i _=>hr i)) (mul_le_mul_of_nonneg_right (Real.exp_monotone (Nat.cast_le.mpr (Nat.mul_le_mul_right _ ht))) hU) (mul_nonneg (Real.exp_pos _|>.le) hU) hZ)
   rw [not_ne_iff.mp (mt ((h.stone p φ T).cap i r) (by have hv:=hk T; omega))]; exact Ink.raise (Ink.none _ _) (mul_nonneg hZ (mul_nonneg (Real.exp_pos _|>.le) hU))
-- hereditary majorant at fixed arity horizon. tag load in amplitude. empty unit
abbrev leafPress (r e:ℕ):= ((wheel r).card:ℝ)*((wheel e).card:ℝ)
lemma spool_lit (hw:0≤w){V W:Tale G}(hk:∀ i≤e,∀ j, Quire.Lit (V i j) w A)(ht:∀ i≤e,∀ j,Quire.Lit (W i j) w B) : Quire.Lit (gust V W e r) w (leafPress r e*(A*B)):=by
   unfold gust; rw [Finset.sum_apply]
   let x:=((wheel r).card:ℝ)*(A*B); have hp p (he:p∈wheel e): Quire.Lit (spoolB (V p.1) (W p.2) r) w x:=by
      have hv:=mem_antidiagonal.mp he; have hz i (he:i∈wheel r): Quire.Lit (grant r (braidV (V p.1 i.1) (W p.2 i.2))) w (A*B):= by rw [← mem_antidiagonal.mp he,grant_self]; exact gust_lit (hk _ (by omega) _) (ht _ (by omega) _) hw
      simpa only [x,spoolB,sum_const,nsmul_eq_mul] using Ink.additions hz (fun i=>(ling_pos _ _).le)
   apply Ink.raise (Ink.additions hp (show 0≤ling (r:=r) (α:=Loc G 1) w from fun i=>(ling_pos _ _).le)); unfold leafPress x; rw [sum_const,nsmul_eq_mul,mul_left_comm,← mul_assoc]
-- unit kernel. progress uses τ overhead from exponential output. Choose explicit positive fee depending X ($≥1)
abbrev sheetFee (t E:ℕ):=∑ r∈range (t+1),∑ i∈range (E+1),leafPress r i
lemma sheet_z (t E:ℕ):0≤ sheetFee t E:= sum_nonneg fun _ _=> sum_nonneg fun _ _=> mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
-- $$lifeMark(T)$$; P0=1. Rectangle D hull alignment.

def rope (E t:ℕ)(H:ℝ)(T:Finset I):ℝ:= if T=∅ then 1 else ‖(↑T.card:ℝ)⁻¹‖*∑ i: directVote T,sheetFee t E*(‖(↑i.val.1.card:ℝ)‖*H*rope E t H i.val.2)
termination_by T.card
decreasing_by
 all_goals exact shrank _ i.property
lemma rope_p (E t: ℕ)(C:ℝ)(hp:0≤C)(T:Finset I): 0≤rope E t C T:= by
   induction T using strongInductionOn with
   | _ T ih=>
     rw [rope]; split; exact zero_le_one
     exact mul_nonneg (norm_nonneg _) (sum_nonneg fun i _=> mul_nonneg (sheet_z ..) (mul_nonneg (mul_nonneg (norm_nonneg _) hp) (ih _ (part_lt i.property))))
lemma unit_p {G:Gauge}: Quire.Lit (spine_one (Loc G 1) i r) w 1:= by
    unfold spine_one; split; next he=>
      have hr : r=0 := by omega
      subst r
      unfold Quire.Lit Quire.Ink; simp only [ling, girth,Finset.univ_eq_empty, sum_empty, Nat.cast_zero,mul_zero, Real.exp_zero]; refine ⟨?_,(hasSum_fintype _).summable,?_⟩
      · intro i; positivity
      rw [tsum_fintype]; simp
    exact Ink.raise (Ink.none _ _) zero_le_one
lemma banner_lit {P:Wax.Head I}(hp:Crease P)(h:P ∅=1){V:Topaz I (Tale G)} (hk:∀ t,Stone (vanes a t) (V t))(he:cardsTell V (fun i=> C*P i) E w)(ht:∀ i,vanes a i+E≤t)(hW:0≤w)(hC:0≤C): cardsTell (Fabrics G V) (fun i=> rope E t C i * P i) E w:=by
    intro T
    induction T using strongInductionOn with
    | _ T ih =>
      intro i hi r; dsimp only; by_cases hT:T=∅; · subst T; unfold Fabrics; rw [banner_one,rope,if_pos rfl,h,mul_one]; exact unit_p
      by_cases hv:r≤t
      swap; · rw [not_ne_iff.mp (mt ((stone_p hk T).cap i r) (by have hp:=ht T; omega))]; exact Ink.raise (Ink.none _ _) (mul_nonneg (rope_p _ _ _ hC T) (hp.pos _)) -- syntax
      unfold Fabrics; rw [Wax.banner,if_neg hT,Pi.smul_apply,Pi.smul_apply, Finset.sum_apply,Finset.sum_apply]; rw [rope,if_neg hT,mul_assoc,Finset.sum_mul]
      refine Ink.scale (Ink.additions (fun j _=> ?_) (fun i=>(ling_pos _ _).le)) _
      let f:=rope E t C j.val.2; have hf:0≤ f:=rope_p _ _ _ hC _
      refine Ink.raise (spool_lit (A:= ‖(↑j.val.1.card:ℝ)‖*(C*P j.val.1)) hW (fun i' he' _=> Ink.scale (he _ i' (he'.trans hi) _) _) (fun i' ht r=>ih _ (part_lt j.property) i' (ht.trans hi) r)) ?_
      let a:= (↑j.val.1.card:ℝ)
      rw [show leafPress r i*(‖a‖*(C*P j.val.1)*(f*_))=leafPress r i*(‖a‖*C*f)*(P j.val.1*P j.val.2) by ring]
      have hx:leafPress r i ≤ sheetFee t E:= (single_le_sum (f:=leafPress r) (fun i _=>by unfold leafPress; positivity) (mem_range_succ_iff.mpr hi)).trans (single_le_sum (f:=fun r=>∑ i∈range (E+1),leafPress r i) (fun r _=>sum_nonneg fun i _=>mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mem_range_succ_iff.mpr hv))
      exact mul_le_mul (mul_le_mul_of_nonneg_right hx (by positivity)) (hp.rise _ _ (mem_filter.mp j.property).1) (mul_nonneg (hp.pos _) (hp.pos _)) (mul_nonneg (sheet_z ..) (by positivity))
end care
end YM.RG08.Creek
