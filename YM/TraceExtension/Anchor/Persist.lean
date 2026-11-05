import YM.TraceExtension.Anchor.Fields

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Set Function Analysis Filter Asymptotics MeasureTheory Extraction Around Table Lattice Wilson RG Next.UVStress MergeProof
  MergeProof.Accent Source Bid Extra.Histories Push Cells
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{d : ℕ}
variable (H:C.Makes){b:Ultrafilter (ℕ×ℕ)}(hb:(b:Filter (ℕ×ℕ)) ≤ f.fuse)
local notation "F"=> C.labels.level d
local notation "α"=> C.path.levels
local notation "A!"=> C.S.a
variable {Z : ∀ k _N p : ℕ, Coefficient (C.labels.level d) (C.side k p)}
variable {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{Doors:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r Doors)
include H
private lemma down_cost {k N p:ℕ} (hm:C.ref d ≤ k)(hk:k≤N) (v:C.label d) :
    let T:= C.factory d N p
    (C.labels.level d).coeffSize v ≤ factor C.S d k*Real.exp (Work.D01.columnLogs C.path.levels k) *
      (C.labels.level d).coeffSize (T.entries k (T.terminal.symm v)).x :=by
   intro T; have he k : factor C.S d k=(A! k)⁻¹^d:=by
     rw [factor,mul_comm,Real.exp_nat_mul,Schedule.scale,Real.exp_log (inv_pos.mpr (C.S.a_pos k))]
   have hj i: 1≤factor C.S d i:= Real.one_le_exp (mul_nonneg (Shoot.scale_nn (α) _) (Nat.cast_nonneg _))
   induction k,hm using Nat.le_induction with
   | base=> rw [show (T.entries (C.ref d) (T.terminal.symm v)).x=v from C.normalized H hk v]; exact le_mul_of_one_le_left (Work.G08.size_nonneg F v) (one_le_mul_of_one_le_of_one_le (hj _) (Real.one_le_exp (Work.D01.columnLogs_nonneg ..)))
   | succ i hi IH=>
     apply (IH (by omega)).trans
     let c:=Real.exp (Work.D01.columnLogs (α) i); let t:= (C.path.levels.params (i+1)).columns; have ht:0<t:= zero_lt_one.trans_le (C.path.levels.params _).columns_ge
     let L:ℝ:= (C.S.block i).val; have hL: L≠0:=by unfold L; exact_mod_cast (C.S.block i).property.ne'
     have hh:=(H.calibrated d N p (by omega)).front i hi hk (T.terminal.symm v)
     refine le_trans (mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) ?_
     simp only [he,Work.D01.columnLogs_succ, Real.exp_add,C.S.a_step]
     rw [Real.exp_log (show 0<(C.path.levels.params (i+1)).columns from ht)]; dsimp only [T,Family.S]
     apply le_of_eq; field_simp; ring

variable {Q:ℕ→ℝ}
include hb
private lemma obtained (hN : Costs (b:=b) Z Q) {v:ℕ→ℕ×ℕ→C.label d} (hV:Captured (b:=b) Z Q v) :
     ∃ u:ℕ→C.label d, Calms C.S (d:ℝ) u ∧ ∀ᶠ k:ℕ in atTop, Tendsto (v k) (b:Filter _) (𝓝 (u k)):= by
    let f' k:= factor C.S d k * Real.exp (Work.D01.columnLogs (α) k) * (2*Q k)
    have he:Calms C.S d f':=by
       have h':Calms C.S 0 fun _=>(2:ℝ):=(show Calms C.S 0 fun _=>(2:ℝ) from fun p hp=> factor_const _ _ p hp)
       have hh:= ((factor_calms C.S (d:ℝ)).mul (curtain (α))).mul (h'.mul hN.calms); rw [add_zero,add_zero,add_zero] at hh; exact hh
    have hh:∀ᶠ k:ℕ in atTop,∃ x:C.label d, ‖x‖ ≤ f' k ∧ Tendsto (v k) (b:Filter _) (𝓝 x):=by
       filter_upwards [hN.pays,hV,eventually_ge_atTop (C.ref d)] with k hK hv ht
       have hB:∀ᶠ i : ℕ×ℕ in (b:Filter _),‖v k i‖ ≤ f' k:=by
          filter_upwards [hv,hK.2,(large_mesh f k).filter_mono hb] with i hi hs hh
          obtain ⟨N,p⟩:=i; obtain ⟨_,t,h,hU⟩:=hs
          let x:= Z k N p; let z:=v k (N,p); let X:=C.factory d N p; let u:=(X.entries k (X.terminal.symm z)).x
          apply (RelayDifference.norm_cost F z).trans ((down_cost H (p:=p) ht hh z).trans ?_)
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          change (F).coeffSize u≤ _; apply (Work.G08.size_triangle F u x.x).trans
          rw [Work.G08.size_sub_rev]; let c:=(α|>.params k).columns; change 32*(1+c)^2*(F).coeffSize (x.x-u) ≤ 2*(1+c)*Q k at hi; have hC:1 ≤ c:= (α|>.params k).columns_ge
          have hP : (F).coeffSize (x.x-u) ≤ Q k:= by apply le_of_mul_le_mul_left (a:=(2*(1+c))) _ (by linarith); apply (mul_le_mul_of_nonneg_right _ (Work.G08.size_nonneg ..)).trans hi; nlinarith only [hC]
          linarith only [hU,hP,rem_nonneg h]
       obtain ⟨D,hD,hS,x,hx⟩:= finite_extract _ _ hB; have hu:D=(b:Filter _) := Ultrafilter.unique b hD
       subst D; refine ⟨x,le_of_tendsto hx.norm hB,hx⟩
    let x k:= if h:∃ x:C.label d, ‖x‖ ≤ f' k∧ Tendsto (v k) (b:Filter _) (𝓝 x) then Classical.choose h else 0
    have hP:=hh.mono fun k e=> (show ‖x k‖≤ f' k ∧ Tendsto (v k) (b:Filter _) (𝓝 (x k)) from by unfold x; rw [dif_pos e];exact Classical.choose_spec e)
    refine ⟨x,he.smaller (isBigO_of_le _ (fun k=> ?_)),hP.mono fun _ i=>i.2⟩
    unfold x; split
    next h=> exact (Classical.choose_spec h).1.trans (Real.le_norm_self _)
    next=>rw [norm_zero]; exact norm_nonneg _

include hr
lemma marks (h:Cells.CellHyp C f)(HE:f.PointLimits C S)(HS:S.Hierarchy)(K:Stock.Tabs C.path.levels)
    (hN:Costs (b:=b) Z Q)(hp:Supported (b:=b) Z): ∃ v x, Calms C.S d x ∧
      (∀ᶠ k:ℕ in atTop,Tendsto (v k) (b:Filter (ℕ×ℕ)) (𝓝 (x k))) ∧ Captured (b:=b) Z Q v∧
        Book (b:Filter _) (hosted Z) (fun k=>S.project d (x k)) :=by
   obtain ⟨v,hV,hP⟩:= acquired H hb Z hr hN hp K
   obtain ⟨x,hX,hY⟩:= obtained H hb hN hV
   exact ⟨v,x,hX,hY,hV,from_center H h HE HS hb hY hP⟩
end YM.Trace.Pull
