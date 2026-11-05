import YM.Push.GRID_APPROXIMATION.Geometry
import YM.Push.PRICE_COMPILER.Post
import YM.TraceExtension.Quince.Nadir
import YM.TraceExtension.Zn.Have

/-!
 Numerical geometry at the actual clock. We will read the representations *within* the
 same history, comparing observations from measurement `j` and insertion stop `summit A j`.
 Maintain at least (log hatBeta)^48 log-scale separation; bounded by twice that eventually.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG RG.Supply Wilson Push.PriceCompiler Push.GridApprox Vac
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}(A:Levels G) (i j k:ℕ)
def Lyra (A:Levels G)(i:ℕ):= Real.log (A.clock.hatBeta i)
def Gate (x:ℝ):= (Real.log x)^48
def gap (j k:ℕ):= A.S.scale k-A.S.scale j
private lemma goal (j:ℕ): ∃ i:ℕ, j < i ∧ Gate (A.clock.hatBeta j) ≤ gap A j i:=by
   have hp:= (tendsto_atTop_add_const_right atTop (-A.S.scale j) A.S.divergent).eventually_ge_atTop (Gate (A.clock.hatBeta j)); exact ((eventually_gt_atTop j).and (hp.mono (fun i h=>by simpa only[gap,sub_eq_add_neg] using h))).exists
def summit (i:ℕ):= Nat.find (goal A i)
lemma stellar : i < summit A i:= (Nat.find_spec <| goal A i).1
lemma gstar : Gate (A.clock.hatBeta i) ≤ gap A i (summit A i):=(Nat.find_spec <| goal A i).2
lemma Sstar : Tendsto (summit A) atTop atTop:= tendsto_atTop_mono (fun i=> (stellar A i).le) tendsto_id

/-- One pre-L stem, several post-L costs. -/
def ctl (j:ℕ) := 1024*(j+10)
structure PostT (A:Levels G) : Prop where
    cropK (i:ℕ): ctl (A.clock.J (i+1)) ≤ (A.S.block i).val
    bloom (i:ℕ): ((A.S.block i).val:ℝ) ≤ Real.log (A.clock.hatBeta i)
    share (i:ℕ): (A.params i).columns ≤ Real.log (A.clock.hatBeta i)
    purse (i:ℕ): Vac.fiat G (A.params i) (A.clock.hatBeta i) ≤ Real.log (A.clock.hatBeta i)^2
    jig (i:ℕ): Real.log (A.clock.hatBeta i) * (A.params i).clip.linear ≥ 1

lemma staircase {X:Sheet G} {D:Rolls X} (H:ctl ≤ X.floorL){E:Protection D} (U:Delays E) : ∃ W:Delays E,DelayLe U W∧
    ∀ (Y:Delays E),DelayLe W Y→∀ (B:Bar Y)(I:Wait B)(A:Levels G), Paid I A→PostT A:=by
    let P (j i:ℕ)(x:ℝ):Prop:=let S:= X.profile i; let y:=Real.log x
        ((D.L j).val:ℝ) ≤ y ∧ S.columns ≤ y∧ Vac.fiat G S x ≤ y^2∧ 1≤ y*S.clip.linear
    have hp (j i:ℕ) : ∀ᶠ x:ℝ in atTop,P j i x:=by
        let S:= X.profile i; let a:ℝ:=2*Module.finrank ℝ G.Mat; let b:= Vac.fiat G S 1
        have hf(x:ℝ):Vac.fiat G S x= b+a*Real.log x:=by unfold a b Vac.fiat; rw [Real.log_one];ring
        have hx:=Real.tendsto_log_atTop; have he :0<S.clip.linear:= S.clip.tail_pos
        filter_upwards [hx.eventually_ge_atTop ((D.L j).val:ℝ), hx.eventually_ge_atTop S.columns,hx.eventually_ge_atTop b,hx.eventually_ge_atTop (a+1), (hx.atTop_mul_const he).eventually_ge_atTop 1] with x ht hu hv hk hl
        refine ⟨ht,hu,?_ ,hl⟩
        change Vac.fiat G S x ≤ _ ; rw[hf]
        have he:0 ≤ Real.log x:=le_trans (by unfold a;positivity) hk
        linarith only [mul_le_mul_of_nonneg_right hk he,hv]
    have hu(j:ℕ):∀ᶠ x:ℝ in atTop,∀ i,StepStages j i → P j i x:= eventually_transitions j atTop _ (fun i _=>hp _ _)
    obtain ⟨y,-,hy,ht⟩:= collect_upper U.betaEntry _ hu
    refine ⟨{U with betaEntry:=y},⟨hy,le_rfl,le_rfl,le_rfl⟩,fun W hw B I A h=>?_⟩
    have hf (i:ℕ) := ht (A.clock.J (i+1)) (A.clock.hatBeta i) ((hw.beta _).trans (h.pays i)) (A.clock.J i) (step_paid A i)
    exact ⟨fun i=> (Push.PriceCompiler.block_eq h i).symm ▸ ((H _).trans (D.large _).need),fun i=> (Push.PriceCompiler.block_eq h i).symm ▸ (hf i).1, fun i=>(params_eq h i).symm ▸ (hf i).2.1, fun i=>(params_eq h i).symm ▸ (hf i).2.2.1,fun i=>(params_eq h i).symm ▸ (hf i).2.2.2⟩

lemma point_room (h:PostT A)(i:ℕ) : Push.GridApprox.room A i (i+1) 8:=by
    unfold room tail; let j:= (A.clock.J (i+1)); let X:= (A.S.block i).val; have ht:=A.S.a_pos (i+1)
    have he : ((1024:ℝ)*(j+10)) ≤ X:= by exact_mod_cast h.cropK i
    rw [← A.S.embeds_scale (A.S.oneStep i 0)]; norm_num; let u:= A.S.a (i+1); change _ < u*X
    have hv:0 ≤ (j:ℝ):= Nat.cast_nonneg _
    linarith only [mul_le_mul_of_nonneg_left he ht.le,mul_nonneg ht.le hv,ht]
end YM.Trace.Terrace
