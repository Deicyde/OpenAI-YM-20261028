import YM.Pert.Spatial.Wide

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(D d :ℕ){x:ℝ} {j : ℕ→ℕ}
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "q₀"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "K"=> C.path.levels.budget
local notation "H"=> C.path.levels.clock.hatBeta
local notation "ℓK" => spacingFactor C.path.levels
variable (hG:G.Simple)(t:ℝ) (hT:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t)) (hj:Tendsto j atTop atTop)
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hV:Velour C (renal C.path.levels) r D')
variable {b a:ℝ}(hb:0<b)(ha:0<a)
open Accent Source Extra.Histories
variable {u ψ:ℕ→ℝ}{W:Worth}
variable (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')

/-- Extra post-block condition (before Delays), so the enlarged margin fits the
Sail preimage width with log-cost negligible on every fine-calendar scale.
Proof of supply is in Deeper, not a consequence here of `hV`.
-/
def Plenty := ∀ i, ((K i).supportExponent+1)*((ℓK i:ℕ):ℝ)^4 ≤ Real.sqrt (H i)
include hG

theorem coverGrowth : Tendsto (fun i:ℕ=>(1+((K i).B:ℝ))^8/(H i)) atTop (𝓝 0) := by
  let x(i:ℕ):= H i
  have ht : Tendsto x atTop atTop:= tendsto_atTop_add_const_left _ _ (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have hh : Tendsto (fun i:ℕ => (3^8:ℝ)*(Real.log (x i)^16 / x i)) atTop (𝓝 0) := by
      simpa using! (((Real.tendsto_pow_log_div_mul_add_atTop 1 0 16 one_ne_zero).comp ht).const_mul ((3:ℝ)^8))
  refine squeeze_zero' (Eventually.of_forall fun i=> by have := ((hut C hG).pos i).le; positivity) ?_ hh
  filter_upwards [(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with i hi;
  · have hx : ((K i).B:ℝ) ≤ 2*Real.log (x i)^2 := by
      change (⌈Real.log (x i)^2⌉₊:ℝ) ≤ _
      simp only [Function.comp_apply] at hi
      nlinarith only [hi,Nat.ceil_lt_add_one (sq_nonneg (Real.log (x i)))]
    have hz : 1+((K i).B:ℝ) ≤ 3*Real.log (x i)^2 := by simp only [Function.comp_apply] at hi;nlinarith
    calc
      _ ≤ ((3:ℝ)*Real.log (x i)^2)^8/x i := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hz 8) ((hut C hG).pos i).le
      _ = (3^8:ℝ)*(Real.log (x i)^16/x i) := by ring
include hV in
-- wrapper to pay the change relative to `whack`/`pica`, not replace all those post costs
lemma wide_cost (hp : Plenty C) : Tendsto (fun m=>Real.log
    (Real.exp (-(((K m).supportExponent+1/2)*((crowd (P) m : ℝ) - (peepers (P) m : ℝ))))) / q₀ m) atTop (𝓝 0) := by
  have old := whack C hG hV
  suffices he : Tendsto (fun m=>((K m).supportExponent+1/2)*((crowd (P) m : ℝ))/q₀ m) atTop (𝓝 0) by
    simp_rw [Real.log_exp, mul_sub,neg_sub, sub_div]
    simpa using! old.sub he
  let B m:= (1+((K m).B:ℝ))^4 / (Real.sqrt (H m))
  have hx : Tendsto (fun m=> H m / q₀ m) atTop (𝓝 G.slopeConstant) := by
    have hp : Tendsto (fun i=> C.path.levels.clock.bar/q₀ i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop C.S.divergent
    refine (show Tendsto (fun i=> C.path.levels.clock.bar/q₀ i+G.slopeConstant) atTop (𝓝 G.slopeConstant) from by simpa only [zero_add] using! hp.add_const G.slopeConstant).congr' ?_; filter_upwards [C.S.divergent.eventually_gt_atTop 0] with i hi
    change _= (C.path.levels.clock.bar+G.slopeConstant*q₀ i)/_; rw [add_div,mul_div_cancel_right₀ _ hi.ne']
  have hB : Tendsto B atTop (𝓝 0) := by
    refine (show Tendsto (fun m=>Real.sqrt ((B m)^2)) atTop (𝓝 (Real.sqrt 0)) from ?_).congr ?_ |> (Real.sqrt_eq_zero_of_nonpos le_rfl ▸ ·)
    · exact (Real.continuous_sqrt.continuousAt.tendsto.comp ((coverGrowth C hG).congr (fun i=>by unfold B; rw [div_pow,←pow_mul,Real.sq_sqrt ((hut C hG).pos i|>.le)])))
    intro m; rw [Real.sqrt_sq (by unfold B; positivity)]
  have hpos m : 0 < Real.sqrt (H m) := Real.sqrt_pos.2 ((hut C hG).pos m)
  have hden m : 1 / Real.sqrt (H m) * (H m / q₀ m) = Real.sqrt (H m)/q₀ m := by
    rw [← mul_div_assoc (1/_ : ℝ), div_mul_eq_mul_div,div_right_comm]
    have ht := Real.sq_sqrt (((hut C hG).pos m).le)
    field_simp [(hpos m).ne']; rw [ht]
  refine squeeze_zero' (Eventually.of_forall fun i=> by have := (K i).exponent_pos; have := RG.Shoot.scale_nn (P) i; positivity)
    (Eventually.of_forall (fun i => ?_)) (g:=fun i=> (((2049:ℝ)^4*(B i)) * (H i / q₀ i))) (show _ from ?_)
  · unfold crowd B
    push_cast
    let x := (K i).B
    let y := (K i).supportExponent
    let u : ℝ := ℓK i
    let β := H i
    have hb : 0 ≤ (x:ℝ) := Nat.cast_nonneg _
    have hy : 0 ≤ y := ((K i).exponent_pos).le
    have hu : 1 ≤ u := Nat.one_le_cast.mpr (C.S.block (i-1)).pos
    calc
      _ ≤ ((y+1)*u^4) * (((2049*(1+x))^4)) / q₀ i := div_le_div_of_nonneg_right (?_) (RG.Shoot.scale_nn (P) i)
      _ ≤ (Real.sqrt β)*((2049*(1+x))^4) / q₀ i := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hp i) (by positivity)) (RG.Shoot.scale_nn (P) i)
      _ = _ := by rw [mul_pow]; change _ = _ * (_ / _) * (β / _); rw [show (2049^4:ℝ)*((1+x)^4 / Real.sqrt β)*(β / q₀ i) = (2049^4:ℝ)*((1+(x:ℝ))^4)*(1/Real.sqrt β*(β / q₀ i)) from by ring,hden];ring
    · rw [mul_assoc (y+1),← mul_pow]; change (y+1/2)*(2*(u*1024*x)+1)^4 ≤ _
      gcongr <;> nlinarith only [hb,hu,mul_nonneg (zero_le_one.trans hu) hb]
  · simpa using! (hB.const_mul ((2049:ℝ)^4)).mul hx
end YM.MergeProof.Ribbons
