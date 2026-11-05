import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Glowing
import YM.PhysicalNext.ORDERED_AFFINE_2B.Pay
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Proof
import YM.Primitives.SMALL_FIELD_EXTERIOR.Window
import YM.ProjectorNext.EQUATION_CAMPAIGN.Receiving

/-! # Unrearranged auxiliary charge. Still any α. This is post-Kin. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shellac
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare  Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (A : ChartRatio G)
    (B : BudgetPoint) (ρ : Bid.Dir G c→AxisChart G F) (β α : ℝ) (k : S.Choices) {σ C Λ m M v d a H D u Θ γ : ℝ} {j n : ℕ}
local notation "P" => Uniform.Primary c G
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun (x:Xs)=> represent (tint G _ x))
local notation "f₁" => Lapis.table F k T.up T.high
local notation "μ" => Lapis.orbit F ρ
local notation "ψ" => mist F A T.up
local notation "K" => Lapis.gram F T.up T.high ρ k
local notation "Ω" => solar F A β

local notation "w" => shed F T A ρ α k
def cryo {σ C : ℝ} (J : BareRates.pre G σ C n) (p : Clip) (M H α Λ : ℝ) := tollS M n ((1+|α|+Λ)*BareRates.bill J p)+(wood n H + H)
variable (hV : Golf (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (gram F T.up T.high ρ k) n D u u H)
    (hp:T.down.Bounds T.low σ C Λ) (J : BareRates.pre G σ C n) (hs:1 ≤ M) (ht : (Fintype.card (Uniform.Primary c G):ℝ)≤ M)
section smooth
include hV hp hs ht
lemma hills (x:Xs) (hx:x∈ball 0 u): ContDiffAt ℝ n w x ∧ ∀ i ≤ n, 0 < i → normJ i w x ≤ cryo J T.low M H α Λ:= by
  obtain ⟨-,hf,h,hC,-,hh⟩:= bareSocket c J hp (ball_subset_ball hV.small hx) α
  have hg:= vill F T A ρ k hV x hx|>.2
  let f x:= hum F T A ρ k x-Lantern.shade (K) 0
  have he : hum F T A ρ k=f+(fun _=> Lantern.shade (K) 0):= funext fun i=> (sub_add_cancel ..).symm
  let v (x:Xs):= draft α T.down T.low (tint G _ x)
  change ContDiffAt ℝ n (v-hum F T A ρ k) _ ∧ ∀ _ : ℕ,_
  have ht' : ContDiffAt ℝ n f x:=hg.smooth
  refine ⟨(by rw [he]; exact (hf.of_le le_top).sub (ht'.add contDiffAt_const)), fun i hi h₁=>?_⟩
  have hA : ContDiffAt ℝ (i:ℕ) f x:= (hg.smaller hi).smooth
  change normJ i (v-hum F T A ρ k) _ ≤ _; rw [he,normJ,iteratedFDeriv_sub_apply (show ContDiffAt ℝ i v x from hf.of_le le_top) (show ContDiffAt ℝ i (f + fun _=> Lantern.shade (K) 0) x from hA.add contDiffAt_const),iteratedFDeriv_add_apply hA contDiffAt_const]
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero h₁.ne'; rw [iteratedFDeriv_succ_const,Pi.zero_apply,add_zero]; apply (norm_sub_le ..).trans; have hx := hasInheritance hp; exact add_le_add (ratifyS hs ht h (by positivity) hh hi h₁) ((Brush.offer.1 hg).2 _ hi)
omit hp hs ht in
lemma thermalP (hO:LocalRatio A) (hρ : ρ 0=0) : thermal F k T.high T.up ρ A ∘ tint G _ =ᶠ[𝓝 0] hum F T A ρ k := by
  have hf : ContinuousAt (μ) 0:= (hV.curve _ (show ‖(0:Xs)‖<u by simp [hV.pos])).smooth.continuousAt
  have hv : μ 0=0:= by unfold Lapis.orbit Uniform.station; simp [hρ]
  have hc : ∀ᶠ x:Xs in 𝓝 0, windmill F (μ x)∈ mouth A := by
    have hh i (hi:i∈ (Set.univ:Set F.Free)):∀ᶠ x:Xs in 𝓝 0,(windmill F (μ x) i)∈ball (0:G.Color) A.radius := by
      let L:= tint G F.Free; let g:=weld (Precision.Key F G)
      have he : ContinuousAt (fun x=> L (g (μ x)) i) 0:= (continuous_apply i).continuousAt.comp (L.continuousAt.comp (g.continuousAt.comp hf))
      have hs: L (g (μ 0)) i=0:= by rw [hv,map_zero,map_zero]; rfl
      exact he.eventually (by change ball (0:G.Color) _ ∈ 𝓝 (L (g (μ 0)) i); rw [hs]; exact ball_mem_nhds _ hO.patch)
    filter_upwards [eventually_all.mpr (fun i=>hh i (Set.mem_univ i))] with x hx using (fun i _=>hx i)
  filter_upwards [hc] with x hx; unfold thermal hum; dsimp only [Function.comp_apply]; rw [Lapis.plume,Real.log_prod (fun i _=> (show 0 < A.J (ρ (tint G _ x) i) from hO.pos _ (hx i (Set.mem_univ _))).ne')]; change _ + (1/2:ℝ)* Real.log ((K) x).det-_ = Precision.loop T.up (lifting F (V x) (ρ (tint G _ x)))-(∑ i:F.Free,Real.log (A.J (ρ (tint G _ x) i))) + Lantern.shade (K) x; unfold Lantern.shade; ring
end smooth

-- All component bound. Glowing.confer avoids cardinal-tag overhead.
open Further.PhysicalPeriodLimitF933
variable {p : ℝ} (hk : (Fintype.card (Site c):ℝ) ≤ M) (H₀:FiniteBound F T.up T.down T.high T.low α A ρ Θ γ p) (hρ : ρ 0=0) (hO : LocalRatio A) (hg : 0<Θ) (hy : 0 ≤ p)
def sailAmt (M : ℝ) (G : Gauge) := M^4 * (Uniform.shade G)^2 * M
include H₀ hρ hk ht hO hg hy hs hV
lemma sputter : normJ 2 w 0 ≤ tollS M 2 (sailAmt M G * (Θ * p * Real.exp (-γ*c.val))) := by
  let W v:=draft α T.down T.low (c:=c) v -- argument c
  let V₀:= thermal F k T.high T.up ρ A
  let L:=(tint G (Exterior.Body 1 c)).toContinuousLinearMap
  let f:=W-V₀
  have hz : w=ᶠ[𝓝 0] f ∘ L:= by filter_upwards [thermalP F T A ρ k hV hO hρ] with x hx using (congr_arg (W (L x)-·) hx).symm
  unfold normJ; rw [(hz.iteratedFDeriv ℝ 2).self_of_nhds]
  let m := p * Real.exp (-γ*c.val); let q:=Θ*m
  have hq : 0 ≤ q:=by unfold q m; positivity
  have hv : ContDiffAt ℝ 2 V₀ 0:= (H₀.born k).of_le le_top; have ht' : ContDiffAt ℝ 2 W 0:=H₀.classicalResult.of_le le_top
  have hζ : iteratedFDeriv ℝ 2 f 0= iteratedFDeriv ℝ 2 W 0-iteratedFDeriv ℝ 2 V₀ 0:= iteratedFDeriv_sub_apply (i:=2) (by simpa) (by simpa)
  let Z:=fderiv ℝ (fderiv ℝ f) 0
  have hK : ∀ x y : Bid.Dir G c, iteratedFDeriv ℝ 2 f 0 ![x,y]=Z x y:=fun x y=> by rw [iteratedFDeriv_two_apply]; rfl
  have hm x y a b (ha:Glowing.unitSize (G:=G) a) (hb:Glowing.unitSize b): |Z (wave x a) (wave y b)| ≤ M*q := by
    rw [← hK,hζ,_root_.sub_apply,abs_sub_comm]
    apply (H₀.wave_price k x y a b ha hb).trans
    apply le_trans (b:=(Fintype.card (Site c):ℝ)*q) (le_of_eq (by unfold q m; ring)) (mul_le_mul_of_nonneg_right hk hq)
  have H' : ContDiffAt ℝ ((2:ℕ):ℕ∞ω) f (L 0) := by rw [map_zero]; simpa using! ht'.sub hv
  have hS:= Uniform.shade_pos G
  apply raises hs ht (by rw [mul_assoc Θ]; unfold sailAmt; positivity) le_rfl; intro v
  let x := bolt (v 0); let y:= bolt (v 1)
  have he : entry (f ∘ L) 0 v=Z (L x) (L y):= by
    unfold Push.Uniform.entry; rw [linear_pull L H',map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply]
  rw [he]; have hh (i:P) : ‖L (bolt i)‖ ≤ Uniform.shade G := (tint_le _).trans (mul_le_of_le_one_right hS.le ((norm_bolt i).le))
  have ht':0 ≤ M:= zero_le_one.trans hs
  apply (Glowing.confer Z hm (L x) (L y) (hh _) (hh _)).trans
  unfold sailAmt; rw [mul_assoc Θ, mul_assoc (M^4 * _)]; apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) ht _) (pow_le_pow_right₀ hs (by decide))) (sq_nonneg _)) (mul_nonneg ht' hq) -- algebra associativity
end YM.PhysicalNext.Repeat.Shellac
