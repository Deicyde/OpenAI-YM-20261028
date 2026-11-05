import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Turmeric
/-! # Combine linear transfer from Φ book & central predictions
 all V-native coordinates. Scalar cost normalized -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shellac
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare  Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (A : ChartRatio G)
    (B : BudgetPoint) (ρ : Bid.Dir G c→AxisChart G F) (β α : ℝ) (k : S.Choices) {σ C Λ m M v d a H D u Θ γ p : ℝ} {j n : ℕ}
local notation "P" => Uniform.Primary c G
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "ψ" => mist F A T.up
local notation "K" => Lapis.gram F T.up T.high ρ k
local notation "Ω" => solar F A β
local notation "Y" => lack F T A B ρ β k D
local notation "L₀" => pigment F T A ρ β k D
local notation "W" => shed F T A ρ α k
local notation "f₁" => cedar F T ρ k
local notation "g" => harmony T B β α
variable (hV : Golf (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (gram F T.up T.high ρ k) n D u u H)
    (hp:T.down.Bounds T.low σ C Λ) (J : BareRates.pre G σ C n) (hs:1 ≤ M) (ht : (Fintype.card (Uniform.Primary c G):ℝ)≤ M)
    (hK:ClassicalMatch F T.high T.low T.up T.down ρ) (he: 5 ≤ n) (hS:S.patch.Branches S.kernel G)
include hV hp J hs ht he hK hS
lemma smuts (h : Brush 1 v 1 (Y) 0) (hh: Brush 1 d 1 L₀ 0): ‖fderiv ℝ W 0‖≤ v+d:= by
  let b x:= (Real.log Ω + L₀ x + Y x) + β • f₁ x
  let P₀ : Xs→ℝ:= (fun x=>Real.log Ω + L₀ x)+ (Y)
  have hz : (g)=fun x=>P₀ x+ β • f₁ x+ W x:= funext fun i=> merit F T A B ρ β α k i
  have ht' : (0:Xs)∈ball 0 u:=mem_ball_self hV.pos
  have hw := (hills F T A ρ α k hV hp J hs ht 0 ht').1; have hF := (sticks F T A ρ k hV hp J hs ht 0 ht').1; have hn : (1:ℕ) ≤ n := by omega
  have he : HasFDerivAt (g) (fderiv ℝ L₀ 0+fderiv ℝ (Y) 0+fderiv ℝ W 0) 0 := by
    let Q := hasFDerivAt_const (𝕜:=ℝ) (Real.log Ω) (0:Xs)
    have hx:= (Q.add (hh.smooth.differentiableAt (by norm_num)).hasFDerivAt).add ((h.smooth.differentiableAt (by norm_num)).hasFDerivAt)
    have hB:= ((hF.differentiableAt (by exact_mod_cast show n ≠ 0 by omega)).hasFDerivAt).const_smul β
    rw [(unshine F T A ρ k hV hp J hs ht 0 ht' hK he).2,smul_zero] at hB
    have hp:= (hx.add hB).add ((hw.differentiableAt (by exact_mod_cast show n ≠ 0 by omega)).hasFDerivAt); rw [add_zero,zero_add] at hp; rw [hz]; exact hp
  have hu := chant T B β α hS he.differentiableAt; rw [he.fderiv] at hu
  rw [(eq_neg_of_add_eq_zero_right hu), norm_neg]; apply (norm_add_le ..).trans; rw [add_comm v]; apply add_le_add <;> rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.1 hh).2 _ le_rfl; exact (Brush.offer.1 h).2 _ le_rfl

variable (hk : (Fintype.card (Site c):ℝ) ≤ M) (H₀:FiniteBound F T.up T.down T.high T.low α A ρ Θ γ p) (hρ : ρ 0=0) (hO : LocalRatio A) (hg : 0<Θ) (hy : 0 ≤ p)
local notation "A₀" => tollS M 2 (sailAmt M G * (Θ * p * Real.exp (-γ*c.val)))
include hk H₀ hρ hO hg hy
lemma swain (h : Brush 1 v 1 (Y) 0) (hh: Brush 1 d 1 L₀ 0) (x:Xs) (hx : x∈ball 0 u) :
    Brush n (cryo J T.low M H α Λ*u^3+ (3:ℝ)*((v+d)*u+A₀*u^2)) u⁻¹ (off W) x:= by
  let D:= off W; let C:= cryo J T.low M H α Λ
  let R x:=W x-W 0
  have hp₀ (i) (hi:i∈ball (0:Xs) u):= hills F T A ρ α k hV hp J hs ht i hi
  have ht₀ : (0:Xs)∈ball 0 u:=mem_ball_self hV.pos; have ha:= hp₀ _ ht₀
  have hs₀ := smuts F T A B ρ β α k hV hp J hs ht hK he hS h hh
  have hQ : 0≤v+d:= add_nonneg h.nonneg hh.nonneg; have hpI : 0<u:= hV.pos
  have hw:= sputter F T A ρ α k hV hs ht hk H₀ hρ hO hg hy; have hd:0 ≤ A₀:=(norm_nonneg _).trans hw
  have hf (i:ℕ) (hi:i≤n) (y:Xs) (hy:y∈ball 0 u) (hk:i≠0): normJ i D y=normJ i W y:= by unfold normJ D off; rw [iteratedFDeriv_sub_apply ((hp₀ y hy).1.of_le (Nat.cast_le.mpr hi)) contDiffAt_const]; obtain ⟨k,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hk; rw [iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]
  have h00 : normJ 0 D 0=0:= by unfold normJ D off; rw [norm_iteratedFDeriv_zero]; simp
  have h1: normJ 1 D 0 ≤ v+d:= by rw [hf 1 (by omega) _ ht₀ one_ne_zero, normJ, norm_iteratedFDeriv_one]; exact hs₀
  have h₃:3≤n:=by omega
  apply pools (f:=D) hV.pos hV.small h₃ (le_trans (norm_nonneg _) ((hp₀ _ ht₀).2 3 h₃ (by decide))) (by positivity) (fun y hy=> (hp₀ y hy).1.sub contDiffAt_const) (fun i h hh y hy=> by rw [hf i hh y hy (by omega)]; exact (hp₀ y hy).2 i hh (by omega)) _ _ hx
  intro i hi; interval_cases i
  · rw [h00,zero_mul]; positivity
  · rw [pow_one]; exact (mul_le_mul_of_nonneg_right h1 hV.pos.le).trans (le_add_of_nonneg_right (by positivity))
  rw [hf 2 (by omega) _ ht₀ (by decide)]; exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans (le_add_of_nonneg_left (mul_nonneg hQ hV.pos.le))

lemma auster (x:Xs) (hx : x∈ball 0 u) (hj : 1≤j) (hi:j≤n) (he' : 0<β) (h : Brush j v 1 (Y) x) (hr : Brush j v 1 (Y) 0) (hh: ∀ y∈closedBall (0:Xs) ‖x‖, Brush j d 1 L₀ y) :
    Brush j (d*u+(v+v)+ β*(kinBill n J T.low M H * u^5)+(cryo J T.low M H α Λ*u^3+ 3*((v+d)*u+A₀*u^2))) u⁻¹ (off (g)) x:= by
  have hU:= (unshine F T A ρ k hV hp J hs ht x hx hK he).1
  have hw := swain F T A B ρ β α k hV hp J hs ht hK he hS hk H₀ hρ hO hg hy (hr.smaller hj) ((hh 0 (mem_closedBall_self (norm_nonneg x))).smaller hj) x hx
  have hk : Brush j (v+v) u⁻¹ (off (Y)) x:= (h.separating ((Brush.certified zero_le_one _).climb hr.bound le_rfl)).climb le_rfl ((one_le_inv₀ hV.pos).2 hV.small)
  have hf:= (hU.smaller hi).smul β; rw [Real.norm_of_nonneg he'.le] at hf
  have hL:= rapid hh (mem_ball_zero_iff.mp hx).le hj hV.pos hV.small
  apply (((hL.gathering hk).gathering hf).gathering (hw.smaller hi)).shimmy; refine Eventually.of_forall fun j=>?_; change (g) j-(g) 0 = (L₀ j-L₀ 0+(Y j-Y 0))+ β*(f₁ j-f₁ 0)+(W j-W 0); rw [merit F T A B ρ β α k (D:=D) j,merit F T A B ρ β α k (D:=D) 0]; ring
end YM.PhysicalNext.Repeat.Shellac
