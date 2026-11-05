import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Sum

/-! # Operator cost of actual pure push derivatives. Relative invoice
 Never assume nearby x stays in flag set. Fixed base; uses noise only.
 Gross.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Token
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S)
    (B : BudgetPoint) (β : ℝ) (k : S.Choices) {n : ℕ} {r C Z : ℝ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun x:Xs=> represent (tint G _ x))
local notation "M" => Pane.virgin T B β

section norm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma seasons (p : E→ℝ) {t a : ℝ} (ht:0≤t) (x:E) (hx: Brush n a 1 p x) (hr : Brush n C 1 Real.exp 0) :
    Brush n (clump n (a+a) C * (t*Real.exp (p x))) 1 (fun x=> t*Real.exp (p x)) x := by
  let g y:=p y-p x; have hp:Brush n (a+a) 1 g x:= hx.separating ((Brush.certified zero_le_one _).climb hx.bound le_rfl); have hk:= composite hp (show Brush n C 1 Real.exp (g x) from ((by rw [show g x=0 by unfold g; ring]; exact hr)))
  have h:= hk.smul (t*Real.exp (p x)); rw [Real.norm_of_nonneg (mul_nonneg ht (Real.exp_pos _).le),mul_comm] at h
  apply h.shimmy; refine Eventually.of_forall (fun i=>?_); unfold Function.comp; unfold g; dsimp only; rw [smul_eq_mul, mul_assoc, ← Real.exp_add,add_sub_cancel]
end norm
variable {t : ℝ}
def sizeN (G : Gauge) (k : KernelChoices) (n:ℕ) (r Z : ℝ) := k.penalty*r* priceCost G (2^n * outerCost G n Z*G.colorScale)
include k
lemma dates {U : Config G f} (hp : PaintSupply G n Z) (h : (Fintype.card (Bond c):ℝ)≤ r) (x:Xs) (hx: ‖x‖≤1) : Brush n (sizeN G S.kernel n r Z) 1 (fun v=> noiseTaylor S (V v) U k) x := by
  let u:= outerCost G n Z; let m:= priceCost G (2^n * u*G.colorScale)
  let f (i:Bond c) v:= G.price (V v i*(S.prediction U k i)⁻¹)
  have he i : Brush n m 1 (f i) x := by
    let j:= (i.1,Exterior.coord i.2); let o := Exterior.Body 1 c
    let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : o => G.Color) j ∘L (tint G o).toContinuousLinearMap
    have hQ : ‖L‖≤ Uniform.shade G := ContinuousLinearMap.opNorm_le_bound _ (Uniform.shade_pos _).le fun v=> le_trans (norm_le_pi_norm (tint G o v) _) (Uniform.tint_le v)
    have hL : ‖L x‖ ≤ Uniform.shade G := (L.le_opNorm x).trans ((mul_le_mul hQ hx (norm_nonneg x) (Uniform.shade_pos _).le).trans_eq (mul_one _))
    have hf : Allows n (fun v:Xs=> G.mat (V v i)) x u:= by
      have hh v : V v i=G.lieExp (L v) := Work.F03.represent_link _ _
      simp_rw [hh]; exact (hp.2 _ hL).comp (allows_linear hQ hL)
    let u' := (S.prediction U k i)⁻¹
    have ht : Allows n (fun _ : Xs=> G.mat u') x G.colorScale:= allows_const x (le_of_eq (by simp only [Gauge.colorScale, YM.Gauge.unitary_frob (G.mat_mul_star u')]))
    have hK : Allows n (f i) x m:= Allows.price (Allows.times (f:=fun v=> V v i) hf (g:=fun _=> u') ht)
    exact Brush.offer.2 ⟨hK.1.of_le le_top,hK.2⟩
  have hz := (Brush.spree univ f (fun _=> m) zero_le_one (fun i _=> he i)).smul S.kernel.penalty; simp only [sum_const,nsmul_eq_mul,card_univ, Real.norm_of_nonneg S.kernel.penalty_pos.le] at hz; apply hz.climb _ le_rfl; unfold sizeN; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (he (Classical.arbitrary _)).nonneg) S.kernel.penalty_pos.le

def prime (G : Gauge) (k : KernelChoices) (n : ℕ) (Z C β r : ℝ) := let p:= |β| *sizeN G k n r Z; clump n (p+p) C
lemma inc (U : F.Slice G) (hp : PaintSupply G n Z) (h : (Fintype.card (Bond c):ℝ)≤ r) (x:Xs) (hx: ‖x‖≤1) (hr : Brush n C 1 Real.exp 0) : Brush n (prime G S.kernel n Z C β r * actU F T k B β (V x) U) 1 (fun x=> actU F T k B β (V x) U) x:= by
  let t:= prefactor S G β*S.likelihood (F.drape U) k * (M).eval (F.drape U); let a (x:Xs):= actU F T k B β (V x) U; let p (x:Xs):= -β*noiseTaylor S (V x) (F.drape U) k
  have he:a=(fun x=>t*Real.exp (p x)):= by funext i; unfold a actU taggedKernel t p; rw [true_point]; ring
  have ht:0 ≤ t:= mul_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr (S.penaltyZ_pos _)).le _) (S.likelihood_pos ..)) (by rw [Pane.sparkling]; split <;> positivity)
  have hA := (dates (U:=F.drape U) k hp h x hx).smul (-β); rw [norm_neg] at hA
  change Brush n (_ * a x) 1 a x; rw [he]; exact seasons p ht x hA hr

omit k
lemma volumeQ (U : F.Slice G) (hp : PaintSupply G n Z) (h : (Fintype.card (Bond c):ℝ)≤ r) (x:Xs) (hx: ‖x‖≤1) (hr : Brush n C 1 Real.exp 0) : Brush n (prime G S.kernel n Z C β r * overall F T B β (V x) U) 1 (fun x=> overall F T B β (V x) U) x:= by
  unfold overall; rw [Finset.mul_sum]; exact Brush.spree _ _ _ zero_le_one fun i _=> inc F T B β i U hp h x hx hr
end YM.PhysicalNext.Repeat.Token
