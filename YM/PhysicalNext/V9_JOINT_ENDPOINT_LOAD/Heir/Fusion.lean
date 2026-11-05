import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Cover
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Crowd
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Transit


/-!
# Combined large/small per-occurrence estimate on the actual input mass

Before-L overhead depends on the caller's REAL support radius and desired
FULL output exponent (not capped to the budgetPoint exponent at the
use site). After-L numeric criterion `Plented` kept initially. Lute
attenuation taken BEFORE charging any new overlap at an enlarged Y. No
subtraction or replacement of existing empirical payments in a forest
mixture authorized just by this estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Lattice Wilson Pressure RG Tree Next Exterior Bloch Planned.AtomRegular MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {X : Support f} {L : Side} {P B : BudgetPoint} {x u t τ : ℝ} {n r : ℕ} {C : Libretto G n} {D : Record}
    {S : StepData c f} {Y : Support c}
namespace Lute

def debited (n p : ℕ) := fuse n p*(n+n)+visitors n
def Plented (C : Libretto G n) (D : Record) (P B : BudgetPoint) (L : Side) (r : ℕ) (x u : ℝ) :=
    ((boost C D L*Lute.ζ B u)^(n+n) * guests G D.K n L) * ((r+48:ℝ)*(1+(radiusB x:ℝ)))^debited n P.power ≤ 1

variable (h : B.B≤2*radiusB x) (ht : P.threshold≤2*B.threshold) (hu : 0≤u) (hw : Plented C D P B L r x u)
include h ht hu hw
lemma extra_le : rust C D P B L X r x u ^(n+n) * AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)) ≤ (1+(coverNumber B.B X:ℝ))^debited n P.power := by
  let A := ((r+48:ℝ)*(1+(radiusB x:ℝ))); let d : ℝ := coverNumber B.B X; let H := debited n P.power
  let s := bulk (coverNumber B.B X) r x; have hs : 1 ≤ s := bulk_one ..
  let K := boost C D L*Lute.ζ B u; have hK : 0 ≤ K := mul_nonneg (boost_nn ..) (add_nonneg B.threshold_pos.le (div_nonneg hu B.threshold_pos.le))
  have hm : 0 ≤ AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)) := by unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; have := D.peak; positivity
  have he := fares (n:=n) (G:=G) (L:=L) (r:=r) (X:=X) (D:=D) h
  calc
    _ ≤ (K*s^fuse n P.power)^(n+n) * (guests G D.K n L * s^visitors n) := mul_le_mul (pow_le_pow_left₀ (rust_nn hu) (booster h ht hu) _) he hm (by positivity)
    _ = ((K^(n+n) * guests G D.K n L)* A^H)*(1+d)^H := by unfold H debited; change (K*(A*(1+d))^fuse n P.power)^_*(_*(A*(1+d))^visitors n) = _; simp only [mul_pow (a:=A),mul_pow (a:=K), pow_add]; ring
    _ ≤ _ := mul_le_of_le_one_left (by unfold d; positivity) hw

lemma issued : returnFee C D P B L X r x u ≤ 2*beat C*((L.val:ℝ)⁻¹)^5*(1+(coverNumber B.B X:ℝ))^(15+debited n P.power) := by
  let d : ℝ := coverNumber B.B X; let H := debited n P.power
  have he : 0 < (L.val:ℝ) := Nat.cast_pos.mpr L.property
  have hd : 1 ≤ 1+d := le_add_of_nonneg_right (Nat.cast_nonneg _); have hb := beat_nn C
  have hD : decay B L X ≤ ((L.val:ℝ)⁻¹)^5*(1+d)^15 := by
    unfold decay; split; · exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hd)
    rw [inv_pow, inv_mul_eq_div,le_div_iff₀ (pow_pos he _),one_mul, show 15 = 3*5 from rfl, pow_mul]; gcongr
    unfold d; exact_mod_cast le_trans (show L.val ≤ coverNumber B.B X ^3 by omega) (Nat.pow_le_pow_left (Nat.le_add_left _ 1) 3)
  have hm : 0 ≤ AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)) := by unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; have := D.peak; positivity
  have hr := rust_nn (C:=C) (D:=D) (P:=P) (B:=B) (L:=L) (X:=X) (r:=r) (x:=x) hu
  have hh := extra_le h ht hu hw (X:=X); unfold returnFee
  calc
    _ ≤ (beat C*(((L.val:ℝ)⁻¹)^5*(1+d)^15))*((1+d)^H+(1+d)^H) := by gcongr; exact one_le_pow₀ hd
    _ = _ := by rw [pow_add]; unfold d H; ring
end Lute
namespace Release

def base (a : ℝ) (r : ℕ) := a*(toll r:ℝ)
def accepts (r : ℕ) (A a : ℝ) (L : Side) := 20*base a r ≤ (L.val:ℝ)*A
lemma compressed (ha : 0≤t) (hh : accepts r B.supportExponent t S.patch.L) (h : Walled S X Y x r) (hP : P.B=radiusB x) (he : B.B≤2*P.B) :
    t*coverNumber P.B Y ≤ base t r + (B.supportExponent/2)*coverNumber B.B X := by
  have hl : 0 < (S.patch.L.val:ℝ) := by positivity
  have he := Corona.collapse S.ratio X _ _ P.B_pos he r
  unfold Walled at h; rw [← hP] at h; have he : S.patch.L.val*coverNumber P.B Y ≤ (S.patch.L.val+10*coverNumber B.B X)*toll r := (Nat.mul_le_mul_left _ (Corona.cover_mono h _)).trans he
  have ht : (S.patch.L.val:ℝ)* ↑(coverNumber P.B Y) ≤ (S.patch.L.val+10*(coverNumber B.B X:ℝ))*(toll r:ℝ) := by exact_mod_cast he
  unfold accepts base at hh; unfold base; apply le_of_mul_le_mul_left (a:=(S.patch.L.val:ℝ)) _ hl
  nlinarith only [mul_le_mul_of_nonneg_left ht ha,mul_le_mul_of_nonneg_right hh (show (0:ℝ) ≤ coverNumber B.B X from Nat.cast_nonneg _)]

theorem preprices (C : Libretto G n) (p r : ℕ) {A t : ℝ} (hA : 0<A) (ht : 0≤t) : ∃ rate : ℝ, 1≤rate ∧
    ∀ {c f : Side} (S : StepData c f) (D : Record) (P B : BudgetPoint) (X : Support f) (Y : Support c) (u x : ℝ),
      P.power=p → B.supportExponent=A → accepts r A t S.patch.L → Walled S X Y x r → P.B=radiusB x → B.B≤2*P.B → P.threshold ≤2*B.threshold →
      0≤u → Lute.Plented C D P B S.patch.L r x u → ∀ τ : ℝ, 0≤τ →
      Real.exp (t*coverNumber P.B Y)*(τ*Lute.returnFee C D P B S.patch.L X r x u) ≤ rate*((S.patch.L.val:ℝ)⁻¹)^5 * B.mass X τ := by
  let Z := 2*Lute.beat C; have hZ : 0 ≤ Z := by unfold Z; positivity [Lute.beat_nn C]
  let j := 15+Lute.debited n p
  obtain ⟨R,hR,H⟩ := MultiNext.SignedSource.Newt.length_mom j (half_pos hA)
  refine ⟨1+Real.exp (base t r)*Z*R,le_add_of_nonneg_right (by positivity),?_⟩
  intro c f S D P B X Y u x hP hB hh hw hR' hK ht' hu he τ hτ
  let z : ℝ := coverNumber B.B X; let L := (S.patch.L.val:ℝ)
  have hN : 0 ≤ B.mass X τ := mul_nonneg (Real.exp_nonneg _) hτ
  have hy : t*coverNumber P.B Y ≤ base t r+(A/2)*z := hB ▸ compressed ht (hB.symm ▸ hh) hw hR' hK
  have hr := Lute.issued (X:=X) (hR' ▸ hK) ht' hu he; rw [hP] at hr
  calc
    _ ≤ Real.exp (base t r+(A/2)*z)*(τ*((Z*L⁻¹^5)*(Real.exp ((A/2)*z)*R))) := by
        apply mul_le_mul (Real.exp_monotone hy) (mul_le_mul_of_nonneg_left (hr.trans (mul_le_mul_of_nonneg_left (H _) (by positivity))) hτ) _ (Real.exp_nonneg _)
        unfold Lute.returnFee; have hK := D.peak; have hm : 0 ≤ AnalyticBridge.LocalGaussian.Moments.meter (Lute.heads G B S.patch.L X r x) 0 D.K (2*(n+n)) := by unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; positivity
        positivity [Lute.beat_nn C,Lute.decay_pos (B:=B) (X:=X) (L:=S.patch.L),Lute.rust_nn (C:=C) (D:=D) (P:=P) (B:=B) (L:=S.patch.L) (r:=r) (x:=x) (X:=X) hu]
    _ = Real.exp (base t r)*Z*R * L⁻¹^5*B.mass X τ := by
      unfold BudgetPoint.mass; rw [hB,show A*z=(A/2)*z+(A/2)*z by ring,Real.exp_add,Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)) hN
end Release
end YM.PhysicalNext.JointLoad.Heir
