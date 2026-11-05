import YM.RemainderComparison.Access.Geometry
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogosG

/-!
 # Removal of fixed-chart truncation on arbitrary-order moment tensors.
 Price tail at same polynomial and inverse eta tolerances. Not running through
 unrestricted-density partition function. Uniform for these *polynomial volume*
 auxiliary estimates without dimension-dependent probability lower bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Germ
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Pressure Next.Scheduling Push.AbsoluteSums ConnectedActivityE6
open Coat PhysicalNext.Repeat Lantern Poll Blaze Flux
open scoped Topology BigOperators Classical NNReal ENNReal
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ}
variable {ι : Type} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ)
variable {m C A t c M : ℝ} {n j : ℕ}
local notation "Z" => (fun x=>betaF G x L)
local notation "S" => Poll.Body ι

def Contract (Q : Matrix ι ι ℝ) (c : ℝ) := ∀ z : ι→ℝ, dotProduct z (Q*ᵥ z) ≤ c * dotProduct z z

def vat (n : ℕ) (x : S) := (1+‖x‖)^n

def lump (n : ℕ) (c M : ℝ) := (1+M)^n *(1+M*(2*Real.exp (c*(n:ℝ)^2/2)))

-- Also in trivial/empty transverse dimension!
variable (hp : Q.PosSemidef) (hy : Contract Q c) (h : (Fintype.card ι:ℝ) ≤ M)
include hp hy h
lemma charges (k : ℕ) : Integrable (vat k) (sweep Q) ∧ ∫ z, vat k z ∂sweep Q ≤ lump k c M := by
  let b (z:S):=1+∑ i, (1+|z i|)^k
  let D:= 1+M; have hM : 0 ≤ M:= (Nat.cast_nonneg _).trans h
  have hD : 1 ≤ D:= le_add_of_nonneg_right hM
  have ht i : |Q i i| ≤ c := by
    let x : ι→ℝ:=Pi.single i 1
    have hx : dotProduct x (Q*ᵥ x)=Q i i:= by simp [x]
    have hf:0≤Q i i:= by
      rw [← hx]; exact hp.dotProduct_mulVec_nonneg x -- edit
    rw [abs_of_nonneg hf]
    simpa [x] using hy x
  obtain ⟨hk,hK⟩:= salience univ hp ht k
  have hQ (z:S): vat k z ≤ D^k*b z:= by
    cases isEmpty_or_nonempty ι
    · unfold vat b
      have h:z=0 := Subsingleton.elim ..
      simpa [h] using one_le_pow₀ hD (n:=k)
    obtain ⟨i,hi,hp⟩:= Finset.exists_max_image Finset.univ (fun i=>|z i|) (Finset.univ_nonempty) -- arg
    have hh : ‖z‖ ≤ D*|z i|:= by
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (zero_le_one.trans hD) (abs_nonneg _)), EuclideanSpace.real_norm_sq_eq, mul_pow]
      apply le_trans (sum_le_sum (g:= fun _=> |z i|^2) (fun j h=> show z j ^ 2 ≤ |z i|^2 from (sq_abs ..).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) (hp j h) _))) _
      rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (h.trans ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ hD (by decide)))) (sq_nonneg _)
    unfold vat; apply (pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖z‖) ((add_le_add hD hh).trans_eq (show D+D*|z i|=D*(1+|z i|) by ring)) k).trans
    rw [mul_pow]; unfold b; exact mul_le_mul_of_nonneg_left ((Finset.single_le_sum (f:=fun i=> (1+|z i|)^k) (fun i _=> by positivity) hi).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)
  have hd : Integrable b (sweep Q):=(integrable_const 1).add hk
  have hC : Integrable (vat k) (sweep Q):= (hd.const_mul (D^k)).mono' (by unfold vat; fun_prop) (ae_of_all _ fun z=> by
    rw [Real.norm_of_nonneg (show 0≤ vat k z by unfold vat; positivity)]
    exact hQ z)
  refine ⟨hC,(integral_mono hC (hd.const_mul _) hQ).trans ?_⟩
  rw [integral_const_mul]; unfold lump; refine mul_le_mul_of_nonneg_left ?_ (by unfold D; positivity)
  unfold b; rw [integral_add (integrable_const _) hk,integral_const,probReal_univ,one_smul]
  simp only [Finset.card_univ] at hK
  exact add_le_add_right (hK.trans (mul_le_mul_of_nonneg_right h (by positivity))) _

lemma daylight {v d A : ℝ} (ht : (sweep Q).real (closedBall (0:S) t)ᶜ ≤ d)
    (hv : 0 < v) (ha : 0 ≤ A) : ∫ z in (closedBall (0:S) t)ᶜ, A * vat n z ∂sweep Q ≤ A*(v⁻¹*d+v*lump (2*n) c M) := by
  have he := charges Q hp hy h (2*n)
  have hh (z:S) : vat n z ≤ v⁻¹ + v*vat (2*n) z := by
    have hK: vat (2*n) z=(vat n z)^2:= by unfold vat; rw [mul_comm 2,pow_mul]
    rw [hK]
    apply le_of_mul_le_mul_left _ hv
    rw [mul_add,mul_inv_cancel₀ hv.ne']
    nlinarith only [sq_nonneg (v*vat n z-1/2)]
  let K:Set S:=(closedBall 0 t)ᶜ
  rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ ha
  apply (integral_mono (μ:=(sweep Q).restrict K) ((charges Q hp hy h n).1.restrict) ((integrable_const _).add (he.1.const_mul v).restrict) hh).trans
  change (∫ i in K,v⁻¹+v*vat (2*n) i ∂sweep Q)≤_
  simp only [integral_add (integrable_const _) ((he.1.const_mul v).restrict),setIntegral_const, smul_eq_mul,integral_const_mul]
  have hP: ∫ i in K,vat (2*n) i ∂sweep Q ≤ ∫ i,vat (2*n) i ∂sweep Q:=
    setIntegral_le_integral he.1 (ae_of_all _ fun i=> by unfold vat; positivity)
  rw [mul_comm ((sweep Q).real K)]
  exact add_le_add (mul_le_mul_of_nonneg_left ht (inv_pos.mpr hv).le) (mul_le_mul_of_nonneg_left (hP.trans he.2) hv.le)

omit hp hy h
lemma lump_cost (c : ℝ) (hf : Reserve G L p) (n : ℕ) : Reserve G L fun x=> lump n c (p x) :=
  (((Reserve.const _).add hf).pow n).mul ((Reserve.const _).add (hf.mul (Reserve.const _)))
lemma night (hq : Reserve G L q) (hp : Bolt G L p) (hc : 0 < c) (he : 0 < t) (φ : ℝ) (k : ℕ) :
    ∀ᶠ x in atTop, ∀ (ι:Type) [Fintype ι] [DecidableEq ι] (S₀ : Matrix ι ι ℝ), (Fintype.card ι:ℝ)≤p x → 0 ≤ q x → S₀.PosDef → Contract S₀ c →
      (∫ z in (closedBall (0:Poll.Body ι) (Sienna.wick G L t x))ᶜ, q x * vat k z ∂sweep S₀) ≤ (Z x)^φ := by
  let θ := φ - 1
  let r:= θ * 2
  have hy := walls G L hp hc he r
  have hl := (lump_cost c (Reserve.covers hp) (2*k))
  let s α x:=Z x^(α:ℝ)
  have ht : Rate G L θ (fun x=> s (-θ) x*s r x) := (show Rate G L (-θ+r) _ from Rate.mul Rate.power Rate.power).weaken (by unfold r; linarith)
  have hx : Rate G L θ (fun x=> q x*(s (-θ) x*s r x+s θ x * lump (2*k) c (p x))) := by
    have hh := hq.rate.mul (ht.add (Rate.weaken (Rate.mul Rate.power hl.rate) (b:=θ) (a:=θ+0) (le_of_eq (add_zero θ))))
    rw [zero_add] at hh; exact hh
  filter_upwards [hx _ (sub_one_lt _),hy,Delay.shift_pos G L] with x hx hr hv ι _ _ S₂ hp hq hs hf
  let K:=closedBall (0:Poll.Body ι) (Sienna.wick G L t x)
  have hh: (sweep S₂).real Kᶜ ≤ s r x:= by
    rw [measureReal_compl (by unfold K; exact measurableSet_closedBall),probReal_univ]; exact hr ι S₂ hp hs hf
  let v:= s θ x; have hz := daylight S₂ hs.posSemidef hf hp (n:=k) hh (show 0<v from Real.rpow_pos_of_pos hv _) hq
  rw [show v⁻¹= s (-θ) x from (Real.rpow_neg hv.le θ).symm] at hz
  exact hz.trans ((le_abs_self _).trans hx)

end YM.RemainderComparison.Germ
