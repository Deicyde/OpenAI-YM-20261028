import YM.Pert.Parity.Pull
import YM.Pert.Position.Detect
/-! Value tests on general nonlinear columns, paired with their graded transforms. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Pert.Parity
open Position Labels Full Filter Function Set Topology Maxwell Lattice
open scoped Topology Classical
variable {G : Gauge} (F : Frames G) (d : ℕ) {k : ℕ} (s : Fin k→Section F d)
local notation "S" => Section F d

def scenery (b : Fin k × Fin 2) : S := {r := (s b.1).r, p := if b.2=0 then (s b.1).p else Coat F d ∘ (s b.1).p, f := (s b.1).f}
def duo : (Fin (k*2) → S) := scenery F d s ∘ finProdFinEquiv.symm

lemma unshifted (i : Fin k) : duo F d s (finProdFinEquiv (i,0))=s i := by
  have : finProdFinEquiv.symm (finProdFinEquiv (i,(0:Fin 2)))=(i,(0:Fin 2)) := finProdFinEquiv.symm_apply_apply _
  unfold duo; dsimp only [comp_apply]; rw [this,scenery]; dsimp

lemma shifted (i : Fin k) : duo F d s (finProdFinEquiv (i,1))=scenery F d s (i,1) := congrArg _ (finProdFinEquiv.symm_apply_apply (i,(1:Fin 2)))
def valueSeries (q : S) (L : Side) (m) (v : Fin q.r→E F d) := profile d q.r F L m (q.f) v
def culm (q : S) (L : Side) (m p:ℕ) (v : Fin q.r→E F d) (t : ℝ) : ℂ := ∑ a∈Finset.range (p+1), t^a • PowerSeries.coeff a (valueSeries F d q L m v)
def sample (b : Buffer F d) (L m p t) (q : S) := (culm F d q L m p (fun j=> motor F b (q.p j)) t).re
lemma sample_switch (b : Buffer F d) (L m p t) (i : Fin k) : sample F d b L m p t (duo F d s (finProdFinEquiv (i,0))) = sample F d (twice F d b) L m p (-t) (duo F d s (finProdFinEquiv (i,1))) := by
  rw [unshifted,shifted]; unfold sample; apply congrArg Complex.re
  unfold culm; change Finset.sum _ _ = Finset.sum _ _; refine Finset.sum_congr rfl fun a _=>?_
  have h₂ (j : Fin (s i).r) : (scenery F d s (i,1)).p j=Coat F d ((s i).p j) := by simp [scenery]
  have h (u) := twice_motor F b (Coat F d u)
  change t^a • PowerSeries.coeff a (valueSeries F d (s i) L m (motor F b ∘(s i).p)) = _
  have hw : (fun j => motor F (twice F d b) ((scenery F d s (i,1)).p j)) = Coat F d ∘(motor F b ∘ (s i).p) := by funext; rw [h₂,h,Coat_round];rfl
  rw [hw];change _ = (-t)^a • PowerSeries.coeff a (valueSeries F d (s i) L m (Coat F d ∘ _)); simp only [valueSeries, profile_reflect ,PowerSeries.coeff_rescale, show -t=(-1:ℝ)*t from neg_one_mul t |>.symm, mul_pow,Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_one]
  rw [mul_mul_mul_comm, ←mul_pow, neg_mul_neg, mul_one, one_pow, one_mul]

lemma reconstruct (q : S) (L : Side) (m a v) :
    ∑ z : Fin q.r→ ChartIx F d, (∏ j, (baring F d).coord (z j) (v j)) * PowerSeries.coeff a (valueSeries F d q L m (fun j=> baring F d (z j))) = PowerSeries.coeff a (valueSeries F d q L m v) := by
  let he := (PowerSeries.coeff a).compMultilinearMap (profile d q.r F L m q.f)
  change (∑ z: Fin q.r→ ChartIx F d, _ * he (fun j=>baring F d (z j)))=he v
  conv_rhs=> rw [←funext (fun i=> (baring F d).sum_equivFun (v i))]
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]; refine Finset.sum_congr rfl fun z _=>?_ ;rw [he.map_smul_univ]; rfl

variable {n : ℕ}
/-- Exact decoding, not fitted coefficients. -/
lemma shift_meter (g : (Fin k→ℝ)→ₗ[ℝ] (Fin n→ℝ)) (b : Buffer F d) (m p : ℕ) (L : Side) (t : ℝ) : let Q := assemble F d s n g
  chart Q (curve (finite Q L m) p t,b)=g (fun i=> sample F d b L m p t (s i)) := by
  dsimp only; refine congrArg g (funext fun i=>congrArg Complex.re ?_)
  unfold decode curve; dsimp only [Prod.snd]; let Q := assemble F d s n g
  simp only [_root_.sum_apply,Finset.sum_apply, Pi.smul_apply]; simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _=>?_ ; simp_rw [Complex.real_smul, mul_left_comm _ (↑(t^a):ℂ), ←Finset.mul_sum]; exact congrArg _ (reconstruct F d (s i) L m a _)
end YM.Pert.Parity
