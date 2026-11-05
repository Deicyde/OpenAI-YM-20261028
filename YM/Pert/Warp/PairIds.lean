import YM.Pert.Warp.Diagonal
import YM.Analysis.Symmetric
/-! Polarization to symmetrically averaged Stein pair removals. Support for complex *bilinear* covariance, finite without nondegeneracy. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Pert.Warp
open Function Filter Set MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsGaussian μ]
variable {K : Type*} [RCLike K]
local notation "C" => E → K
lemma price_tame {p : E→K} (h : Orb.Tame p) : Integrable p μ := by
  obtain ⟨c,_,k,hc⟩ := h.2
  have hi : Integrable (fun x : E => (1+‖x‖)^k) μ := by
    by_cases hk : k=0; · simp [hk]
    have hd := ((IsGaussian.memLp_id μ k (by simp)).norm.add (memLp_const (1:ℝ))).integrable_norm_pow hk
    convert! hd using 2; simp only [Pi.add_apply,id_eq, Real.norm_eq_abs]; rw [abs_of_nonneg (by positivity),add_comm]
  exact (hi.const_mul c).mono' h.1.aestronglyMeasurable (Eventually.of_forall hc)
variable {I J V : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
lemma prod_tame {s : Finset I} {p : I → E→K} (hp : ∀ i∈s,Orb.Tame (p i)) : Orb.Tame (fun a=>∏ i∈s,p i a) := by
  induction s using Finset.induction_on with
  | empty=> exact Orb.Tame.constant (1:K)
  | insert i s h ih=> simp only [Finset.prod_insert h]; apply (hp i (Finset.mem_insert_self ..)).mul (ih fun j hj=> hp j (Finset.mem_insert_of_mem hj))
omit [Fintype I] [DecidableEq I] in
lemma sum_tame {s : Finset I} {p : I→E→K} (hp : ∀ i∈s,Orb.Tame (p i)) : Orb.Tame (fun a=>∑ i∈s,p i a) := by
  simp_rw [show (fun a=>∑ i∈s,p i a) = ∑ i∈s,p i by funext a; simp only [Finset.sum_apply]]; exact Orb.Tame.sum hp

def fake (T : Finset I) (p : I → V → K) (x y : V) := ∏ i, p i (if i ∈ T then x else y)
def scan (T : Finset I) (p : I → E → K) := ∫ x, (∫ y, fake T p x y ∂μ) ∂μ
def kick (T : Finset I) (p : I → E → K) := ∫ x, (∏ i∈T,p i x) ∂μ
def price (p : I → E → K) := kick μ Finset.univ p
lemma fake_exact (T : Finset I) (p : I→V→K) (x y : V) : fake T p x y = (∏ i∈T,p i x)*(∏ i∈Tᶜ,p i y) := by
  unfold fake; rw [←Finset.union_compl T ,Finset.prod_union disjoint_compl_right]
  · congr 1
    exact Finset.prod_congr rfl fun i hi=> (by rw [if_pos hi])
    exact Finset.prod_congr rfl fun i hi=> (by rw [if_neg (Finset.mem_compl.mp hi)])
lemma scan_exact (T : Finset I) (p : I→E→K) : scan μ T p=kick μ T p * kick μ Tᶜ p := by simp only [scan,kick,fake_exact,integral_mul_const,integral_const_mul]

def charge (F : J→V→K) (z : I→J→K) (i : I) (x : V) : K := ∑ a:J,z i a *F a x

def tab (T : Finset I) (F : J→E→K) (f : I→J) (z : I→J→K) := scan μ T (F ∘ f) * (∏ i,z i (f i))
lemma scan_tab (T : Finset I) (F : J→E→K) (z : I→J→K) (hF : ∀ j, Orb.Tame (F j)): scan μ T (charge F z)= ∑ f:I→J, tab μ T F f z := by
  let P (f : I→J) := ∏ i, z i (f i)
  let A (x y : E) (f : I→J) := P f * fake T (F ∘ f) x y
  have e (x y : E) : fake T (charge F z) x y = ∑ f:I→J,A x y f := Fintype.prod_sum _ |>.trans (Finset.sum_congr rfl fun f _ => Finset.prod_mul_distrib ..)
  unfold scan; simp_rw [e]
  have he (x : E) : (∫ y,(∑ f:I→J,A x y f) ∂μ) = ∑ f:I→J, P f*(∫ y, fake T (F ∘ f) x y ∂μ) := by
    rw [integral_finsetSum]
    · simp only [A, integral_const_mul]
    · intro f _; apply price_tame
      have ht (i) : Orb.Tame (fun y=>F (f i) (if i∈T then x else y)) := by
        by_cases h : i∈T; · simp [h]; exact Orb.Tame.constant _
        simp [h];exact hF _
      exact Orb.Tame.mul (Orb.Tame.constant _) (prod_tame (fun i (_ : i∈Finset.univ) => ht i))
  simp_rw [he]; rw [integral_finsetSum]
  · apply Finset.sum_congr rfl; intro f _; unfold tab scan;rw [integral_const_mul,mul_comm]
  · intro f _; apply Integrable.const_mul
    simp_rw [fake_exact,integral_const_mul]
    apply price_tame
    exact Orb.Tame.mul (prod_tame (fun i _=>hF (f i))) (Orb.Tame.constant _)
end YM.Pert.Warp
