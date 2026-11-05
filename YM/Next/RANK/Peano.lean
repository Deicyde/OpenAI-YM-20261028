import Mathlib.Analysis.Calculus.Taylor
import YM.Next.RANK.Ray
import YM.Next.RANK.SpectrumReal

/-! # Finite degree ray values even without function-space differentiability across masks -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Finset Asymptotics Filter Metric Set Normal Rise MvPolynomial
open scoped Topology BigOperators ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Dims (n : ℕ) (t : ℕ → E) (x : ℝ) := ∑ i∈Finset.range (n+1), x^i • t i
abbrev asym (n : ℕ) (F : ℝ → E) := F =o[𝓝 0] (fun t : ℝ => t^n)

def peano (F : ℝ → E) (t : ℕ→ E) (n : ℕ) := asym n (F-Dims n t)

lemma taylor_data {f : ℝ → E} {n : ℕ} (hf : ContDiffAt ℝ n f 0) : peano f (fun i => (i.factorial:ℝ)⁻¹ • iteratedDeriv i f 0) n := by
  obtain ⟨r,hr,h⟩ := Metric.mem_nhds_iff.mp (hf.eventually (by simp))
  let B:=Metric.ball (0:ℝ) r
  have ho : IsOpen B := Metric.isOpen_ball
  have hv : (0:ℝ)∈ B := Metric.mem_ball_self hr
  have ht := taylor_isLittleO (convex_ball (0:ℝ) r) hv (show ContDiffOn ℝ n f B from fun i hi => (show ContDiffAt ℝ n f i from h hi).contDiffWithinAt)
  rw [isOpen_ball.nhdsWithin_eq hv] at ht
  simp_rw [sub_zero] at ht
  apply ht.congr_left; intro i; simp only [taylor_within_apply,sub_zero, Dims, Pi.sub_apply]; congr 1
  apply sum_congr rfl; intro j hj; have hi := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [smul_smul,mul_comm _ ((j.factorial:ℝ))⁻¹,iteratedDerivWithin_eq_iteratedDeriv ho.uniqueDiffOn (hf.of_le (by exact_mod_cast hi)) hv]
lemma depth {n : ℕ} {A B : ℝ → E} (h : ContDiffAt ℝ n A 0) (ht : ContDiffAt ℝ n B 0) (he : ∀ i, i≤n → iteratedDeriv i A 0=iteratedDeriv i B 0) : asym n (A-B) := by
  let E:= Dims n (fun i => (i.factorial:ℝ)⁻¹ • iteratedDeriv i A 0)
  have h₁ := taylor_data h; have h₂ := taylor_data ht; have hp : asym n (B-E) := by
    have he : E=Dims n (fun i => (i.factorial:ℝ)⁻¹ • iteratedDeriv i B 0) := by
      funext v; refine sum_congr rfl fun i hi => ?_; dsimp only; rw [he i (Nat.le_of_lt_succ (mem_range.mp hi))]
    rw [he]; exact h₂
  change asym n (A-E) at h₁; exact (h₁.sub hp).congr_left fun x => by simp [sub_sub_sub_cancel_right]
omit [NormedSpace ℝ E] in
lemma knock {n m : ℕ} {v : ℝ → E} (h : n≤m) (hv : asym m v) : asym n v := (eq_or_lt_of_le h).elim (fun h => h ▸ hv) (fun h => hv.trans (isLittleO_pow_pow h))
omit [NormedSpace ℝ E] in
lemma error_power {n : ℕ} {v : ℝ → E} (c) (h : ∀ᶠ s in 𝓝 (0:ℝ), ‖v s‖ ≤ c * ‖s‖^(n+1)) : asym n v :=
    (show v=O[𝓝 0] fun s : ℝ => s^(n+1) from (isBigO_iff ..).2 ⟨c, by simp_rw [norm_pow]; exact h⟩).trans_isLittleO (isLittleO_pow_pow (Nat.lt_succ_self n))

lemma retreat {f : ℕ → E} (n : ℕ) (he : asym n (Dims n f)) : ∀ i, i ≤ n → f i=0 := by
  classical
  induction n with
  | zero =>
    have ho : asym 0 (Dims 0 f):=he
    change (fun x : ℝ=> _) =o[𝓝 0] _ at he
    simp only [Dims,zero_add,sum_range_one,pow_zero,one_smul] at he
    have ht : Tendsto (fun _ : ℝ => f 0) (𝓝 0) (𝓝 0) := isLittleO_one_iff ℝ |>.mp he
    intro i hi; have hv := Nat.eq_zero_of_le_zero hi; rw [hv]; exact tendsto_nhds_unique tendsto_const_nhds ht
  | succ n H =>
    let u:= f (n+1)
    let A (t : ℝ) := t^(n+1) • u
    have hx : Dims (n+1) f= Dims n f+A := funext fun t => by rw [Dims,sum_range_succ]; rfl
    have hv : asym n A := (show A=O[𝓝 0] fun t : ℝ => t^(n+1) from isBigO_iff.mpr ⟨‖u‖,Eventually.of_forall fun x => by dsimp only [A]; rw [norm_smul, mul_comm]⟩).trans_isLittleO (isLittleO_pow_pow (Nat.lt_succ_self _))
    have ht : asym n (Dims n f) := by
      have he := (knock (Nat.le_succ _) he).sub hv; rw [hx] at he; simp only [Pi.add_apply,add_sub_cancel_right] at he; exact he
    have hi := H ht
    rw [hx, show Dims n f=0 from funext fun t => sum_eq_zero fun i h => by rw [hi i (Nat.le_of_lt_succ (mem_range.mp h)),smul_zero],zero_add] at he
    have hz : u=0 := by
      by_contra hh
      have hf := norm_pos_iff.mpr hh; obtain ⟨x,hv,hx⟩ := ((he.def (half_pos hf) |>.filter_mono
        (show (𝓝[>] (0:ℝ)) ≤ _ from nhdsWithin_le_nhds)).and (self_mem_nhdsWithin (α:=ℝ))).exists
      unfold A at hv; change 0<x at hx; rw [norm_smul] at hv; have hx' : 0<‖x^(n+1)‖ := norm_pos_iff.mpr (pow_ne_zero _ hx.ne'); nlinarith only [hv,mul_pos hf hx']
    intro i h; by_cases hm : i=n+1
    · rw [hm]; exact hz
    exact hi i (by omega)

lemma dims_sub {n} (f g : ℕ→ E) : Dims n (f-g)=Dims n f-Dims n g := by
  funext x; simp only [Dims,Pi.sub_apply,← sum_sub_distrib, smul_sub]

-- cardinal-independent formulas for totals along a ray. also weighted powers in `stampHeight`.
def rays (w : V→ℕ) (x : V→ℂ) (h : ℝ) : V→ℂ := fun i => (h:ℂ)^(w i)*x i

lemma told (w : V→ℕ) (x : V→ℂ) (h : ℝ) (i : V →₀ ℕ) (a : ℂ) : aeval (rays w x h) (monomial i a)=h^(Finsupp.weight w i) • aeval x (monomial i a) := by
  unfold rays; rw [aeval_monomial,aeval_monomial]
  simp_rw [Finsupp.prod,mul_pow,Finset.prod_mul_distrib,← pow_mul,prod_pow_eq_pow_sum]
  rw [Complex.real_smul,Complex.ofReal_pow]
  have hp : Finsupp.weight w i=∑ j∈i.support,w j * i j := by
    rw [Finsupp.weight_apply]; unfold Finsupp.sum; simp_rw [smul_eq_mul, mul_comm]
  rw [hp]; ring

def sound (w : V→ℕ) (P : poly V) (x : V→ℂ) : ℕ→ℂ := fun i => ∑ j∈P.support,if Finsupp.weight w j=i then aeval x (monomial j (coeff j P)) else 0

lemma toller (w : V→ℕ) (P : poly V) (x) (n : ℕ) (h : ∀ i ∈ P.support,Finsupp.weight w i ≤ n) : (fun t : ℝ => aeval (rays w x t) P) = Dims n (sound w P x) := by
  classical
  funext t; unfold Dims sound
  simp_rw [Finset.smul_sum]; rw [sum_comm]; nth_rw 1 [MvPolynomial.as_sum P]
  rw [map_sum]; apply sum_congr rfl; intro i hi; rw [told]; simp only [smul_ite,smul_zero,sum_ite_eq,mem_range.mpr (Nat.lt_succ_of_le (h i hi)),↓reduceIte]
lemma verse (P : poly V) (x : V→ ℝ) (n : ℕ) (h : P.totalDegree≤n) : ∃ f : ℕ→ℂ, (fun t : ℝ => text (fun i=>t*x i) P)=Dims n f := by
  let w (_:V):=1
  let g i:ℂ:= x i
  refine ⟨sound w P g,?_⟩
  rw [← toller w P g n ?_]; rotate_left
  · exact fun i hi => by simpa [Finsupp.weight_apply,Finsupp.sum,totalDegree,w] using (MvPolynomial.le_totalDegree hi).trans h
  have ht (t : ℝ) : (fun i:V => (↑(t*x i):ℂ))=rays w g t := by funext i; simp only [rays,w,pow_one,Complex.ofReal_mul]; rfl
  simp only [text,ht]

lemma decipher (n : ℕ) (P Q : ℝ→ℂ) (h : ∃ f,P=Dims n f) (he : ∃ g,Q=Dims n g) (ha : asym n (P-Q)) : P=Q := by
  obtain ⟨f,rfl⟩ := h; obtain ⟨g,rfl⟩ := he; rw [← dims_sub] at ha
  have hv := retreat n ha; funext t; apply sum_congr rfl; intro i hi
  rw [show f i=g i from sub_eq_zero.mp (hv i (Nat.le_of_lt_succ (mem_range.mp hi)))]

end YM.Next.Rank.Spindle
