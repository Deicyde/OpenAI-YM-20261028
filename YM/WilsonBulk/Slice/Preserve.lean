import YM.WilsonBulk.Slice.Morph

/-!
# Exact linear/affine and spectator-dependent transform commutes with heat

Hybrid Wick push across different presentations (Γ singular spectator).
Real statement over HELD parameters, no positivity or unintegration needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical BigOperators
open PowerSeries Function Finset Filter
variable {A X : Type} {α β ι : Type} [CommRing A] [Algebra ℝ A]
variable [Fintype α] [Fintype β]
variable {G : Page α 2} {H : Page β 2} (V : α→Tape β)
-- tangent directions in affine covariance support target
structure Reflects (T : α→ β → ℝ) (G : Page α 2) (H : Page β 2) : Prop where
  underlies (x y : β) (h : H (two x y)≠0) :
    (∀ i : α,player x (V i)=algebraMap ℝ (Tape β) (T i x)) ∧ ∀ i : α,player y (V i)=algebraMap ℝ (Tape β) (T i y)
  projects (i j : α) : ∑ x:β,∑ y:β, H (two x y)*T i x*T j y=G (two i j)
variable {T : α→β→ℝ}
omit [Fintype β] in
lemma Reflects.tangent (x : β) (hv : ∀ i : α, player x (V i)=algebraMap ℝ (Tape β) (T i x)) (p : Tape α) :
    player x (submit V p)=∑ i:α,T i x • submit V (player i p) := by rw [player_chain]; exact sum_congr rfl fun i _=> by rw [hv,Algebra.smul_def,mul_comm]
section
omit [Fintype β] -- line above β unused (fix)
omit [Fintype α] in
lemma parallel_pow {B : Tape α →ₗ[ℝ]Tape α} {T : Formula α→ₗ[ℝ]Formula α} (h : B=parallel T) (n : ℕ) : B^n = parallel (T^n) := by
  subst B; induction n with
  | zero=> ext1 p; ext1 i; simp [coeff_parallel]
  | succ n ih=> ext1 p; ext1 i; rw [pow_succ',pow_succ']; simp [Module.End.mul_apply,ih,coeff_parallel]
lemma lap_full (p : Tape α) : parallel (laplace G) p =∑ i:α,∑ j:α, (G (two i j)/2) • player j (player i p) := by ext1 k; simp only [player,coeff_parallel,map_sum,parallel_D,coeff_smul,laplace_eval]
lemma around_rect {ι κ μ ν B : Type} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν] [AddCommMonoid B] (p : ι→κ→μ→ν→B) :
   ∑ i:ι,∑ j:κ,∑ k:μ,∑ l:ν,p i j k l=∑ k:μ,∑ l:ν,∑ i:ι,∑ j:κ,p i j k l := by
     conv_lhs => arg 2; intro i; rw [permute_three]
     rw [permute_three]
end
lemma Reflects.heat (h : Reflects V T G H) (p : Tape α) : parallel (laplace H) (submit V p)=submit V (parallel (laplace G) p) := by
  rw [lap_full,lap_full]; simp only [map_sum,map_smul]
  let c x y i j : ℝ:= H (two x y)/2 * T i x * T j y
  have he (i j) : ∑ x:β,∑ y:β,c x y i j =G (two i j)/2 := by
    rw [← h.projects, sum_div]; simp_rw [sum_div]; refine sum_congr rfl fun x _=>sum_congr rfl fun y _=>?_; unfold c; ring
  simp_rw [← he, Finset.sum_smul]
  rw [around_rect]; refine sum_congr rfl fun x _=>sum_congr rfl fun y _=>?_
  by_cases heq : H (two x y)=0; · simp only [c, heq,zero_div,zero_smul,zero_mul,sum_const_zero]
  obtain ⟨hx,hy⟩:= h.underlies x y heq
  rw [tangent V x hx p,map_sum]; simp_rw [Derivation.map_smul, tangent V y hy, Finset.smul_sum, smul_smul]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_; unfold c; rw [mul_assoc]
omit [Fintype β] in
lemma wick_count (i : ℕ) (p : Tape α) :
    ∀ᶠ n:ℕ in atTop, Steps i (parallel (wick G) p) (∑ k∈range n,(k.factorial:ℝ)⁻¹ • ((parallel (laplace G)) ^ k) p) := by
  -- doesn't require absolute bounds on number of terms (volume-specific)
  let f j := (coeff j p)
  have hu (j : ℕ) : ∀ᶠ n:ℕ in atTop, (f j).totalDegree < n:= eventually_gt_atTop _
  filter_upwards [((Finset.eventually_all (range i)).mpr fun j _=>hu j)] with n hn
  intro j hj; simp only [map_sum,coeff_parallel,coeff_smul,parallel_pow (T:=laplace G) rfl]
  have hk : (coeff j p).totalDegree<n := hn _ (mem_range.mpr hj)
  -- exact stabilization
  rw [wick_read]; unfold timeRead; simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial,rayc,ray,one_pow,mul_one]; apply sum_subset (range_mono hk) (fun a _ ha=>?_); rw [lap_finite G (by rw [mem_range] at ha; omega),smul_zero]
lemma Reflects.all (h : Reflects V T G H) (p : Tape α) : parallel (wick H) (submit V p)=submit V (parallel (wick G) p) := by
  have he (n : ℕ) : ((parallel (laplace H))^n) (submit V p)=submit V (((parallel (laplace G))^n) p) := by induction n with
    | zero=> simp
    | succ n ih=> rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih,h.heat V]
  ext1 j
  obtain ⟨n,h₁,h₂⟩:=(Filter.Eventually.and (wick_count (G:=H) (j+1) (submit V p)) (wick_count (G:=G) (j+1) p)).exists; exact h₁ j (by omega)|>.trans ((by simp only [map_sum,map_smul,he] : coeff j (∑ k∈range n,(k.factorial:ℝ)⁻¹ • ((parallel (laplace H)) ^ k) (submit V p))= coeff j (submit V (∑ k∈range n,(k.factorial:ℝ)⁻¹ • ((parallel (laplace G)) ^ k) p))).trans (((Steps.push (submit V) (by rw [submit_X,constantCoeff_X]) h₂) j (by omega)).symm))
end YM.WilsonBulk.Sheet
