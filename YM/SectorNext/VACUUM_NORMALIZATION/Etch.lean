import YM.SectorNext.VACUUM_NORMALIZATION.Panel


/-!
# Nonperturbative per-coordinate local windows for a free scalar log-det

Use uniform counting gap in a *geometrically finite-range* precision
table. Mercator series on scaled table (principal REAL log). Does not
bind a sign-changing Hessian of a varying background nor supply the
precision estimates; designed also for comparing paired no-hole and
hole bills. Exponential decay in NUMBER OF WALK STEPS (convert range /
B costs separately). Per-coordinate even summable uniformly on the
true matrices incl periods. Includes exact trace identity; does NOT
majorize the absolute sum of all chain entries or arbitrary derivatives
of log ratios (different purpose). No assumption about order of lattice
keys, so ordinary rectangle plus finite-period metric receipt can use it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.Panel
open RG Precision Matrix Function Unitary
open scoped Matrix.Norms.Frobenius BigOperators Topology ComplexOrder ENNReal Classical

variable {J : Type*} [DecidableEq J] [Fintype J] (A : Matrix J J ℝ)
  (H : A.IsHermitian)

def stencil (L : ℝ) : Matrix J J ℝ := 1 - L⁻¹ • A
def bead (L : ℝ) (k : ℕ) (i : J) := - (stencil A L ^ (k+1)) i i / (k+1:ℝ)
def priceLine (L : ℝ) (i : J) := Real.log L + ∑' k : ℕ, bead A L k i

private lemma spectral_power (L : ℝ) (p : ℕ) : stencil A L ^ p = (H.eigenvectorUnitary).val *
    diagonal (fun i => (1-L⁻¹*H.eigenvalues i)^p) * (H.eigenvectorUnitary).valᴴ := by
  let V := H.eigenvectorUnitary
  let T := conjStarAlgAut ℝ _ V
  have hh : A = T (diagonal fun i => H.eigenvalues i) := H.spectral_theorem
  let d := fun i => 1-L⁻¹*H.eigenvalues i
  have he : stencil A L = T (diagonal d) := by
    unfold stencil
    have ht : diagonal d = (1:Matrix J J ℝ)-L⁻¹ • diagonal H.eigenvalues := by
      ext i j; by_cases h : i=j <;> simp [d,h,diagonal]
    rw [ht,map_sub]; simp only [map_one,map_smul,←hh]
  rw [he,← map_pow, diagonal_pow]; rfl

private lemma row_sq (i : J) : ∑ j, (H.eigenvectorUnitary.val i j)^2 = 1 := by
  let V := H.eigenvectorUnitary
  have h : V.val * V.valᴴ=1 := V.prop.2
  have he := congr_arg (fun Q : Matrix J J ℝ=>Q i i) h
  simpa [Matrix.mul_apply, pow_two,V] using he

private lemma drill (L : ℝ) (p : ℕ) (i : J) : (stencil A L ^ p) i i = ∑ j,(H.eigenvectorUnitary.val i j)^2 * (1-H.eigenvalues j/L)^p := by
  rw [spectral_power A H,Matrix.mul_apply]; apply Finset.sum_congr rfl; intro j _
  rw [Matrix.mul_diagonal,Matrix.conjTranspose_apply,star_trivial]; rw [div_eq_mul_inv]; ring

/-- Band ratio for Mercator, uniform in key/period. -/
def steep (η L : ℝ) := 1-η/L
include H
variable {η L : ℝ}
private theorem fit (f : Numeric A η L) (he : 0 < η) (hL : η ≤ L) (i : J) :
    0 ≤ 1 - H.eigenvalues i / L ∧ 1-H.eigenvalues i/L ≤ steep η L ∧ steep η L<1 := by
  have h := bill_quad H f i; have hl : 0<L := he.trans_le hL
  unfold steep; exact ⟨sub_nonneg.mpr ((div_le_one hl).mpr h.2), sub_le_sub_left (by gcongr; exact h.1) _,
    sub_lt_self _ (div_pos he hl)⟩

theorem line_bounds (f : Numeric A η L) (he : 0<η) (hL : η ≤ L) (k : ℕ) (i : J) :
    bead A L k i ≤ 0 ∧ ‖bead A L k i‖ ≤ steep η L ^ k.succ / k.succ := by
  have hy j := fit A H f he hL j
  have h₁ j : 0≤(1-H.eigenvalues j/L)^(k+1) := pow_nonneg (hy j).1 _
  have h₂ j : (1-H.eigenvalues j/L)^(k+1) ≤ steep η L ^ (k+1) := pow_le_pow_left₀ (hy j).1 (hy j).2.1 _
  have h3 : 0 ≤ (stencil A L ^ (k+1)) i i := by rw [drill A H]; exact Finset.sum_nonneg fun j _=>mul_nonneg (sq_nonneg _) (h₁ j)
  have h4 : (stencil A L ^ (k+1)) i i ≤ steep η L ^ (k+1) := by
    rw [drill A H]
    exact (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (h₂ j) (sq_nonneg (_ : ℝ)))).trans
      (le_of_eq (by rw [← Finset.sum_mul,row_sq A H,one_mul]))
  unfold bead
  have hx : 0 < (k:ℝ)+1 := by positivity
  rw [neg_div]; constructor
  · exact neg_nonpos.mpr (div_nonneg h3 hx.le)
  rw [norm_neg,Real.norm_of_nonneg (div_nonneg h3 hx.le)]; simp only [Nat.cast_succ]
  gcongr

private lemma walk_eigenvalue (f : Numeric A η L) (he : 0<η) (hL : η ≤ L) (j : J) :
    HasSum (fun k : ℕ => (1-H.eigenvalues j/L)^(k+1)/(k+1:ℝ)) (Real.log L - Real.log (H.eigenvalues j)) := by
  obtain ⟨h₁,h₂,h₃⟩ := fit A H f he hL j
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (by rw [abs_of_nonneg h₁]; exact h₂.trans_lt h₃)
  have hl := he.trans_le (bill_quad H f j).1
  rw [show 1-(1-H.eigenvalues j/L) = H.eigenvalues j/L by ring,Real.log_div hl.ne' (he.trans_le hL).ne', neg_sub] at h; exact h

lemma balance (f : Numeric A η L) (he : 0<η) (hL : η ≤ L) (i : J) :
    HasSum (bead A L · i) (∑ j,(H.eigenvectorUnitary.val i j)^2 * Real.log (H.eigenvalues j) - Real.log L) := by
  let v := H.eigenvectorUnitary.val
  have h := hasSum_sum (s:=Finset.univ) (f:=fun j (k : ℕ) => -(v i j ^ 2 * ((1-H.eigenvalues j/L)^(k+1)/(k+1:ℝ))))
    (fun j (_:j∈Finset.univ)=> ((walk_eigenvalue A H f he hL j).mul_left ((v i j)^2)).neg)
  -- API
  convert! h using 1
  · funext k; unfold bead; rw [drill A H,← Finset.sum_neg_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _; unfold v; ring
  have hh := row_sq A H i
  change ∑ j,(v _ _)^2*Real.log _ - _ = ∑ j,_
  simp_rw [mul_sub,neg_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]; unfold v; rw [hh]; ring

private lemma column_sq (i : J) : ∑ j, (H.eigenvectorUnitary.val j i)^2 = 1 := by
  let V := H.eigenvectorUnitary
  have h : V.valᴴ * V.val=1 := V.prop.1
  have he := congr_arg (fun Q : Matrix J J ℝ=>Q i i) h
  simpa [Matrix.mul_apply, pow_two,V] using he

theorem log_form (f : Numeric A η L) (he : 0<η) (hL : η≤L) : Real.log A.det = ∑ i : J,priceLine A L i := by
  unfold priceLine
  simp_rw [(balance A H f he hL _).tsum_eq, show ∀ x : ℝ,Real.log L+(x-Real.log L)=x from fun x=>by ring]
  rw [H.det_eq_prod_eigenvalues]; change Real.log (∏ i,H.eigenvalues i)= _
  rw [Real.log_prod (fun i _=>(he.trans_le (bill_quad H f i).1).ne'),Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_mul,column_sq A H,one_mul]


/-- Local approximant. No logs of possibly nonsymmetric clipped
restrictions; only finite entries actually read plus log of positive
common L. Per-coordinate extensive terms include pre- *and* post-pair
matches. -/
def headLine (A : Matrix J J ℝ) (L : ℝ) (q : ℕ) (i : J) := Real.log L + ∑ k∈Finset.range q, bead A L k i

def mist (η L : ℝ) (q : ℕ) := steep η L ^ q * (1-steep η L)⁻¹

lemma faith (f : Numeric A η L) (he : 0<η) (hL : η ≤ L) (q : ℕ) (i : J) :
    |priceLine A L i-headLine A L q i| ≤ mist η L q := by
  let u := fun k => bead A L k i
  let x := steep η L
  have hh : 0≤x := by unfold x steep; rw [sub_nonneg]; exact (div_le_one (he.trans_le hL)).mpr hL
  have ht : x<1 := by unfold x steep; exact sub_lt_self _ (div_pos he (he.trans_le hL))
  have hu (k : ℕ) : ‖u k‖ ≤ x^k := (line_bounds A H f he hL k i).2.trans
    (le_trans (div_le_self (by unfold x at hh; positivity) (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k)))) (by
      rw [pow_succ]; change _ ≤ x^k
      exact mul_le_of_le_one_right (pow_nonneg hh k) ht.le))
  have hk (k : ℕ) : ‖u (k+q)‖ ≤ x^k*x^q := (hu _).trans_eq (pow_add ..)
  have hw := (hasSum_geometric_of_lt_one hh ht).mul_right (x^q)
  have hc := hw.summable.of_nonneg_of_le (fun i=>norm_nonneg _) hk
  have hsum := ((balance A H f he hL i).summable.sum_add_tsum_nat_add q)
  unfold priceLine headLine
  change |Real.log L+∑' k,u k-(Real.log L+∑ k∈Finset.range q,u k)| ≤ _
  -- parentheses of tsum
  rw [add_sub_add_left_eq_sub]; rw [←hsum,add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hc).trans ((hc.tsum_le_tsum hk hw.summable).trans_eq (hw.tsum_eq.trans (mul_comm ..)))

omit H [Fintype J] [DecidableEq J] in
lemma steams (he : 0<η) (hL : η ≤ L) : Filter.Tendsto (mist η L) Filter.atTop (nhds 0) := by
  let x := steep η L
  have hh : 0≤x := by unfold x steep; rw [sub_nonneg]; exact (div_le_one (he.trans_le hL)).mpr hL
  have ht : x<1 := by unfold x steep; exact sub_lt_self _ (div_pos he (he.trans_le hL))
  unfold mist; simpa only [zero_mul,x] using (tendsto_pow_atTop_nhds_zero_of_lt_one hh ht).mul_const (1-x)⁻¹

variable {T : Type*} (site : J → T) (δ : T → T → ℕ)

omit H in
private lemma blink {A B : Matrix J J ℝ} {x : T} {M R : ℕ} {η : ℝ}
    (hs : ∀ i j, M < δ (site i) (site j) → A i j = 0)
    (ht : ∀ i j, δ x (site i) ≤ R → A i j = B i j)
    (hr : ∀ a b c, δ a c ≤ δ a b+δ b c) (hz : ∀ a,δ a a=0) (p : ℕ) (i j : J) (he : δ x (site i)+p*M ≤ R) :
    (stencil A η^p) i j = (stencil B η^p) i j := by
  induction p generalizing i with
  | zero => rw [pow_zero,pow_zero]
  | succ k ih =>
    rw [pow_succ',pow_succ',Matrix.mul_apply,Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hh : δ x (site i) ≤ R := Nat.le_trans (Nat.le_add_right ..) he
    have hf : stencil A η i b = stencil B η i b := by simp only [stencil,Matrix.sub_apply, Matrix.smul_apply,ht _ _ hh]
    by_cases hv : δ (site i) (site b) ≤ M
    · rw [hf,ih _ (by
        have H := hr x (site i) (site b)
        calc
          _ ≤ δ x (site i)+δ (site i) (site b)+k*M := Nat.add_le_add_right H _
          _ ≤ R := le_trans (by gcongr : δ x _ + δ _ _+k*M ≤ δ x (site i)+M+k*M) (by rw [Nat.succ_mul] at he; omega))]
    rw [←hf]; have hb : stencil A η i b = 0 := by
      have hl : i ≠ b := by intro hi; subst b; exact hv (by simp [hz])
      simp [stencil,hl,hs _ _ (lt_of_not_ge hv)]
    simp [hb]

omit H in
lemma head_local {A B : Matrix J J ℝ} {M : ℕ} (q : ℕ) (i : J)
    (hs : ∀ i j, M < δ (site i) (site j) → A i j = 0)
    (ht : ∀ k j, δ (site i) (site k) ≤ q*M → A k j=B k j)
    (hr : ∀ a b c, δ a c ≤ δ a b+δ b c) (hz : ∀ a,δ a a=0) : headLine A L q i = headLine B L q i := by
  unfold headLine; congr 1; apply Finset.sum_congr rfl; intro j hj
  unfold bead; rw [blink site δ hs ht hr hz (j+1) i i ?_]; rw [hz,zero_add]; exact Nat.mul_le_mul_right _ (Finset.mem_range.mp hj)

omit H in
/-- A genuine log-det locality estimate. Entry radius M in native
geometry (periodic or arbitrary with triangle etc.), identical rows
through q hops. Close the determinant trace on any pair of actual
positive tables satisfying that gap & upper bound. On a field/tag family
use to charge even the absolute changes of per-anchor scalar terms,
without a V/log coefficient claim on the Bloch symbol divisor.
-/
theorem paired {A B : Matrix J J ℝ} (ha : A.IsHermitian) (hb : B.IsHermitian) (fA : Numeric A η L) (fB : Numeric B η L)
    (he : 0<η) (hL : η ≤ L) {M : ℕ} (q : ℕ) (i : J)
    (hs : ∀ i j,M < δ (site i) (site j) → A i j=0)
    (ht : ∀ k j,δ (site i) (site k) ≤ q*M → A k j=B k j)
    (hr : ∀ a b c,δ a c ≤ δ a b+δ b c) (hz : ∀ a,δ a a=0) :
    |priceLine A L i-priceLine B L i| ≤ 2*mist η L q := by
  have hh := head_local (L:=L) site δ q i hs ht hr hz
  apply le_trans (abs_sub_le (priceLine A L i) (headLine A L q i) (priceLine B L i))
  nth_rw 2 [hh]; rw [abs_sub_comm (headLine _ _ _ _)]
  exact (add_le_add (faith A ha fA he hL q i) (faith B hb fB he hL q i)).trans_eq (by ring)

end YM.SectorNext.Vacuum.Panel
