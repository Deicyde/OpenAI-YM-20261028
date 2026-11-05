import YM.Next.RANK.Bird
import YM.Next.RANK.Instructions


/-!
# Wick projector before choosing origins

Budget certificate uses *untransported* ordinary source poly on k curvature.
Must still obtain it together with the actual P(W) application W transfer, using
any truncation windows with remainders and updated inventory. Show calibration
via a germ test representing nonlinear transported-variable reading (need ask
this at unweighted amplitude `g`; factor weights then compare). The nonlinear
defect only contributes above degree-one in SCALARS, not engineering grade.
No assuming Price.Tested. Require invariant and star separately below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.LiftMark
open Labels Lattice Wilson RG Normal  Perch Beamer Configuration  Rise Filter MvPolynomial Set Tariffs
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {F : Family G} {k N p d n : ℕ}

section
-- algebra of costs
variable {V Z : Type*}

def first (f : V → Z→₀ ℂ) (i : V) := exchange f (X i)
def garnish (A : V→Normal.poly Z) (f : V→ Z→₀ ℂ) (t : ℝ) : Normal.poly V →ₐ[ℂ] Normal.poly Z :=
    MvPolynomial.aeval fun i => (t:ℂ)⁻¹ • (factors (t:ℂ) (A i+first f i))

def Diet (f : V → Z→₀ ℂ) (A : V→Normal.poly Z) (C : ℝ) := ∀ i,
    coin (first f i)≤C ∧ coin (A i)≤ C ∧ ∀ j∈(A i).support, 2 ≤ Finsupp.weight (fun _ : Z => 1) j

lemma sprinkle (f : V → Z→₀ ℂ) (P : Normal.poly V) (a : ℂ) : factors a (exchange f P)=exchange f (factors a P) := by
  apply DFunLike.congr_fun (f:= (factors a).comp (exchange f)) (g:= (exchange f).comp (factors a))
  ext1 i; rw [AlgHom.comp_apply,AlgHom.comp_apply,exchange_x, factors_X,map_mul (exchange f),exchange_x,exchange_c]; simp only [glyph,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,factors_X]
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => (mul_smul_comm ..).symm
lemma alter (x : ℂ) (f : V → Z→₀ ℂ) (i : V) : factors x (first f i) = x • first f i := by
  simp only [first, sprinkle,factors_X, C_mul',map_smul]

lemma zips (A : V→Normal.poly Z) (f : V→ Z→₀ ℂ) (i : V) (t : ℝ) (ht : 0<t) :
    garnish A f t (X i)=first f i+ (t:ℂ)⁻¹ • factors (t:ℂ) (A i) := by
  unfold garnish; rw [aeval_X, map_add, alter, smul_add,smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht.ne'), one_smul]; abel

lemma west (f : V → Z→₀ ℂ) (A : V→Normal.poly Z) {t C : ℝ} (ht : 0<t) (he : t ≤ 1) (hc : 1 ≤ C) (h : Diet f A C)
    (i : V) :
    coin (garnish A f t (X i)) ≤ 2*C ∧ coin (garnish A f t (X i)-exchange f (X i)) ≤ t*C := by
  let x:= (t:ℂ)⁻¹ • factors (t:ℂ) (A i)
  have hx : coin x ≤ t*C := by
    unfold x; apply (peak_cost 1 _ _ _ zero_le_one).trans
    rw [norm_inv,Complex.norm_real, Real.norm_of_nonneg ht.le]
    apply (mul_le_mul_of_nonneg_left ((scalar_bound (A i) ht.le he (h i).2.2).trans
      (mul_le_mul_of_nonneg_left (h i).2.1 (pow_nonneg ht.le _))) (inv_pos.mpr ht).le).trans_eq; field_simp
  rw [zips _ _ _ _ ht, ← first]; refine ⟨(taller _ zero_le_one ..).trans ?_,?_⟩
  · apply (add_le_add (h i).1 hx).trans; linarith only [mul_le_mul_of_nonneg_right he (zero_le_one.trans hc)]
  rw [add_comm, add_sub_cancel_right]; exact hx

-- reduce output to pin costs

def annuity (t c e : ℝ) (n : ℕ) := n*(t*c)*(2*c)^n + e*(2*((n:ℝ)+2))^n * c^n

private lemma bearer (p q : Normal.poly V) : (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg, show -q=(-1:ℂ) • q by simp]; exact (totalDegree_add ..).trans (max_le_max le_rfl (totalDegree_smul_le ..))

lemma stock (t B ε : ℝ) {P : Normal.poly V} {K : Normal.Symmetric V}
    (f : V → Z→₀ ℂ) (A : V→Normal.poly Z) (ht : 0<t) (he : t ≤ 1) (hc : 1 ≤ B) (h : Diet f A B) (hp : P.totalDegree ≤ n)
    (hb : 0≤ ε) (hv : ε ≤ 1) (H : ∀ i j, ‖K.cov i j‖ ≤ ε) :
    totalDegree (milk K P) ≤ n ∧ coin (garnish A f t P - exchange f (milk K P)) ≤ coin P * annuity t B ε n := by
  have hh := bounds K n ε H hb hv P hp
  let F:= exchange f
  have hz (i) : cents (glyph (f i)) 0 1 ≤ B := by simpa only [first,Normal.exchange_x] using (h i).1
  have he' : coin (milk K P-P) ≤ _ := hh.1
  have hw : coin (F P-F (milk K P)) ≤ coin P * (ε*(2*(n+2))^n) * B^n := by
    rw [← map_sub]
    apply (rise _ _ zero_le_one hc hz _ ((bearer P (milk K P)).trans (max_le hp hh.2))).trans
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (zero_le_one.trans hc) n)
    rw [show P-milk K P= (-1:ℂ) • (milk K P-P) by simp]; refine le_trans (peak_cost 1 _ _ _ zero_le_one) ?_; simpa only [norm_neg,norm_one,one_mul] using! he'
  let q:= garnish A f t P; let s:= F (milk K P)
  change _ ∧ coin (q-s) ≤ _
  have hu := zero_le_one.trans hc
  have hs : coin (q-F P) ≤ coin P * (n*(t*B)*(2*B)^n) := message (garnish A f t) F _ _ (by linarith) (mul_nonneg ht.le hu)
    (fun i => (west f A ht he hc h i).1) (fun i => (h i).1.trans (by linarith)) (fun i => (west f A ht he hc h i).2) P hp
  rw [show q-s=(q-F P)+(F P-s) by abel]; exact ⟨hh.2,(Rise.taller _ zero_le_one ..).trans ((add_le_add hs hw).trans_eq (by unfold annuity; ring))⟩
end
end YM.Next.Rank.LiftMark
