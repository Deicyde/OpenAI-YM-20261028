import YM.Extra.FREE_DETECTOR_ALGEBRA.PositiveLeg
import YM.Extra.FREE_DETECTOR_ALGEBRA.Symbol

set_option warningAsError false

/-! Finite ordering scripts and reflection for two point tests. -/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Maxwell Wick Pair Tensor Analysis
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {j n m : ℕ} {x y : E4}

def code (G : Gauge) (n : ℕ) : ProbeTower G n →ₗ[ℝ] WickPol G where
  toFun p := ∑ i : Fin n, digit (p i)
  map_add' p q := by
    change (∑ i : Fin n, digit (p i + q i))= _
    simp_rw [digit_add,Finset.sum_add_distrib]
  map_smul' t p := by
    change (∑ i : Fin n, digit (t • p i))= _
    simp_rw [digit_smul,← Finset.smul_sum]; exact IsScalarTower.algebraMap_smul (R:=ℝ) (M:=WickPol G) ℂ _ _

def encode {ι : Type*} (b : ι → ProbeTower G n) : MvPolynomial ι ℂ →ₐ[ℂ] WickPol G := MvPolynomial.aeval fun i => code G n (b i)

@[simp] lemma encode_X {ι : Type*} (b : ι → ProbeTower G n) (i : ι) : encode b (MvPolynomial.X i) = code G n (b i) := MvPolynomial.aeval_X ..

lemma digit_zero (j : ℕ) : digit (0 : Sol G.Color j) = 0 := by apply equalPol; intro A; rw [digit_read]; simp

lemma code_origin (i : Fin n) (p : Sol G.Color i.val) : code G n (originLeg G i p) = digit p := by
  change ∑ j : Fin n, digit (originLeg G i p j)= _
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · unfold originLeg; simp
  intro j _ hj; unfold originLeg; simp [Pi.single_eq_of_ne hj,digit_zero]

lemma from_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (ProbeTower G n)) (p : ProbeTower G n) :
    ∃ q : MvPolynomial ι ℂ, encode (⇑b) q = code G n p := by
  classical
  refine ⟨∑ i : ι, (((b.repr p i):ℝ):ℂ) • MvPolynomial.X i,?_⟩
  rw [_root_.map_sum]
  conv_rhs => rw [← b.sum_repr p]
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [_root_.map_smul,_root_.map_smul,encode_X]
  exact IsScalarTower.algebraMap_smul (R:=ℝ) (M:=WickPol G) ℂ _ _

/-- No basis has to be fixed before choosing the truncation! Includes
complex labels, length mixtures, and the zero-color case. Finite-basis
consumer will use the proposition with explicit Fin. -/
theorem from_large (p : WickPol G) : ∃ n : ℕ, ∀ m ≥ n, ∀ N : ℕ, ∀ b : Module.Basis (Fin N) ℝ (ProbeTower G m),
    ∃ q : MvPolynomial (Fin N) ℂ, encode (⇑b) q=p := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0,fun m _ _ b => ⟨MvPolynomial.C c,MvPolynomial.aeval_C ..⟩⟩
  | add p q hp hq =>
    obtain ⟨n,hn⟩ := hp; obtain ⟨l,hl⟩ := hq
    refine ⟨max n l,fun m hm N b => ?_⟩
    obtain ⟨p',rfl⟩ := hn m (le_trans (le_max_left ..) hm) N b
    obtain ⟨q',rfl⟩ := hl m (le_trans (le_max_right ..) hm) N b
    exact ⟨p'+q',_root_.map_add ..⟩
  | mul_X p i hp =>
    obtain ⟨n,hn⟩ := hp
    refine ⟨max n (i.1+1),fun m hm N b => ?_⟩
    obtain ⟨p',rfl⟩ := hn m (le_trans (le_max_left ..) hm) N b
    let j : Fin m := ⟨i.1,(le_max_right ..).trans hm⟩
    obtain ⟨q,hq⟩ := from_basis b (originLeg G j (rCoeff i))
    rw [code_origin,digit_coeff] at hq
    exact ⟨p'*q,by rw [_root_.map_mul,hq]⟩

/-- Reflection here is linear. `duplex` moments below use an additional
coefficient conjugation (on second entry). -/
def turns (s : Ortho) (p : ProbeTower G n) : ProbeTower G n := fun i => solO s (p i)

lemma pull_code (s : Ortho) (p : ProbeTower G n) : pullSol s (code G n p) = code G n (turns s p) := by
  change pullSol s (∑ i, digit (p i))= _; rw [_root_.map_sum]
  exact Finset.sum_congr rfl fun i _ => pull_digit _ s

lemma bar_code (p : ProbeTower G n) : barPol (code G n p) = code G n p := by
  change barPol (∑ i,digit (p i))=_; rw [_root_.map_sum]; simp only [digit_bar]; rfl

def crash (p : ProbeTower G n) (x y : E4) : Derivation ℂ (WickPol G) (WickPol G) := ∑ i, descend (p i) x y

theorem crash_test (hx : x≠y) (p q : ProbeTower G n) :
    crash p x y (pullSol (face (x-y)) (code G n q)) = MvPolynomial.C
      (towerB (show x-y ∈ away from sub_ne_zero.mpr hx) n p q : ℂ) := by
  let s := face (x-y)
  rw [pull_code]
  unfold crash
  change (∑ i, descend (p i) x y) (∑ j, digit ((turns s q) j))= _
  rw [deriv_apply_sum]
  simp_rw [_root_.map_sum, descend_digit _ _ hx]
  let B := scan (G:=G) (show x-y ∈ away from sub_ne_zero.mpr hx)
  change _ = MvPolynomial.C (↑(∑ i : Fin n, ∑ j : Fin n, B i.val j.val (p i) (q j)) : ℂ)
  simp_rw [Complex.ofReal_sum,_root_.map_sum]; rfl

lemma crash_relation (p : ProbeTower G n) {x : Points m} (i : Fin m) (hx : x∈conf m) (W : Fin m → WickPol G) :
    Pair.replace x W i (W i * code G n p) = ∑ k : Others i, Pair.replace x W k (crash p (x i) (x k) (W k)) := by
  change Pair.replace x W i (W i * ∑ i, digit (p i)) = _
  simp_rw [Finset.mul_sum,_root_.map_sum,fun j => descend_relation (p j) x i hx,crash,deriv_apply_sum,_root_.map_sum]
  rw [Finset.sum_comm]
end YM.Extra.FD
