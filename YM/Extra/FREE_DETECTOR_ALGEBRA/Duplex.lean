import YM.Extra.FREE_DETECTOR_ALGEBRA.Script

set_option warningAsError false

/-!
# Two-point tests of polynomial labels

At first ordinary bilinear. Turn second indices alone to make another
bilinear test -- *then* conjugate coefficients when using a positive
sesquilinear form. Genuine multiplicities from `moment`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Maxwell Wick Pair Tensor Analysis
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {x y : E4}

def couple (x y : E4) : Points 2 := points ![x,y]
lemma couple_ok (hx : x≠y) : couple x y ∈ conf 2 := by
  intro i j; fin_cases i <;> fin_cases j
  · simp
  · exact fun he => (hx he).elim
  · exact fun he => (hx he.symm).elim
  simp

def join (x y : E4) (p q : WickPol G) := moment G (couple x y) ![p,q]

lemma replace_join₁ (p q a : WickPol G) : replace (couple x y) ![a,q] (0:Fin 2) p = join x y p q := by
  rw [replace_at,show Function.update ![a,q] (0:Fin 2) p = ![p,q] by ext1 v; fin_cases v <;> simp]; rfl

lemma replace_join₂ (p q a : WickPol G) : replace (couple x y) ![p,a] (1:Fin 2) q = join x y p q := by
  rw [replace_at,show Function.update ![p,a] (1:Fin 2) q = ![p,q] by ext1 v; fin_cases v <;> simp]; rfl

def joinLin (x y : E4) : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ where
  toFun p := Pair.replace (couple x y) ![p,0] 1
  map_add' p q := by
    apply LinearMap.ext; intro k; change Pair.replace (couple x y) ![p+q,0] 1 k = Pair.replace (couple x y) ![p,0] 1 k + Pair.replace (couple x y) ![q,0] 1 k
    simp only [replace_join₂]
    simp_rw [← replace_join₁ (a:=(0:WickPol G)),_root_.map_add]
  map_smul' t p := by
    apply LinearMap.ext; intro k; change Pair.replace (couple x y) ![t • p,0] 1 k = t • Pair.replace (couple x y) ![p,0] 1 k
    simp only [replace_join₂]
    simp_rw [← replace_join₁ (a:=(0:WickPol G)),_root_.map_smul]

theorem joinLin_apply (p q : WickPol G) : joinLin x y p q = join x y p q := replace_join₂ p q 0

def aligned (G : Gauge) (x y : E4) : WickPol G →ₗ[ℂ] WickPol G →ₗ[ℂ] ℂ where
  toFun p := (joinLin x y p).comp (pullSol (face (x-y))).toLinearMap
  map_add' u v := by ext w; simp
  map_smul' c u := by ext w; simp

def duplex (x y : E4) (p q : WickPol G) := aligned G x y p (barPol q)

theorem aligned_apply (p q : WickPol G) : aligned G x y p q = join x y p (pullSol (face (x-y)) q) := joinLin_apply (x:=x) (y:=y) p _

variable {n : ℕ} {u v : ProbeTower G n}

theorem join_crash (p : ProbeTower G n) (P Q : WickPol G) (hx : x≠y) : join x y (P*code G n p) Q =
    join x y P (crash p x y Q) := by
  have he := crash_relation p (x:=couple x y) 0 (couple_ok hx) ![P,Q]
  have ht : ∀ i : Others (0:Fin 2), i = (⟨1,by decide⟩ : Others (0:Fin 2)) := by rintro ⟨i,hi⟩; fin_cases i <;> first | rfl | exact (hi rfl).elim
  rw [Finset.sum_eq_single_of_mem (⟨(1:Fin 2),by decide⟩ : Others (0:Fin 2)) (Finset.mem_univ _) (fun i _ h => (h (ht i)).elim)] at he
  change replace (couple x y) _ 0 (P * code G n p) = replace (couple x y) _ 1 (crash p x y Q) at he
  rwa [replace_join₁, replace_join₂] at he

theorem join_crash' (p : ProbeTower G n) (P Q : WickPol G) (hx : x≠y) : join x y P (Q*code G n p)=
    join x y (crash p y x P) Q := by
  have he := crash_relation p (x:=couple x y) 1 (couple_ok hx) ![P,Q]
  have ht : ∀ i : Others (1:Fin 2), i = (⟨0,by decide⟩ : Others (1:Fin 2)) := by rintro ⟨i,hi⟩; fin_cases i <;> first | rfl | exact (hi rfl).elim
  rw [Finset.sum_eq_single_of_mem (⟨(0:Fin 2),by decide⟩ : Others (1:Fin 2)) (Finset.mem_univ _) (fun i _ h => (h (ht i)).elim)] at he
  change replace (couple x y) _ 1 (Q * code G n p) = replace (couple x y) _ 0 (crash p y x P) at he
  rwa [replace_join₁, replace_join₂] at he

lemma aligned_one_right (p : ProbeTower G n) (P : WickPol G) (hx : x≠y) : aligned G x y 1 (P*code G n p)=0 := by
  rw [aligned_apply,_root_.map_mul,pull_code,join_crash' _ _ _ hx]
  rw [← joinLin_apply]
  simp

lemma aligned_unit (G : Gauge) (x y : E4) : aligned G x y 1 1=1 := by
  rw [aligned_apply,_root_.map_one,join]
  have h : (![(1:WickPol G),1]) = fun _ => 1 := by ext1 i; fin_cases i <;> rfl
  rw [h]; exact constants _

variable {ι : Type*} [DecidableEq ι]

lemma crash_basis (b : ι→ProbeTower G n) (hx : x≠y) (i : ι) (A : ℝ)
    (he : ∀ j, towerB (show x-y∈away from sub_ne_zero.mpr hx) n (b i) (b j) = if j=i then A else 0) (p : MvPolynomial ι ℂ) :
    crash (b i) x y (pullSol (face (x-y)) (encode b p)) = (A:ℂ) • pullSol (face (x-y)) (encode b (MvPolynomial.pderiv i p)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [encode,pullSol,MvPolynomial.derivation_C]
  | add p q hp hq => simp only [_root_.map_add,hp,hq,smul_add]
  | mul_X p j h =>
    let s := face (x-y)
    have ht : crash (b i) x y (pullSol s (encode b (MvPolynomial.X j))) =
        (A:ℂ) • pullSol s (encode b (MvPolynomial.pderiv i (MvPolynomial.X j))) := by
      rw [encode_X,crash_test hx,he j]; by_cases hj : j=i
      · subst j; simp [← MvPolynomial.C_mul']
      simp [hj]
    simp only [Derivation.leibniz,smul_eq_mul,_root_.map_add,_root_.map_mul,h]; rw [ht]; simp [smul_add,s]

lemma aligned_step (b : ι→ProbeTower G n) (hx : x≠y) (i : ι) (A : ℝ)
    (he : ∀ j, towerB (show x-y∈away from sub_ne_zero.mpr hx) n (b i) (b j) = if j=i then A else 0) (p q : MvPolynomial ι ℂ) :
    aligned G x y (encode b (p*MvPolynomial.X i)) (encode b q) =
      A • aligned G x y (encode b p) (encode b (MvPolynomial.pderiv i q)) := by
  simp only [aligned_apply,_root_.map_mul,encode_X]
  rw [join_crash _ _ _ hx,crash_basis b hx i A he,← joinLin_apply,← joinLin_apply,_root_.map_smul]; rfl
end YM.Extra.FD
