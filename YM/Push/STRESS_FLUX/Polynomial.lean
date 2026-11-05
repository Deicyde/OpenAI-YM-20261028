import YM.Push.STRESS_FLUX.Jets
import YM.Push.STRESS_FLUX.Low

/-! Explicit curvature-product labels and an equation label. Includes trace, slot and color
normalizations and real signed-axis transformations (sign indexed by INPUT). Operations on
these polynomials are *not* multiplication of limiting separated fields at the same point.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Labels Function Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge}

def changedRead (e : ∀ i, Module.End ℝ (Taylor G i)) (J : Jet G) := changedJet e J
abbrev shifted (s : Signed) (J : Jet G) := changedJet (fun i => Taylor.turn (G:=G) (j:=i) s.ortho⁻¹) J

def coordPol {j : ℕ} (p : Taylor G j →ₗ[ℝ] ℝ) : Pol G := ∑ i,
  MvPolynomial.C (R:=ℂ) (p (axes G j i)) * MvPolynomial.X ⟨j,i⟩

lemma coordPol_value {j : ℕ} (p : Taylor G j →ₗ[ℝ] ℝ) (J : Jet G) : read J (coordPol p) = (p (J j) : ℝ) := by
  conv_rhs => rw [← (axes G j).sum_repr (J j)]
  simp only [coordPol,Labels.read, map_sum, map_mul, map_smul, MvPolynomial.aeval_X,MvPolynomial.aeval_C, coord,
    Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm ..
lemma coordPol_pure {j : ℕ} (p : Taylor G j →ₗ[ℝ] ℝ) : pureDegree (coordPol p) (j+2) 1 :=
  MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun i _ =>
    (MvPolynomial.isWeightedHomogeneous_X ℂ bidegree (⟨j,i⟩ : Key G)).C_mul _

def productPol {j k : ℕ} (f : Taylor G j →ₗ[ℝ] G.Color) (g : Taylor G k →ₗ[ℝ] G.Color) : Pol G :=
    ∑ i, coordPol ((EuclideanSpace.proj i).toLinearMap.comp f) * coordPol ((EuclideanSpace.proj i).toLinearMap.comp g)
lemma productPol_grade {j k : ℕ} (f : Taylor G j →ₗ[ℝ] G.Color) (g : Taylor G k →ₗ[ℝ] G.Color) :
    pureDegree (productPol f g) ((j+2)+(k+2)) 2 := MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun _ _ => (coordPol_pure _).mul (coordPol_pure _))
lemma productPol_value {j k : ℕ} (f : Taylor G j →ₗ[ℝ] G.Color) (g : Taylor G k →ₗ[ℝ] G.Color) (J : Jet G) :
    read J (productPol f g) = (⟪f (J j),g (J k)⟫_ℝ : ℂ) := by
  unfold productPol
  simp only [map_sum,map_mul,coordPol_value, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    dotProduct, Complex.ofReal_sum,Complex.ofReal_mul]; exact Finset.sum_congr rfl fun _ _ => mul_comm ..

lemma product_mem {j k d : ℕ} (hd : (j+2)+(k+2) ≤ d) (f : Taylor G j →ₗ[ℝ] G.Color) (g : Taylor G k →ₗ[ℝ] G.Color)
    (hf : ∀ u x, f (Taylor.paint u x) = G.adjoint u (f x)) (hg : ∀ u x, g (Taylor.paint u x) = G.adjoint u (g x)) :
    productPol f g ∈ localFields G d := by
  refine ⟨(MvPolynomial.mem_restrictSupport_iff ℂ).mpr (fun b hb => ?_), fun J u => ?_⟩
  · have he := productPol_grade f g (MvPolynomial.mem_support_iff.mp hb); rw [weight_slot] at he
    exact (congr_arg Prod.fst he).le.trans hd
  simp only [productPol_value,colored,hf,hg,inner_adjoint]

/-- Real inner product of F_ab with F_cd in the label polynomial, no extra half or dimension factor. -/
def pair (G : Gauge) (a b c d : Axis) : Label G 4 :=
  ⟨productPol (curl0 a b) (curl0 c d),product_mem le_rfl (curl0 a b) (curl0 c d) (fun _ x => curled_paint x 0 a b _) (fun _ x => curled_paint x 0 c d _)⟩

lemma pair_value (a b c d : Axis) (J : Jet G) :
    read J (pair G a b c d).val = (⟪curl0 a b (J 0),curl0 c d (J 0)⟫_ℝ : ℂ) := productPol_value ..


def pairDeriv (G : Gauge) (a b i c d : Axis) : Label G 5 :=
  ⟨productPol (curl0 a b) (curl1 i c d), product_mem le_rfl (curl0 a b) (curl1 i c d) (fun _ x => curled_paint x 0 a b _) (fun _ x => curled_paint x (basis i) c d _)⟩

lemma pairDeriv_value (a b i c d : Axis) (J : Jet G) :
    read J (pairDeriv G a b i c d).val = (⟪curl0 a b (J 0),curl1 i c d (J 1)⟫_ℝ : ℂ) := productPol_value ..

lemma label_ext {d : ℕ} {v w : Label G d} (he : ∀ J, read J v.val = read J w.val) : v=w := Subtype.ext (eval_ext _ _ he)
lemma label_real {d : ℕ} (v : Label G d) (he : ∀ J, star (read J v.val) = read J v.val) : realBar v=v :=
  label_ext fun J => (conj_value ..).trans (he J)
lemma pair_real (a b c d : Axis) : realBar (pair G a b c d) = pair G a b c d := label_real _ fun J => by simp [pair_value]
lemma pairDeriv_real (a b i c d : Axis) : realBar (pairDeriv G a b i c d) = pairDeriv G a b i c d := label_real _ fun J => by simp [pairDeriv_value]

lemma curl0_shifted (s : Signed) (J : Jet G) (a b : Axis) : curl0 a b (shifted s J 0) =
    (sign s a * sign s b) • curl0 (s.perm a) (s.perm b) (J 0) := by
  have he := curl0_turn (shifted s J 0) s a b
  have ht : Taylor.turn s.ortho (shifted s J 0) = J 0 := by
    change Taylor.turn s.ortho (Taylor.turn s.ortho⁻¹ _) = _; rw [← Taylor.turn_mul, mul_inv_cancel,Taylor.oneTurn]
  rw [ht] at he; rw [he,smul_smul, ← sq, mul_pow,sign_sq,sign_sq, one_mul,one_smul]
lemma curl1_shifted (s : Signed) (J : Jet G) (i a b : Axis) : curl1 i a b (shifted s J 1) =
    (sign s i * (sign s a * sign s b)) • curl1 (s.perm i) (s.perm a) (s.perm b) (J 1) := by
  have he := curl1_turn (shifted s J 1) s i a b
  have ht : Taylor.turn s.ortho (shifted s J 1) = J 1 := by
    change Taylor.turn s.ortho (Taylor.turn s.ortho⁻¹ _) = _; rw [← Taylor.turn_mul, mul_inv_cancel,Taylor.oneTurn]
  rw [ht] at he; rw [he,smul_smul, ← sq, mul_pow, mul_pow, sign_sq,sign_sq,sign_sq, one_mul,one_mul,one_smul]

lemma read_smul (J : Jet G) (a : ℝ) (p : Pol G) : read J (a • p) = a • read J p :=
  ((read J).toLinearMap.restrictScalars ℝ).map_smul a p

theorem pair_turn (s : Signed) (a i b j : Axis) : tensor s.ortho (pair G a i b j) =
    ((sign s a * sign s i)*(sign s b * sign s j)) • pair G (s.perm a) (s.perm i) (s.perm b) (s.perm j) := by
  refine label_ext fun J => ?_
  change read J (changed _ _) = read J ((_ : ℝ) • _)
  simp_rw [eval_changed, read_smul, pair_value, curl0_shifted s J]
  simp [real_inner_smul_left,real_inner_smul_right,mul_assoc,Complex.real_smul]; ring

theorem pairDeriv_turn (s : Signed) (a i k b j : Axis) : tensor s.ortho (pairDeriv G a i k b j) =
    ((sign s a * sign s i)*(sign s k * (sign s b * sign s j))) •
      pairDeriv G (s.perm a) (s.perm i) (s.perm k) (s.perm b) (s.perm j) := by
  refine label_ext fun J => ?_
  change read J (changed _ _) = read J ((_ : ℝ) • _)
  simp_rw [eval_changed, read_smul, pairDeriv_value, curl0_shifted s J, curl1_shifted s J]
  simp [real_inner_smul_left,real_inner_smul_right,mul_assoc,Complex.real_smul]; ring



/-- A nonzero polar vector killed by Maxwell projection. Antisymmetric first pair has free
index first; the relative sign would flip with the opposite pair order. At this stage no
claim of being a null on a finite cutoff or a particular interacting-table null. -/
def eom (G : Gauge) (b : Axis) : Label G 5 := ∑ i, ∑ a, pairDeriv G b i a a i

lemma eom_real (b : Axis) : realBar (eom G b) = eom G b := by simp [eom,pairDeriv_real]
lemma eom_vector (b : Axis) (s : Signed) : tensor s.ortho (eom G b) = sign s b • eom G (s.perm b) := by
  have he (a i : Axis) : (sign s b * sign s i)*(sign s a * (sign s a * sign s i)) = sign s b := by
    unfold sign; split_ifs <;> norm_num
  have hw (i j : Axis) := Equiv.sum_comp s.perm (fun a => pairDeriv G i j a a j)
  simp [eom,pairDeriv_turn, he, ← Finset.smul_sum, hw, Equiv.sum_comp s.perm (fun i => ∑ a, pairDeriv G (s.perm b) i a a i)]

lemma eom_null (b : Axis) : eom G b ∈ Maxwell.equationIdeal G 5 := by
  rw [Maxwell.ideal_meaning]; intro X
  have he (a i : Axis) : curl1 a a i (Maxwell.gaugeJet (X 1)) =
      Maxwell.grad a (Tensor.diagonal ((X 1).val a i)) 0 := by
    change Tensor.diagonal (Maxwell.takeCurl _ a i) _ = _
    rw [Maxwell.match_leg]; unfold Maxwell.grad Analysis.D
    let L := ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)
    obtain ⟨f,hf⟩ := L.surjective ((X 1).val a i)
    rw [← hf]; change f _ = fderiv ℝ (fun z => f z) 0 _; rw [f.fderiv]
  simp [eom, pairDeriv_value]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Complex.ofReal_sum]
  simp_rw [he, ← inner_sum, (X 1).property.2 i 0, inner_zero_right,Complex.ofReal_zero]



 
lemma curl0_leg (a b i j : Axis) (x : G.Color) : curl0 i j (leg0 a b x) =
    (basis i a * basis j b - basis i b * basis j a) • x := by
  rw [curl0_value, leg0_value,leg0_value]
  have ht (a b : Axis) (v : G.Color) : (if b=a then v else 0) = basis b a • v := by simp [eq_comm]
  rw [ht,ht,ht,ht]; simp only [smul_sub, smul_smul]; module

lemma curl1_leg (a b r i j k : Axis) (x : G.Color) : curl1 k i j (leg1 r a b x) =
    (1/3 * ((basis j b * (basis i a * basis k r + basis k a * basis i r) -
             basis j a * (basis i b * basis k r + basis k b * basis i r)) -
            (basis i b * (basis j a * basis k r + basis k a * basis j r) -
             basis i a * (basis j b * basis k r + basis k b * basis j r)))) • x := by
  rw [curl1, curled_deriv]
  have ht (a : Axis) := (Maxwell.compAxis a).hasFDerivAt (x := basis k)
  have he (i j) : Maxwell.grad i ((leg1 r a b x).value j) (basis k) =
      (1/3 * (basis j b * (basis i a * basis k r + basis k a * basis i r) -
              basis j a * (basis i b * basis k r + basis k b * basis i r))) • x := by
    have hc (c d : Axis) : HasFDerivAt (fun z : E4 => basis j c • z d • z r • x)
        (basis j c • (basis k d • (Maxwell.compAxis r).smulRight x + (Maxwell.compAxis d).smulRight (basis k r • x))) (basis k) := by
      exact (((ht d).smul ((ht r).smul_const x)).const_smul (basis j c))
    rw [show (leg1 r a b x).value j = fun z : E4 => (3:ℝ)⁻¹ • ((basis j b • z a • z r • x) - (basis j a • z b • z r • x)) by
      funext z; simp [leg1_value, basis_eq,eq_comm]]
    unfold Maxwell.grad Analysis.D
    change fderiv ℝ ((3:ℝ)⁻¹ • ((fun z : E4 => basis j b • z a • z r • x) - fun z => basis j a • z b • z r • x)) _ _ = _
    rw [(((hc b a).sub (hc a b)).const_smul (3:ℝ)⁻¹).fderiv]
    simp only [smul_apply, sub_apply, add_apply, ContinuousLinearMap.smulRight_apply]
    change (3:ℝ)⁻¹ • (basis j b • (basis k a • basis i r • x + basis i a • basis k r • x) -
      basis j a • (basis k b • basis i r • x + basis i b • basis k r • x)) = _
    module
  rw [he,he]; module

private def eomJet (x : G.Color) : Jet G := Pi.single 0 (leg0 (G:=G) 0 1 x) + Pi.single 1 (leg1 (G:=G) 0 0 1 x)
lemma eom_nonzero (H : G.Simple) : eom G ≠ 0 := by
  haveI := H.nontrivial_color
  obtain ⟨x,hx⟩ := exists_ne (0:G.Color)
  have he : read (eomJet x) (eom G 0).val = (⟪x,x⟫_ℝ : ℂ) := by
    unfold eom; simp only [AddSubmonoidClass.coe_finsetSum, map_sum]; change (∑ i, ∑ a, read (eomJet x) (pairDeriv G 0 i a a i).val) = _
    simp only [pairDeriv_value, eomJet, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (show (1:ℕ)≠0 by decide), Pi.single_eq_of_ne (show (0:ℕ)≠1 by decide),add_zero,zero_add,
      Fin.sum_univ_four, curl0_leg, curl1_leg]
    norm_num [basis_eq, Fin.ext_iff]
  intro hz
  rw [hz] at he; change read _ (0 : Label G 5).val = _ at he; simp at he; exact hx (norm_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp (by exact_mod_cast he.symm)))

abbrev Coeff := Fin 4 → ℝ
-- order c, diagonal-with-index, diagonal-total (ordered sum), shear

def stress (G : Gauge) : Coeff →ₗ[ℝ] Axis → Axis → Label G 4 where
  toFun t a b := if a=b then t 0 • unit G 4 + t 1 • (∑ i, pair G a i a i) + t 2 • (∑ i, ∑ j, pair G i j i j) else
      t 3 • ∑ i, pair G a i b i
  map_add' x y := by funext a b; dsimp; split <;> simp only [add_smul]; abel
  map_smul' c x := by funext a b; dsimp; split <;> simp only [smul_add,smul_smul]

lemma stress_of (t : Coeff) (a b : Axis) : stress G t a b =
    if a=b then t 0 • unit G 4 + t 1 • (∑ i, pair G a i a i) + t 2 • (∑ i, ∑ j, pair G i j i j) else
    t 3 • ∑ i, pair G a i b i := rfl

abbrev weyl : Coeff := ![0,1,-1/4,1]


lemma pair_swap (a i b j : Axis) : pair G a i b j = pair G b j a i := label_ext fun J => by
  rw [pair_value,pair_value,real_inner_comm]
lemma stress_symm (t : Coeff) (a b : Axis) : stress G t a b = stress G t b a := by
  rcases eq_or_ne a b with h|h
  · rw [h]
  rw [stress_of,stress_of,if_neg h,if_neg h.symm]
  exact congr_arg _ (Finset.sum_congr rfl fun _ _ => pair_swap ..)
lemma realBar_scale {d : ℕ} (x : Label G d) (c : ℝ) : realBar (c • x) = c • realBar x := by
  rw [← IsScalarTower.algebraMap_smul ℂ c, ← IsScalarTower.algebraMap_smul ℂ c, map_smulₛₗ]; simp
lemma tensor_scale {d : ℕ} (s : Ortho) (x : Label G d) (c : ℝ) : tensor s (c • x) = c • tensor s x :=
    ((tensor s).restrictScalars ℝ).map_smul c x
lemma stress_real (t : Coeff) (a b : Axis) : realBar (stress G t a b) = stress G t a b := by simp only [stress_of]; split <;> simp only [realBar_scale,map_add,map_sum,unit_real,pair_real]
lemma stress_tensor (s : Signed) (t : Coeff) (a b : Axis) :
    tensor s.ortho (stress G t a b) = (sign s a * sign s b) • stress G t (s.perm a) (s.perm b) := by
  have he (a b i : Axis) : (sign s a * sign s i) * (sign s b * sign s i) = sign s a * sign s b := by
    unfold sign; split_ifs <;> norm_num
  have ht (a i : Axis) : tensor s.ortho (pair G a i a i) = pair G (s.perm a) (s.perm i) (s.perm a) (s.perm i) := by
    rw [pair_turn,he,← sq, sign_sq,one_smul]
  have hw (a b : Axis) := Equiv.sum_comp s.perm (fun i => pair G a i b i)
  simp only [stress_of,s.perm.injective.eq_iff]; split
  · rename_i h; subst b
    have hu : tensor s.ortho (unit G 4) = unit G 4 := Subtype.ext ((rotated (G:=G) s.ortho).map_one)
    simp only [map_add,map_sum,tensor_scale,ht,← sq, sign_sq,one_smul, hu,
      hw, Equiv.sum_comp s.perm (fun i => ∑ j, pair G i j i j)]
  rw [smul_comm _ (t 3)]; simp only [map_sum,tensor_scale, pair_turn, he, ← Finset.smul_sum, hw]
end YM.StressFlux
