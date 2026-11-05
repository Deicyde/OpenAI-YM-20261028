import YM.Next.EXTRACTION.Tails
import YM.Org.Theatre
import YM.Work.A15

/-!
# Low-weight radial labels on the actual simple nonabelian gauge image

Through weight 3 there can be at most one curvature/derivative factor; all
invariant labels are constant. Use actual color normalization and compact group,
kill linear colors by Haar averaging (`ad` is the derivative of `adjoint` on the
image). Will enable actual detector estimates at these levels with NO weak
comparison or equation hypothesis on their projectors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Low
open Function Set Filter MeasureTheory Labels Gauge
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {G : Gauge}

lemma ad_rate (x y : G.Color) : HasDerivAt (fun t : ℝ => G.colorMat (G.adjoint (G.lieExp (t • x)) y))
    (G.colorMat (G.ad x y)) 0 := by
  let f (t : ℝ) := G.mat (G.lieExp (t • x))
  have he : HasDerivAt f (G.colorMat x) 0 := by
    unfold f
    simp_rw [G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat x) (0:ℝ)
  have h : f 0 = 1 := by simp [f,G.mat_lieExp]
  simp_rw [mat_adjoint,conjugate,colorMat_ad]
  convert! (he.mul_const (G.colorMat y) |>.mul he.star) using 1
  rw [h,one_mul,star_one,mul_one, G.colorMat_skew,mul_neg,sub_eq_add_neg]

lemma center_trivial (h : G.Simple) (y : G.Color) (hy : ∀ u : G.El, G.adjoint u y = y) : y = 0 := by
  let I := ⨅ x : G.Color, LinearMap.ker (G.ad x)
  have hI (z : G.Color) : z ∈ I ↔ ∀ x, G.ad x z = 0 := Submodule.mem_iInf _
  have hb : I = ⊥ := (h.ideals I (fun x z hz => ((hI z).mp hz x).symm ▸ I.zero_mem)).resolve_right (by
    obtain ⟨a,b,hab⟩ := h.nonabelian; exact fun he => hab ((hI b).mp (he.symm ▸ Submodule.mem_top) a))
  apply (Submodule.mem_bot ℝ).mp
  rw [← hb,hI]
  intro x
  apply G.colorMat_injective
  have he := ad_rate x y
  simp_rw [hy] at he
  exact he.unique ((hasDerivAt_const _ _).congr_deriv (map_zero _).symm)

lemma adjoint_cont (x : G.Color) : Continuous (fun u : G.El => G.adjoint u x) := by
  exact G.projectColor.continuous_of_finiteDimensional.comp ((G.continuous_mat.mul continuous_const).mul G.continuous_mat.star)

lemma colorMean (h : G.Simple) (x : G.Color) : ∫ u : G.El, G.adjoint u x ∂G.probHaar = 0 := by
  apply center_trivial h _
  intro v
  let L := LinearMap.toContinuousLinearMap (G.adjoint v)
  change L (∫ u : G.El, G.adjoint u x ∂_) = _
  rw [← L.integral_comp_comm ((adjoint_cont _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change (∫ u : G.El, G.adjoint v (G.adjoint u x) ∂_) = _
  simp_rw [← G.adjoint_mul]; apply integral_mul_left_eq_self (fun u => G.adjoint u x)

lemma adjoint_full : Continuous (fun u : G.El => LinearMap.toContinuousLinearMap (G.adjoint u)) := by
  let b := Module.finBasis ℝ G.Color
  let B := b.constr ℝ (M' := G.Color)
  let L := LinearMap.toContinuousLinearMap.toLinearMap.comp B.toLinearMap
  have he (u : G.El) : L (fun i => G.adjoint u (b i)) = LinearMap.toContinuousLinearMap (G.adjoint u) := congr_arg
    LinearMap.toContinuousLinearMap (b.ext (fun i => b.constr_basis ℝ _ i))
  simp_rw [← he]; exact L.continuous_of_finiteDimensional.comp (continuous_pi fun i => adjoint_cont (b i))

variable {j : ℕ}

def painted (A : Labels.Taylor G j) : (G.Color →L[ℝ] G.Color) →ₗ[ℝ] Labels.Raw G j where
  toFun L i := L.compContinuousMultilinearMap (A.val i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma taylor_cont (A : Labels.Taylor G j) : Continuous (fun u : G.El => Labels.Taylor.paint u A) := continuous_induced_rng.mpr <|
  (painted A).continuous_of_finiteDimensional.comp adjoint_full

lemma painted_mean (h : G.Simple) (A : Labels.Taylor G j) : ∫ u : G.El, Labels.Taylor.paint u A ∂G.probHaar = 0 := by
  apply Subtype.ext
  funext i; ext1 v
  let L : Labels.Taylor G j →ₗ[ℝ] G.Color := {
    toFun a := a.val i v
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  change L _ = 0
  apply Eq.trans (ContinuousLinearMap.integral_comp_comm (E := Labels.Taylor G j) (Fₗ := G.Color) (𝕜 := ℝ) (LinearMap.toContinuousLinearMap L) (μ := G.probHaar)
    ((taylor_cont A).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
  apply colorMean h

def colorRead (A : Jet G) (i : Key G) := fun u : G.El => coord (colored u A) i
lemma coord_cont (A : Jet G) (i : Key G) : Continuous (colorRead A i) :=
  Complex.continuous_ofReal.comp (((axes G i.1).coord i.2).continuous_of_finiteDimensional.comp (taylor_cont (A i.1)))
lemma coord_mean (h : G.Simple) (A : Jet G) (i : Key G) : ∫ u, colorRead A i u ∂G.probHaar = 0 := by
  let L := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((axes G i.1).coord i.2))
  change (∫ u : G.El, L (Labels.Taylor.paint u (A i.1)) ∂_) = _
  rw [ContinuousLinearMap.integral_comp_comm (E := Labels.Taylor G i.1) (Fₗ := ℂ) (𝕜 := ℝ) L (μ := G.probHaar) ((taylor_cont (A i.1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]; exact (congr_arg L (painted_mean h (A i.1))).trans L.map_zero

lemma support_low {d : ℕ} (hd : d < 4) (p : Label G d) {i} (hi : i ∈ p.val.support) (he : i ≠ 0) :
    ∃ j : Key G, i = Finsupp.single j 1 := by
  classical
  have hv : height i ≤ d := (MvPolynomial.mem_restrictSupport_iff ℂ).mp (show p.val ∈ limited G d from p.property.1) hi
  have hu : (∑ j ∈ i.support, i j) * 2 ≤ height i := by
    rw [Finset.sum_mul,height,Finsupp.weight_apply,Finsupp.sum]
    exact Finset.sum_le_sum (fun b _ => Nat.mul_le_mul_left _ (show 2 ≤ generation b by unfold generation; omega))
  obtain ⟨b,hb⟩ : i.support.Nonempty := by simpa using he
  have he (b : Key G) (hb : b ∈ i.support) : i b = 1 := by
    have h := Finset.single_le_sum (f := i) (s := i.support) (by simp) hb
    have h' := Finsupp.mem_support_iff.mp hb
    omega
  refine ⟨b, Finsupp.eq_single_iff.mpr ⟨fun c hc => ?_, he b hb⟩⟩
  rw [Finset.mem_singleton]
  by_contra hcb
  have he' := Finset.sum_le_sum_of_subset (f := i) (show ({c,b} : Finset _) ⊆ i.support by simp [Finset.insert_subset_iff, hc, hb])
  rw [Finset.sum_pair hcb,he c hc,he b hb] at he'
  omega

lemma read_low {d} (p : Label G d) (A : Jet G) :
    read A p.val = ∑ i ∈ p.val.support, (MvPolynomial.coeff i p.val) * (read A (MvPolynomial.monomial i (1:ℂ))) := by
  conv_lhs => arg 2; rw [p.val.as_sum]
  rw [map_sum]; apply Finset.sum_congr rfl; intro i _
  rw [← mul_one (MvPolynomial.coeff i p.val),← MvPolynomial.C_mul_monomial,map_mul,mul_one]; simp [Labels.read]

lemma poly_mean (h : G.Simple) {d : ℕ} (hd : d < 4) (p : Label G d) (A : Jet G) :
    read A p.val = MvPolynomial.coeff 0 p.val := by
  classical
  let c i := MvPolynomial.coeff i p.val
  let L i (u : G.El) := c i * read (colored u A) (MvPolynomial.monomial i 1)
  have he u : read A p.val = ∑ i ∈ p.val.support, L i u := (p.property.2 A u).symm.trans (read_low p _)
  have ht (j : Key G) u : L (Finsupp.single j 1) u = c (Finsupp.single j 1) * colorRead A j u := by
    change c _ * Labels.read _ (MvPolynomial.X j) = _; simp [Labels.read,colorRead]
  have hμ (i) (hi : i ∈ p.val.support) : Integrable (L i) G.probHaar := by
    by_cases h : i = 0
    · subst i; apply (integrable_const (c 0 * 1)).congr (Eventually.of_forall (fun u => ?_))
      exact congr_arg (c 0 * ·) (map_one _).symm
    obtain ⟨j,rfl⟩ := support_low hd p hi h
    rw [funext (ht j)]
    exact ((coord_cont A j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [show read A p.val = ∫ _ : G.El, read A p.val ∂G.probHaar by simp]
  conv_lhs => arg 2; intro u; rw [he u]
  rw [integral_finsetSum _ hμ, Finset.sum_eq_single 0]
  · unfold L; rw [show MvPolynomial.monomial (0:Key G →₀ ℕ) (1:ℂ) = 1 by rfl]; simp [c]
  · intro i hi h
    obtain ⟨j,rfl⟩ := support_low hd p hi h
    rw [funext (ht j),integral_const_mul, coord_mean (by assumption),mul_zero]
  · intro h
    have hz := not_not.mp (mt MvPolynomial.mem_support_iff.mpr h)
    unfold L; simp [c,hz]

theorem labels_low (h : G.Simple) {d} (hd : d < 4) (p : Labels.Label G d) : ∃ c : ℂ, p = c • Labels.unit G d := by
  refine ⟨MvPolynomial.coeff 0 p.val,Subtype.ext <| Labels.eval_ext _ _ (fun A => ?_)⟩
  change read A _ = read A (MvPolynomial.coeff 0 p.val • (1 : Pol G))
  simp [poly_mean h hd p A]
end YM.Push.FiniteDetection.Low
