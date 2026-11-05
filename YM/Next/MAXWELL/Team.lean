import YM.Next.MAXWELL.BaseColor
import YM.Next.MAXWELL.Covariance
import YM.Next.MAXWELL.Derives


/-! # Color paired labels and necessary low moment classification -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G : Gauge} {j l d : ℕ}

def available (v : Shell G j) (p : Flavor j) : G.Color := WithLp.toLp 2 fun i => flavor (G:=G) j i p v

lemma shows_hue (v : Shell G j) (u : G.El) (p : Flavor j) :
    available (castFace u j v) p = G.adjoint u (available v p) := by
  have he (k) : faceMap j (cp (G:=G) k) (castFace u j v) = ∑ i : G.ColorIndex,
      (G.adjoint u (unitColor G i) k) • (faceMap j (cp (G:=G) i) v) := by
    apply Subtype.ext; funext a b; ext1 z
    simp_rw [AddSubmonoidClass.coe_finsetSum,SetLike.val_smul,Finset.sum_apply,sum_apply,Pi.smul_apply,smul_apply]
    change G.adjoint u (v.val a b z) k = _
    conv_lhs => rw [← color_sum (G:=G) (v.val a b z), map_sum]
    simp_rw [WithLp.ofLp_sum,Finset.sum_apply,map_smul, PiLp.smul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm ..
  ext1 i
  change p (faceMap _ _ _) = _
  rw [he]; conv_rhs => rw [← color_sum (G:=G) (available v p), map_sum]
  simp only [map_sum,map_smul,WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm ..

def flavor_pick (p : Probe G j) (i : G.ColorIndex) : Flavor j := p.comp (fill j (unitColor G i))

def bit (p : Flavor j) (i : G.ColorIndex) := symbol j (flavor (G:=G) j i p)

def team (G : Gauge) (p : Flavor j) (q : Flavor l) := ∑ i : G.ColorIndex, bit p i * bit q i

lemma basicTeam (A : TaylorTower G) (p : Flavor j) (q : Flavor l) :
    probe A (team G p q)= (⟪available (A j) p,available (A l) q⟫_ℝ:ℂ) := by
  unfold team; simp only [map_sum,bit,map_mul,symbol_test,← Complex.ofReal_mul,← Complex.ofReal_sum];
  rw [real_inner_comm]; rfl

lemma realBit (p : Flavor j) (i : G.ColorIndex) : realForm (bit p i)=bit p i := real_symbol _
lemma realTeam (p : Flavor j) (q : Flavor l) : realForm (team G p q)=team G p q := by simp only [team,map_sum,map_mul,realBit]
lemma colorTeam (p : Flavor j) (q : Flavor l) : Painted (team G p q) := by
  intro u; apply equalPol; intro A
  rw [pigment_action,basicTeam,basicTeam];
  simp only [shade, shows_hue]
  let L : G.Color →ₗᵢ[ℝ] G.Color := ⟨G.adjoint u,G.norm_adjoint u⟩
  exact congr_arg (fun t : ℝ => (t : ℂ)) (L.inner_map_map ..)



lemma team_label (p : Flavor j) (q : Flavor l) (h : j+l+4 ≤ d) : team G p q ∈ shellSector G d := by
  refine sector.mpr ⟨?_,colorTeam p q⟩
  have he : MvPolynomial.IsWeightedHomogeneous scaleW (team G p q) (j+l+4) := by
    unfold team; apply MvPolynomial.IsWeightedHomogeneous.sum; intro i _
    rw [show j+l+4=j+2+(l+2) by omega]; exact (symbol_hom (flavor (G:=G) j i p) (fun j => j+2)).mul (symbol_hom (flavor (G:=G) l i q) (fun i => i+2))
  rw [lowerCap, MvPolynomial.mem_restrictSupport_iff]; intro k hk; exact le_trans
    ((he (MvPolynomial.mem_support_iff.mp hk)).le) h

lemma divide (p : Probe G j) : symbol j p = ∑ i : G.ColorIndex, bit (flavor_pick p i) i := by
  obtain ⟨S,h⟩ := symbol_linear (G:=G) j
  have hp : p=∑ i : G.ColorIndex, flavor (G:=G) j i (flavor_pick p i) := by
    apply LinearMap.ext; intro u
    conv_lhs => rw [← half_sum u]
    rw [LinearMap.sum_apply,map_sum]; rfl
  conv_lhs => rw [hp]
  simp_rw [bit,← h]; exact map_sum S _ _

private lemma phi_real {G : Gauge} {f : G.El → ℝ} (H : Continuous f) : Integrable f G.probHaar :=
  H.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def line (m : G.ColorIndex) (x : G.Color) (u : G.El) := G.adjoint u x m

private lemma line_cont (m : G.ColorIndex) (x : G.Color) : Continuous (line m x) :=
  (EuclideanSpace.proj m : G.Color →L[ℝ] ℝ).continuous.comp (adj_cont x)

lemma pays_color (h : G.Simple) (m n : G.ColorIndex) : ∃ C : ℝ, ∀ x y : G.Color,
    (∫ u, line m x u * line n y u ∂G.probHaar) = C * ⟪x,y⟫_ℝ := by
  let D (x y : G.Color) := fun u => line m x u * line n y u
  have he (x y) : Integrable (D x y) G.probHaar := phi_real ((line_cont _ _).mul (line_cont _ _))
  have H (x y z : G.Color) : (∫ u,D x (y+z) u ∂G.probHaar) = (∫ u, D x y u ∂G.probHaar) + ∫ u,D x z u ∂G.probHaar := by
    rw [show D x (y+z) = fun u => D x y u + D x z u from funext fun u => by simp [D,line,mul_add]]; exact integral_add (he ..) (he ..)
  let B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ :=
    { toFun x :=
        { toFun y := ∫ u,D x y u ∂G.probHaar
          map_add' _ _ := H ..
          map_smul' t y := by
            rw [show D x (t • y) = fun z => t * D x y z from funext fun z => by simp [D,line,mul_left_comm]]
            exact integral_const_mul .. }
      map_add' x y := by
        apply LinearMap.ext; intro b
        change (∫ u,D (x+y) b u ∂G.probHaar)= (∫ u,D x b u ∂G.probHaar) + ∫ u,D y b u ∂G.probHaar
        rw [show D (x+y) b = fun z => D x b z+D y b z from funext fun z => by simp [D,line,add_mul]]; exact integral_add (he ..) (he ..)
      map_smul' t x := by
        apply LinearMap.ext; intro b
        change (∫ u,D (t • x) b u ∂G.probHaar) = t*(∫ u,D x b u ∂G.probHaar)
        simp_rw [show ∀ u, D (t • x) b u=t*D x b u from fun u => by simp [D,line,mul_assoc],integral_const_mul] }
  apply invariant_two h B
  intro u x y
  change (∫ z,D (G.adjoint u x) (G.adjoint u y) z ∂G.probHaar)= ∫ z,D x y z ∂G.probHaar
  simp_rw [show ∀ z : G.El, D (G.adjoint u x) (G.adjoint u y) z=D x y (z*u) from
    fun z => by simp only [D,line,G.adjoint_mul]]
  exact integral_mul_right_eq_self (μ:=G.probHaar) (D x y) _

lemma single_color (h : G.Simple) (m : G.ColorIndex) (x : G.Color) : ∫ u, line m x u ∂G.probHaar=0 := by
  let L : G.Color →ₗ[ℝ] ℝ := {
    toFun x := ∫ u,line m x u ∂G.probHaar
    map_add' x y := by
      simp only [line,map_add,PiLp.add_apply]
      exact integral_add (phi_real (line_cont m x)) (phi_real (line_cont m y))
    map_smul' x y := by simp [line,integral_const_mul] }
  have he : L=0 := singles_inv h L fun u y => by
    change (∫ z, line m (G.adjoint u y) z ∂G.probHaar)= _
    simp_rw [line,← G.adjoint_mul]; exact integral_mul_right_eq_self (μ:=G.probHaar) (line m y) _
  exact LinearMap.congr_fun he x

lemma bit_tint (p : Flavor j) (i : G.ColorIndex) (u : G.El) (A : TaylorTower G) :
    probe A (pigment u (bit p i))=(line i (available (A j) p) u:ℂ) := by
  rw [pigment_action,bit,symbol_test,shade]
  change ((↑(available (castFace u j (A j)) p i)):ℂ)=_
  rw [shows_hue]; rfl

lemma solo (p : Probe G j) (h : G.Simple) : moyenne G (symbol j p)=0 := by
  rw [divide,map_sum]; apply Finset.sum_eq_zero; intro i _
  apply equalPol; intro A
  rw [show probe A (moyenne G _) = _ from blended _ (probe A).toLinearMap]
  change (∫ z, probe A (pigment z _) ∂G.probHaar)=_
  simp_rw [bit_tint, integral_complex_ofReal,single_color h,map_zero,Complex.ofReal_zero]

lemma duet (p : Flavor j) (q : Flavor l) (i m : G.ColorIndex) (h : G.Simple) :
    ∃ t : ℝ,moyenne G (bit p i * bit q m) = (t:ℂ) • team G p q := by
  obtain ⟨t,ht⟩ := pays_color h i m
  refine ⟨t,equalPol _ _ fun A => ?_⟩
  rw [show probe A (moyenne G _) = _ from blended _ (probe A).toLinearMap]
  change (∫ z, probe A (pigment z _) ∂G.probHaar)=_
  simp_rw [map_mul,bit_tint, ← Complex.ofReal_mul, integral_complex_ofReal, ht,map_smul,basicTeam]; push_cast; rfl

end YM.Maxwell.Free
