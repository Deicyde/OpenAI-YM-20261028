import YM.Next.MAXWELL.Covariance
import YM.Next.MAXWELL.Derives

/-!
# Genuine symmetric traceless (Wick) stress label

Construct up to **weight 4**. Tensorial even for reflections. Keep the
normalization here; Lighthouse builder may later multiply by fixed τ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open WaveOn Wick
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j l d m n : ℕ}

def phi (a b i l : Axis) : WickPol G := ∑ c : G.ColorIndex,
  symbol 0 (omegaLeg c a i)*symbol 0 (omegaLeg c b l)

def sheetEnergy (a b : Axis) : WickPol G := ∑ i : Axis, phi a b i i

def polStress (G : Gauge) (a b : Axis) : WickPol G := sheetEnergy a b -
  (((kr a b * (1/4):ℝ):ℂ)) • ∑ i : Axis, sheetEnergy i i

lemma measure_phi (a b i l : Axis) (A : TaylorTower G) :
    probe A (phi a b i l) = (⟪asWave (A 0) a i 0, asWave (A 0) b l 0⟫_ℝ : ℂ) := by
  have he (c : G.ColorIndex) (a b) : omegaLeg c a b (A 0) = asWave (A 0) a b 0 c := rfl
  unfold phi; simp_rw [map_sum,map_mul,symbol_test,he, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1; rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]; rfl

lemma measure_stress (a b : Axis) (A : TaylorTower G) : probe A (polStress G a b) =
    (((1/2 * cross (asWave (A 0)) (asWave (A 0)) a b 0 : ℝ)):ℂ) := by
  unfold polStress sheetEnergy
  simp only [map_sum,map_smul,map_sub,measure_phi,smul_eq_mul, ← Complex.ofReal_sum, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  -- Need factor through inner: real_inner_comm
  congr 1; unfold cross
  simp_rw [show ∀ i : Axis, ⟪asWave (A 0) b i 0,asWave (A 0) a i 0⟫_ℝ=⟪asWave (A 0) a i 0,asWave (A 0) b i 0⟫_ℝ from fun _ => real_inner_comm _ _,
    Finset.sum_add_distrib]
  ring

lemma stress_sym (a b : Axis) : polStress G a b = polStress G b a :=
  equalPol _ _ (by intro A; simp only [measure_stress,cross_rotate_indices _ _ a b])



lemma pol_real (a b : Axis) : realForm (polStress G a b) = polStress G a b :=
  equalPol _ _ (by intro A; rw [real_eval, measure_stress]; simp)

lemma shade_phi (a b i l : Axis) (u : G.El) : pigment u (phi a b i l)=phi a b i l := by
  apply equalPol; intro A; rw [pigment_action, measure_phi, measure_phi]
  let L : G.Color →ₗᵢ[ℝ] G.Color := ⟨G.adjoint u,G.norm_adjoint u⟩
  exact congr_arg (fun t : ℝ => (t:ℂ)) (L.inner_map_map (asWave (A 0) a i 0) (asWave (A 0) b l 0))

theorem stress_label (G : Gauge) (a b : Axis) : polStress G a b ∈ shellSector G 4 := by
  have he (a b i l) : MvPolynomial.IsWeightedHomogeneous scaleW (phi (G:=G) a b i l) 4 := by
    unfold phi; apply MvPolynomial.IsWeightedHomogeneous.sum
    intro c _; exact (symbol_hom (omegaLeg (G:=G) c a i) (fun i => i+2)).mul
      (symbol_hom (omegaLeg (G:=G) c b l) (fun i => i+2))
  have ht (a b : Axis) : sheetEnergy (G:=G) a b∈ lowerCap G 4 := by
    apply Submodule.sum_mem
    intro i _; rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]
    intro p hp; change degree p ≤ 4
    exact (he a b i i (MvPolynomial.mem_support_iff.mp hp)).le
  apply sector.mpr
  refine ⟨Submodule.sub_mem _ (ht a b) (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ht i i)),?_⟩
  intro u; simp only [polStress,sheetEnergy,map_smul,map_sum,map_sub,shade_phi]





/-- Conservation already at label level: probe its Wick derivative on
Taylor data. No need to take any limit or work modulo new nulls. -/
theorem pol_conservation (G : Gauge) (b : Axis) : ∑ a : Axis, rewired (glide G (basis a)) (polStress G a b)=0 := by
  apply equalPol; intro A
  let f : Field G.Color := asWave (A 0)+asWave (A 1)
  have hf : WaveOn univ f := wave_add (wavePoly _) (wavePoly _)
  have hp (j : ℕ) : nth f j 0 = nth (asWave (A 0)) j 0 + nth (asWave (A 1)) j 0 :=
    funext fun i => funext fun l => Tensor.coeff_add
      (((wavePoly _).smooth i l 0 (mem_univ _)).of_le (WithTop.coe_le_coe.mpr le_top))
      (((wavePoly _).smooth i l 0 (mem_univ _)).of_le (WithTop.coe_le_coe.mpr le_top))
  have h0 : nth f 0 0=(A 0).val := by rw [hp,asWave_jet,asWave_other _ (by decide),add_zero]
  have h1 : nth f 1 0=(A 1).val := by rw [hp,asWave_jet,asWave_other _ (by decide),zero_add]
  have h (a b : Axis) (c : G.ColorIndex) : omegaLeg c a b (A 0)=f a b 0 c := by
    unfold omegaLeg; rw [leg_eval,← h0,nth]; simp [Tensor.coeff_apply_zero]
  have hr (a b i : Axis) (c : G.ColorIndex) : glide G (basis i) 0 (omegaLeg c a b) (A 1)=grad i (f a b) 0 c := by
    have he := samples_D (j:=0) hf isOpen_univ (basis i) (mem_univ 0)
    let B : Solution G.Color 1 := ⟨_,hf.jets isOpen_univ (x:=0) (mem_univ _)⟩
    change omegaLeg c a b (lower _ _ _ (A 1)) = _
    rw [show A 1=B from Subtype.ext h1.symm];
    change (lower _ _ _ B).val a b _ c = _
    rw [show (lower G.Color 0 (basis i) B).val = _ from he.symm];
    simp only [nth,Tensor.coeff_apply_zero]; rfl
  let C (a i l k m : Axis) := ⟪grad a (f i k) 0,f l m 0⟫_ℝ + ⟪f i k 0,grad a (f l m) 0⟫_ℝ
  let D (a : Axis) := rewired (glide G (basis a))
  have hk (a i l k m : Axis) : probe A (D a (phi i l k m))=(C a i l k m:ℂ) := by
    have hh (x y : G.Color) : ⟪x,y⟫_ℝ = ∑ i : G.ColorIndex, x i * y i := by rw [real_inner_comm]; rfl
    simp only [D,phi,map_sum, Derivation.leibniz,smul_eq_mul,map_mul,map_add,
      rewired_symbol,symbol_test,h]
    unfold C; simp only [hr,hh,Complex.ofReal_sum,Complex.ofReal_add, Complex.ofReal_mul,
      Finset.sum_add_distrib]
    rw [add_comm]; congr 1
    exact Finset.sum_congr rfl fun c _ => mul_comm ..
  have he (a : Axis) : probe A (D a (polStress G a b))=(((1/2 * grad a (cross f f a b) 0 : ℝ)):ℂ) := by
    rw [grad, crossD (fun i l => hf.smooth i l _ (mem_univ _)) (fun i l => hf.smooth i l _ (mem_univ _)),
      ← cross_comm (fun i l => Analysis.D (basis a) (f i l)) f]
    unfold polStress sheetEnergy
    simp_rw [map_sub,Derivation.map_smul,map_sum,map_smul,hk, ← Complex.ofReal_sum, smul_eq_mul]
    simp only [map_sum,hk, ← Complex.ofReal_sum,← Complex.ofReal_mul,← Complex.ofReal_sub]
    congr 1; unfold C cross
    have ht (a i l k m) : ⟪f i l 0,grad a (f k m) 0⟫_ℝ=⟪Analysis.D (basis a) (f k m) 0, f i l 0⟫_ℝ := real_inner_comm _ _
    simp_rw [ht,Finset.sum_add_distrib,grad]; ring
  simp_rw [map_sum,map_zero]; change ∑ a : Axis, probe A (D a (polStress G a b)) = _
  simp_rw [he,← Complex.ofReal_sum, ← Finset.mul_sum, div_cross (wave_closed hf) (wave_closed hf) isOpen_univ (mem_univ _)]
  simp [divF,hf.divergence _ _ (mem_univ _)]
end YM.Maxwell.Free
