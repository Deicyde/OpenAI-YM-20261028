import YM.TraceExtension.Foundation.Caps
import YM.Push.STRESS_FLUX.FreeTests

set_option autoImplicit false
noncomputable section
namespace YM.Trace
open StressFlux Labels Gauge Maxwell Tensor Analysis Function Set Submodule
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {G : Gauge}

private lemma Bianchi (v : Taylor G 1) (a b c : Axis) : curl1 a b c v + curl1 b c a v + curl1 c a b v = 0 := by
  simp only [← curl_degree_one v _ _ _ 0]; exact ((potential v).property.closed a b c 0)
private lemma skew0 (a b c i j) : pairDeriv G a b c i j = -pairDeriv G b a c i j := by
  apply label_ext; intro J; change _=read J (-_); rw [map_neg,pairDeriv_value,pairDeriv_value,show curl0 a b (J 0) = -curl0 b a (J 0) from curled_swap ..]; simp
private lemma skew1 (a b c i j) : pairDeriv G a b c i j = -pairDeriv G a b c j i := by
  apply label_ext; intro J; change _=read J (-_); rw [map_neg,pairDeriv_value,pairDeriv_value,show curl1 c i j (J 1) = -curl1 c j i (J 1) from curled_swap ..]; simp
private lemma triple (a b k i j) : pairDeriv G a b k i j + pairDeriv G a b i j k + pairDeriv G a b j k i = 0 := by
  apply label_ext; intro J
  simp only [coe_add, coe_zero,map_add,pairDeriv_value, map_zero,← Complex.ofReal_add,← inner_add_right]; rw [Bianchi]; simp
private lemma tripleSum (b : Axis) : (∑ a, ∑ i, pairDeriv G a i a b i) = (1/2:ℝ) • momentum2 G b := by
  let s : Axis→Axis→Label G 5 := fun a i=> pairDeriv G a i a b i
  have he (a i) : s a i + s i a = pairDeriv G a i b a i:= by
    have h:= triple (G:=G) a i a b i; rw [skew1 a i b,← sub_eq_add_neg] at h
    change pairDeriv .. + _=_; dsimp only [s]; rw [skew0 i, skew1 a i i b a]; linear_combination (norm:=abel) h
  have hv :(∑ a, ∑ i, s a i) + (∑ i, ∑ a, s a i)=momentum2 G b := by
    rw [← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib,he]; rfl
  rw [Finset.sum_comm (f:=fun i a=>s a i), ← two_smul ℝ] at hv; rw [← hv,smul_smul]; norm_num; rfl

/-- Continuum Taylor divergence of the centered stress tensor letters (unit discarded).
Input `(diagonal-mountain, diagonal-total, shear)`. -/
private abbrev proj3 (i : Fin 3) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
private def mat3 : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3→ℝ := LinearMap.pi ![(2:ℝ) • (proj3 0 - proj3 2), (2:ℝ) • proj3 1+(1/2:ℝ) • proj3 2,proj3 2]
def bareVector : (Fin 3→ℝ) →ₗ[ℝ] RawOne G := basisV ∘ₗ mat3
lemma bareVector_coords (w : Fin 3→ℝ) : bareVector (G:=G) w = basisV ![2*(w 0-w 2),2*w 1+1/2*w 2,w 2] := by
  have h : mat3 w=![2*(w 0-w 2),2*w 1+1/2*w 2,w 2] := by funext i; fin_cases i <;> rfl
  exact congr_arg (basisV (G:=G)) h

lemma euler (w : Fin 3 → ℝ) (b : Axis) : (bareVector (G:=G) w).val b =
    (w 0 • ∑ i : Axis,(pairDeriv G b i b b i + pairDeriv G b i b b i)) +
    (w 1 • ∑ a, ∑ i : Axis,(pairDeriv G a i b a i+ pairDeriv G a i b a i))+
    (w 2 • ∑ a ∈ Finset.univ.erase b, ∑ i : Axis,(pairDeriv G b i a a i+pairDeriv G a i a b i)) := by
  classical
  rw [bareVector_coords,basisV_apply]
  change (2*(w 0-w 2)) • momentum1 G b + (2*w 1+1/2*w 2) • momentum2 G b+w 2 • eom G b = _
  let t (a i : Axis):=pairDeriv G b i a a i+pairDeriv G a i a b i
  have he : (∑ a ∈ Finset.univ.erase b, ∑ i : Axis,t a i) = eom G b + (1/2:ℝ) • momentum2 G b-(2:ℝ) • momentum1 G b:= by
    apply eq_sub_of_add_eq
    rw [two_smul ℝ, show momentum1 G b + momentum1 G b=∑ i : Axis,t b i from (Finset.sum_add_distrib ..).symm, Finset.sum_erase_add _ _ (Finset.mem_univ b)]
    unfold t; simp_rw [Finset.sum_add_distrib]; rw [tripleSum, Finset.sum_comm (f:=fun a i=>pairDeriv G b i a a i)]; rfl
  rw [he]; simp_rw [Finset.sum_add_distrib]; change _=w 0 • (momentum1 G b+ _) + w 1 • (momentum2 G b+_)+_
  change _=w 0 • (momentum1 G b+ momentum1 G b) + w 1 • (momentum2 G b+momentum2 G b)+_
  module

lemma bareCoordinates (h : G.Simple) : Bijective (bareVector (G:=G)) := by
  obtain ⟨hX,hy⟩:= coordinates1 h
  refine ⟨?_,?_⟩
  · intro v w hv; rw [bareVector_coords,bareVector_coords] at hv; apply hX at hv; funext i
    have h : v 2=w 2:=congr_fun hv 2; fin_cases i
    · change v 0=w 0; linarith only [h,(show 2*(v 0-v 2)=2*(w 0-w 2) from congr_fun hv 0)]
    · change v 1=w 1; linarith only [h,(show 2*v 1+1/2*v 2=2*w 1+1/2*w 2 from congr_fun hv 1)]
    exact h
  rintro v; obtain ⟨y,rfl⟩:= hy v
  refine ⟨![y 0/2+y 2,y 1/2-y 2/4,y 2],?_⟩; rw [bareVector_coords]; apply congr_arg; funext i; fin_cases i <;> simp <;> ring

/-- `1/4` of the sum over *ordered* axes, adjoint color contraction. -/
def square4 (G : Gauge) : Label G 4:= (1/4:ℝ) • ∑ i, ∑ j, pair G i j i j
lemma mechanical_trace (w : Fin 3 → ℝ) : (∑ a, stress G (Fin.cons 0 w) a a) =
    (4*(w 0+4*w 1)) • square4 G:= by
  simp [stress_of]; rw [Finset.sum_add_distrib, ← Finset.smul_sum,Finset.sum_const]; change _+(4:ℕ) • (w 1 • _)=_; unfold square4; module
abbrev raw (G : Gauge) := stress G weyl
lemma conformal (G : Gauge) : (∑ a, raw G a a)=0:= by
  unfold raw; rw [show weyl=Fin.cons (α:=fun _=>ℝ) 0 (![1,-1/4,1] : Fin 3→ℝ) from rfl,mechanical_trace]; norm_num
lemma eom_vector_raw : (bareVector (G:=G) ![1,-1/4,1]).val=eom G:= by
  funext a; rw [bareVector_coords,basisV_apply]; change (2*(1-1):ℝ) • _+(2*(-1/4)+1/2*1:ℝ) • _+(1:ℝ) • eom G a=eom G a; norm_num

/-- Dilation contraction on polar divergences. This is the scalar annihilator of
traceless spin and the Maxwell equation; it reads minus the trace, in square units. -/
def rho (h : G.Simple) : RawOne G →ₗ[ℝ] ℝ :=
  ((-4:ℝ) • (LinearMap.proj (0:Fin 3)+(4:ℝ) • LinearMap.proj (1:Fin 3))) ∘ₗ
       (LinearEquiv.ofBijective bareVector (bareCoordinates h)).symm.toLinearMap
lemma rho_vector (h : G.Simple) (w : Fin 3 → ℝ) : rho h (bareVector w)= -4*(w 0+4*w 1) := by
  let L:=LinearEquiv.ofBijective (bareVector (G:=G)) (bareCoordinates h)
  change -4*(L.symm (L w) 0 + 4*L.symm (L w) 1) = _
  rw [L.symm_apply_apply]
lemma rho_eom (h : G.Simple) (v : RawOne G) (hv : ∀ b, v.val b∈equationIdeal G 5) : rho h v=0:=by
  obtain ⟨w,rfl⟩:= (bareCoordinates h).surjective v
  rw [rho_vector]; simp_rw [bareVector_coords] at hv
  obtain ⟨h₁,h₂⟩:= (through_eq _ h).mp hv; change 2*(w 0-w 2)=0 at h₁; change 2*w 1+1/2*w 2=0 at h₂; linarith
end YM.Trace
