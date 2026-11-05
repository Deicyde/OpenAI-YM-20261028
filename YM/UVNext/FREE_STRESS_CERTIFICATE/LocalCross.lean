import YM.UVNext.FREE_STRESS_CERTIFICATE.Melt

/-! Algebra and integrability of cross stress, in one color. Smooth
conservation assertion away from the far pole (χ compact disjoint) holds
including origin at each REGULARIZED scale. No products of distributions. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Set MeasureTheory Filter Analysis
open scoped Topology ContDiff

def crossing (x y : Axis→Axis→ℝ) (a b : Axis) :=
    (∑ c, (x a c*y b c + x b c*y a c)) - (if a=b then (1/2:ℝ)*∑ i, ∑ c, x i c*y i c else 0)

private lemma swap_cross (x y : Axis→Axis→ℝ) (a b : Axis) : crossing x y a b=crossing y x a b := by
  unfold crossing; congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · split_ifs
    · congr 1; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rfl

private lemma comb (X : Axis→Axis→Axis→ℝ) (y : Axis→Axis→ℝ)
    (hy : ∀ a c,y a c= -y c a) (hX : ∀ a b c,X a b c= -X a c b)
    (h : ∀ a b c, X a b c + X b c a + X c a b = 0) (b : Axis) :
    ∑ a, crossing (X a) y a b = ∑ c, (∑ a, X a a c) * y b c := by
  unfold crossing
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib,Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
    Finset.sum_comm (f:=fun a c => X a a c * y b c)]
  simp_rw [Finset.sum_mul];
  let R := ∑ a : Axis, ∑ c : Axis, X a b c * y a c
  let T := ∑ i : Axis, ∑ c : Axis, X b i c * y i c
  have hr : R=T-R := by
    have he (a c) : X a b c=X b a c-X c a b := by
      have hh := h a b c; rw [hX b c a] at hh; linarith
    unfold R T
    conv_lhs => arg 2; intro a; arg 2; intro c; rw [he,sub_mul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f:=fun c a => X b a c*y a c)]; congr 1
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [hy a c,hX c a b]; ring
  linarith

private lemma diff_cross (x y : Maxwell.Field ℝ) (r a b : Axis) {z : E4} (hx : ∀ a b, DifferentiableAt ℝ (x a b) z)
    (hy : ∀ a b,DifferentiableAt ℝ (y a b) z) :
    grad r (fun z => crossing (fun i j => x i j z) (fun i j => y i j z) a b) z =
      crossing (fun i j => grad r (x i j) z) (fun i j => y i j z) a b +
      crossing (fun i j => x i j z) (fun i j => grad r (y i j) z) a b := by
  let prod (a b i j : Axis) := fun z : E4 => x a b z*y i j z
  have h (a b i j : Axis) : DifferentiableAt ℝ (prod a b i j) z := (hx _ _).mul (hy _ _)
  have hh (a b c i j : Axis) : fderiv ℝ (prod a b i j) z (basis c) =
      grad c (x a b) z * y i j z + x a b z * grad c (y i j) z := by
    dsimp only [prod]; rw [fderiv_fun_mul (hx _ _) (hy _ _)]
    simp [grad,D,mul_comm,add_comm]
  unfold crossing grad D
  let f (a b c) := fun z => prod a c b c z+prod b c a c z
  have he (c : Axis) : DifferentiableAt ℝ (f a b c) z := (h _ _ _ _).add (h _ _ _ _)
  let g (i c) := prod i c i c
  let G := fun z => ∑ i : Axis, ∑ c : Axis, g i c z
  have ht (i : Axis) : DifferentiableAt ℝ (fun z => ∑ c : Axis,g i c z) z := DifferentiableAt.fun_sum fun c _ => h _ _ _ _
  have H : DifferentiableAt ℝ G z := DifferentiableAt.fun_sum fun i _ => ht _
  let P : E4→ℝ := if a=b then fun z => (1/2) * G z else 0
  have hp : DifferentiableAt ℝ P z := by unfold P; split; exact H.const_mul _; exact differentiableAt_const (𝕜:=ℝ) (x:=z) _
  rw [show (fun z => (∑ c : Axis, (x a c z*y b c z+x b c z*y a c z)) -
      (if a=b then (1/2:ℝ)*∑ i, ∑ c : Axis, x i c z*y i c z else 0)) = (fun z => (∑ c : Axis, f a b c z) - P z) from
        by unfold P; split <;> simp_all [f,prod,G,g], fderiv_fun_sub (DifferentiableAt.fun_sum fun i _ => he i) hp]
  simp_rw [_root_.sub_apply, fderiv_fun_sum (fun i _ => he i),_root_.sum_apply, f]
  have hd (c : Axis) := fderiv_fun_add (h a c b c) (h b c a c)
  simp_rw [hd,_root_.add_apply,hh]
  unfold P; split_ifs
  · rw [fderiv_const_mul H]; unfold G
    simp_rw [fderiv_fun_sum (fun i _ => ht i), _root_.smul_apply,_root_.sum_apply, g,fderiv_fun_sum (fun i _ => h _ i _ i),_root_.sum_apply,hh,grad,D,smul_eq_mul, Finset.sum_add_distrib]
    ring
  rw [fderiv_zero]; simp only [Pi.zero_apply,_root_.zero_apply,grad,D,sub_zero,Finset.sum_add_distrib]; ring

section OnPatch

variable (r : ℝ) {U : Set E4} (u : Maxwell.Field ℝ) (hu : WaveOn U u)

def score (r : ℝ) (u : Maxwell.Field ℝ) (i j a b : Axis) (z : E4) :=
    crossing (fun a b => material r i j a b z) (fun a b => u a b z) a b

include hu in
lemma score_smooth (k i a b : Axis) {z : E4} (hz : z ∈ U) (h : r ≠ 0 ∨ z ≠0) :
    ContDiffAt ℝ ∞ (score r u k i a b) z := by
  unfold score crossing
  have ht (a b c d) : ContDiffAt ℝ ∞ (fun z => material r k i a b z * u c d z) z :=
    (material_smooth r z h k i a b).mul (hu.smooth c d z hz)
  have hh : ContDiffAt ℝ ∞ (fun z => (1/2:ℝ)*∑ m, ∑ c, material r k i m c z*u m c z) z :=
    contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun c _ => ht _ _ _ _)
  apply (ContDiffAt.sum fun c _ => (ht a c b c).add (ht b c a c)).sub
  by_cases h : a=b
  · simpa only [if_pos h] using hh
  simp only [if_neg h]; exact contDiffAt_const

include hu in
lemma score_div (ho : IsOpen U) {z : E4} (hz : z ∈ U) (hr : r ≠ 0) (i j b : Axis) :
    ∑ a, grad a (score r u i j a b) z = grad i (droplet r) z * u b j z - grad j (droplet r) z * u b i z := by
  have hm (a b) := (material_smooth r z (Or.inl hr) i j a b).differentiableAt (by simp)
  have hw (a b) := (hu.smooth a b z hz).differentiableAt (by simp)
  simp_rw [show ∀ a : Axis, grad a (score r u i j a b) z = _ from fun a => diff_cross (material r i j) u a a b hm hw,Finset.sum_add_distrib]
  have hM (a b c : Axis) : grad a (material r i j b c) z = -grad a (material r i j c b) z := by
    unfold grad D
    nth_rw 1 [show material r i j b c= -material r i j c b from funext fun x => material_odd ..]
    rw [fderiv_neg]; rfl
  have hQ (a b c : Axis) : grad a (u b c) z = -grad a (u c b) z := by
    have he : u b c =ᶠ[𝓝 z] -u c b := by filter_upwards [ho.mem_nhds hz] with y hy; exact hu.form b c y hy
    rw [grad,GermD _ he,D,fderiv_neg]; rfl
  have hs := comb (fun a b c => grad a (u b c) z) (fun a b => material r i j a b z) (fun a c => material_odd ..) hQ (fun a b c => hu.cycle a b c z hz) b
  simp_rw [swap_cross (fun a b => material r i j a b z),hs,hu.divergence _ z hz,zero_mul,Finset.sum_const_zero,add_zero]
  have ht := comb (fun a b c => grad a (material r i j b c) z) (fun a b=>u a b z) (fun a c => hu.form a c z hz) hM (material_cycle r z (Or.inl hr) i j) b
  rw [ht]
  simp [material_div r z hr, ite_mul, sub_mul, Finset.sum_sub_distrib]

end OnPatch
end YM.UVNext.FreeStress
