import YM.Planned.PRIMARY_INTEGRAL_295.Porous

/-! # Operate cost at a single local chart with moving Gaussian register

All exponents explicit. t+ξ+s, NOT assuming emitted errors already.
Charts call at arbitrary k. Norm comparison excludes physically silent
Z in the unnormalized marginal. `ρ` still on absolute x (standardized)
with all derivatives accounted for. No claims about LARGE field weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Porous
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {S : Finset Cover} {k l : ℕ} {t ξ s M : ℝ}

lemma financed (B : Roof S G) (k:ℕ) : 1 ≤ rootPrice B k := (Seas.expenseLog.{0,0,0}
    (archL S G) B.stitch B.smooth B.launch B.rule k B.radius).choose_spec.1

def creep (k : ℕ) := k+2
-- common auxiliary scale C_*, polynomial post-L M>=1 uniform in k of all budgets

def oasis (B : Roof S G) (k : ℕ) (M : ℝ) := rootPrice B k * (3*M^2)^(creep k) + M + ‖archL S G‖ * M^2

def ore (B : Roof S G) (k : ℕ) (M t ξ s : ℝ) (x : Sky I) := (t+ξ+s)*oasis B k M * breath x^(creep k)

lemma oasis_gold (B : Roof S G) (k : ℕ) (hp : 1≤M) : 1≤oasis B k M := by
  have he:=financed B k; have h1 := mul_nonneg (zero_le_one.trans he) (show 0≤(3*M^2)^(creep k) by positivity);
  unfold oasis; linarith [show 0 ≤ ‖archL S G‖ * M^2 by positivity]

namespace Stand
variable (h : Stand I E S G) (B : Roof S G) {Q:E→Dev S G} (hc : h.Calls B Q t ξ s k M)
include hc

lemma ore_nonneg (x : Sky I) : 0≤ore B k M t ξ s x := by
  have ht:=hc.rate.1; have hh:=hc.noise.1; have hv:=hc.error.1; have hp:=oasis_gold B k hc.paid
  unfold ore; have he:=breath_ge x; positivity

-- ∂^n of *nonlinear* contour term, with gain t irrespective of
-- order n≤k, FDB truly normalized. Compare to Q (lower-level not W).
theorem gem (x : Sky I) (hx : Purse.Present (h.rho x) 0 k) :
    ‖t • h.skyW B ξ t x 0‖ ≤ 1 ∧ Oval.Fuzz 0 k (h.skyW B ξ t x) Q (ore B k M t ξ s x) := by
  classical
  let f:=h.skyW B ξ t x
  let V:=h.bed ξ x; let L:=archL S G
  have he : ‖t • V 0‖ ≤ B.radius := mem_of_mem_nhds (h.tent_whenever B hc (s:=s) (M:=M)) x (within h B hc x hx)
  have ht := hc.rate.1
  constructor
  · unfold skyW; rw [smul_inv_smul₀ ht.ne']; exact (B.supported _ he).2
  obtain ⟨hg,hU⟩:= h.bed_cost B hc x
  have hw := h.W_clean B hc x
  have hv : Oval.Fuzz 0 k f (L ∘ V) (t*rootPrice B k*(1+(2*M^2*breath x))^(2+k)) := by
    have hx := (Seas.expenseLog.{0,0,0} (archL S G) B.stitch B.smooth B.launch B.rule k B.radius).choose_spec.2 (0:E) V hg _ hU t hc.rate he
    refine (Seas.fuzzy (f:=f) hw (L.contDiff.contDiffAt.comp _ hg) _).1 hx
  let p (x' : E) := ξ • h.breeze (h.square x' x)
  obtain ⟨hc',hq⟩:=h.passing B hc x
  let g:E→Dev S G:= L ∘ h.det
  have hy : Oval.Fuzz 0 k (L ∘ V) g (‖L‖*(M^2*ξ*‖x‖)) := by
    have ht : L ∘ V - g = L ∘ p := by funext x; change L (h.det x+_)-L _=L _; rw [map_add]; abel
    refine (Seas.fuzzy (L.contDiff.contDiffAt.comp _ hg) (L.contDiff.contDiffAt.comp _ hc.serve.1) _).1
      (ht.symm ▸ Seas.paidLinear L hc' hq (le_refl _))
  have Hm:=hc.paid; have hz:=hc.noise.1; have hu:=hc.error.1
  let r:=breath x; have hP:1≤r:=breath_ge x; let C:=rootPrice B k; have hC:1≤C:=financed B k
  have hf : t*C*(1+(2*M^2*r))^(2+k) ≤ t*C*(3*M^2)^(creep k)*r^(creep k) := by
    rw [mul_assoc (t*C),←mul_pow,show 2+k=creep k from Nat.add_comm ..]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity); nlinarith only [one_le_mul_of_one_le_of_one_le (one_le_pow₀ Hm (n:=2)) hP]
  have hx' : ‖x‖ ≤ r^(creep k) := (show ‖x‖≤r from le_add_of_nonneg_left zero_le_one).trans
    (le_self_pow₀ hP (by simp [creep]))
  refine ⟨ore_nonneg h B hc x,fun n hn=>?_⟩
  have hs z z' a b : ‖z-b‖ ≤ ‖z-z'‖ +(‖z'-a‖+‖a-b‖) :=
    (@norm_sub_le_norm_sub_add_norm_sub (Tensor.T E (Dev S G) n) _ z z' b).trans (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub z' a b) _)
  change ‖iteratedFDeriv ℝ n f _ - iteratedFDeriv ℝ n Q _‖ ≤ _
  apply (hs ..).trans ((add_le_add ((hv.2 n hn).trans hf) (add_le_add (hy.2 n hn) (hc.go.2 n hn))).trans ?_)
  let a := C*(3*M^2)^(creep k); let b := ‖L‖*M^2; let z:=r^(creep k)
  have hZ:1≤z:=one_le_pow₀ hP
  have hB:0≤b:=mul_nonneg (norm_nonneg _) (by positivity); have hA:=show 0≤a by unfold a; positivity
  unfold ore oasis; calc
   _ ≤ (t*a + ξ*b + M*s)*z := by
     have he : b*ξ*‖x‖ ≤ b*ξ*z:=mul_le_mul_of_nonneg_left hx' (by positivity : 0 ≤ b*ξ)
     have hs := le_mul_of_one_le_right (show 0 ≤ M*s by positivity) hZ
     unfold z a b at *; linarith only [he,hs]
   _ ≤ (t+ξ+s)*(a+M+b)*z := by apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith only [mul_nonneg ht.le (zero_le_one.trans Hm),mul_nonneg ht.le hB,mul_nonneg hz.le (zero_le_one.trans Hm),mul_nonneg hz.le hA,mul_nonneg hu hA,mul_nonneg hu hB]
   _ = _ := rfl

end Stand
end YM.Planned.PrimaryIntegral295.Porous
