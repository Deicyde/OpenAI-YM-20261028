import YM.Next.FOUNDATIONS.SU2
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links

/-!
# Signed link action on actual equation cylinders

Use sums over **positive** links with `Packet.forward`/`derivative`
(orthonormal basis of color in the specified normalization). Everything real
before complexifying the weights. We explicitly compute the change of the
gradient and of the Haar-divergence term: ignoring dependence of the roll on
the links without proof would not work for differential claims. For now
require differentiability in the left increment chart at 0, a local finite
stencil condition, not an asymptotic estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Lattice Wilson RG NormedSpace Push.CutoffProjectors Packet
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- Weight applied to a real Color; equivalently the complex vector read in
physical left components. No conjugation. -/
def weighs (W : Vectors G n) (U : Config G n) (e : Edge (Site n)) (x : G.Color) : ℂ :=
  ∑ j, (x j : ℂ) * W U e j

lemma weighs_basis (W : Vectors G n) (U : Config G n) (e : Edge (Site n)) (j : G.ColorIndex) :
    weighs W U e (cbasis G j) = W U e j := by
  unfold weighs
  rw [Finset.sum_eq_single j] <;> simp [cbasis, EuclideanSpace.basisFun_apply]
  intro k h; simp [h]

/-- How physical link vectors `W'` (target) transform back to `W`
(pullback), written in dual form using the isometry `roll`. Includes
translation of both endpoints, negative orientations use `roll_apply`. -/
def Reorients (s : Signed) (b : Site n) (W W' : Vectors G n) :=
  ∀ U e x, weighs W' U (bonds s b e) x = weighs W (pull s b U) e (roll s b U e x)

lemma roll_transpose (R : G.Color ≃ₗᵢ[ℝ] G.Color) (i j : G.ColorIndex) :
    R (cbasis G j) i = R.symm (cbasis G i) j := by
  have he (i) (x : G.Color) : x i = inner ℝ (cbasis G i) x := (cbasis G).repr_apply_apply x i
  rw [he i, he j, ← R.symm.inner_map_map, R.symm_apply_apply, real_inner_comm]



/-- Orthogonal contraction of TWO color indices. Even for complex entries,
use the real component matrix and no implicit star. -/
lemma contract (R : G.Color ≃ₗᵢ[ℝ] G.Color) (A : G.ColorIndex → G.ColorIndex → ℂ) :
    let r := fun i j => (R (cbasis G j) i : ℂ)
    ∑ j, ∑ k, r k j * ∑ l, r l j * A k l = ∑ k, A k k := by
  intro r
  have hh (k l) : ∑ j, r k j * r l j = if k=l then (1:ℂ) else 0 := by
    have he (x y : G.Color) : inner ℝ x y = ∑ j, x j * y j := by rw [PiLp.inner_apply]; simp [mul_comm]
    have hp : ∑ j, R (cbasis G j) k * R (cbasis G j) l = if k=l then (1:ℝ) else 0 := by
      simp only [roll_transpose R]
      rw [← he, R.symm.inner_map_map, he]
      simp [cbasis,EuclideanSpace.basisFun_apply,eq_comm]
    simp only [r, ← Complex.ofReal_mul, ← Complex.ofReal_sum,hp]; split <;> simp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  simp_rw [Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hh]; simp

section Smooth
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Exact sufficient finite smoothness gate for the direction calculation;
paths of ordinary link reads, with differentiated color coefficients in the
actual left chart. -/
def Slopes (f : Config G n → Y) := ∀ U, DifferentiableAt ℝ (fun A => f (increment U A)) 0

lemma Slopes.variation {f : Config G n → Y} (h : Slopes f) (U : Config G n) (e : Edge (Site n)) (x : G.Color) :
    HasDerivAt (fun t : ℝ => f (increment U (t • single e x))) (∑ j, x j • derivative f e j U) 0 := by
  let L := fderiv ℝ (fun A => f (increment U A)) 0
  have hd (A : Directions G n) : HasDerivAt (fun t : ℝ => f (increment U (t • A))) (L A) 0 := by
    let p (t : ℝ) := t • A
    have he : HasDerivAt p A 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const A
    apply HasFDerivAt.comp_hasDerivAt (f:=p) (l:=fun B => f (increment U B)) _ _ he
    rw [show p 0 = 0 by simp [p]]; exact (h U).hasFDerivAt
  have hj j : derivative f e j U = L (forward e j) := (hd (forward e j)).deriv
  rw [show ∑ j, x j • derivative f e j U = L (single e x) by
    simp_rw [hj, ← map_smul L]; rw [← map_sum]
    congr 1
    let Q := LinearMap.single ℝ (fun _ : Edge (Site n) => G.Color) e
    change ∑ j, x j • Q (cbasis G j) = Q x
    simp_rw [← map_smul Q]; rw [← map_sum, show ∑ j, x j • cbasis G j = x from (cbasis G).sum_repr x]]
  exact hd _



/-- In particular the Wilson energy (no prior assumption on the history). -/
lemma energy_slopes : Slopes (energy (n:=n) (G:=G)) := by
  intro U
  -- The smoothness can be checked directly in increment coordinates.
  have hm (e : Edge (Site n)) : ContDiff ℝ ω (fun A : Directions G n => G.mat ((increment U A) e)) :=
    (G.exp_jet.comp (contDiff_apply ℝ G.Color e)).mul contDiff_const
  have hr (w : Walk) (x : Site n) : ContDiff ℝ ω (fun A : Directions G n => G.mat (travel (increment U A) x w)) := by
    induction w generalizing x with
    | nil => exact contDiff_const
    | cons d w ih =>
      have he : ContDiff ℝ ω (fun A : Directions G n => G.mat (d.read (increment U A) x)) := by
        unfold Step.read; split
        · exact (starL' ℝ (A:=G.Mat)).toContinuousLinearMap.contDiff.comp (hm _)
        exact hm _
      exact he.mul (ih _)
  let L : G.Mat →ₗ[ℝ] ℝ := {
    toFun V := V.trace.re / G.repDim
    map_add' _ _ := by simp [add_div]
    map_smul' _ _ := by simp; ring }
  have he : ContDiff ℝ ω (fun A : Directions G n => energy (increment U A)) := by
    unfold energy
    refine ContDiff.sum fun i _ => contDiff_const.sub ?_
    exact L.toContinuousLinearMap.contDiff.comp (hr _ _)
  exact he.differentiable (by simp) _

end Smooth

namespace Reorients
variable {s : Signed} {b : Site n} {W W' : Vectors G n}

lemma scene (s : Signed) (b : Site n) (U : Config G n) (e : Edge (Site n)) (x : G.Color) (t : ℝ) :
    pull s b (increment U (t • single (bonds s b e) x)) =
      increment (pull s b U) (t • single e (roll s b U e x)) := by
  rw [pull_increment,map_smul,pull_single]

lemma gradient (s : Signed) (b : Site n) (U : Config G n) (e : Edge (Site n)) (j : G.ColorIndex) :
    Packet.derivative energy (bonds s b e) j U =
      ∑ k, roll s b U e (cbasis G j) k * derivative energy e k (pull s b U) := by
  change deriv (fun t : ℝ => energy (increment U (t • forward (bonds s b e) j))) 0 = _
  let x := cbasis G j
  rw [show (fun t : ℝ => energy (increment U (t • forward (bonds s b e) j))) =
      (fun t : ℝ => energy (increment (pull s b U) (t • single e (roll s b U e x)))) by
        funext t; rw [← scene, energy_pull]; rfl]
  exact (energy_slopes.variation _ e (roll s b U e x)).deriv

/-- Divergence component in TARGET coordinates. The identity of functions in
the proof is why it is possible to take this derivative (only because the
variation and the component use the same j). Thus includes the possible
link-dependence of W inside transports, filters etc. -/
lemma diagonal (H : Reorients s b W W') (h : ∀ e j, Slopes (fun U => W U e j))
    (U : Config G n) (e : Edge (Site n)) (j : G.ColorIndex) :
    Packet.derivative (fun V => W' V (bonds s b e) j) (bonds s b e) j U =
      ∑ k, (roll s b U e (cbasis G j) k : ℂ) *
        ∑ l, (roll s b U e (cbasis G j) l : ℂ) * derivative (fun V => W V e k) e l (pull s b U) := by
  let q := bonds s b e
  let x := cbasis G j
  let c := roll s b U e x
  let V (t : ℝ) := increment (pull s b U) (t • single e c)
  have he (t : ℝ) : W' (increment U (t • single q x)) q j = ∑ k, (c k : ℂ) * W (V t) e k := by
    let B := t • single q x
    change W' (increment U B) q j = _
    rw [← weighs_basis W' (increment U B) q j, H (increment U B) e (cbasis G j)]
    have hp : roll s b (increment U B) e x = c := by
      have hh := roll_increment s b U (single q x) e t
      simpa only [q,single,Pi.single_eq_same] using hh
    change weighs W _ e (roll s b (increment U B) e x) = _
    rw [hp, show pull s b (increment U B)=V t from scene s b U e x t]; rfl
  change deriv (fun t : ℝ => W' (increment U (t • single q x)) q j) 0 = _
  simp_rw [he]
  apply HasDerivAt.deriv
  refine HasDerivAt.fun_sum fun k _ => HasDerivAt.const_mul (c k : ℂ) ?_
  simpa only [Complex.real_smul,smul_eq_mul] using (h e k).variation (pull s b U) e c

end Reorients

/-- The  expression as used in `Packet.Jorigin` (caller inserts the
slot-rescaled weights). -/
def ward (a β : ℝ) (d : ℕ) (W : Vectors G n) (U : Config G n) : ℂ :=
  ((a : ℂ)^d)⁻¹ * ∑ e, ∑ j, (W U e j * (derivative energy e j U : ℝ) -
      ((β : ℂ))⁻¹ * derivative (fun V => W V e j) e j U)

lemma ward_roll (a β : ℝ) (d : ℕ) (s : Signed) (b : Site n) {W W' : Vectors G n}
    (H : Reorients s b W W') (h : ∀ e j, Slopes (fun U => W U e j)) (U : Config G n) :
    ward a β d W' U = ward a β d W (pull s b U) := by
  unfold ward
  conv_lhs => rw [← Equiv.sum_comp (bonds s b)]
  apply congr_arg _; refine Finset.sum_congr rfl fun e _ => ?_
  let V := pull s b U
  let q := bonds s b e
  let r := fun k j => (roll s b U e (cbasis G j) k : ℂ)
  have ht : ∑ j, derivative (fun V => W' V q j) q j U = ∑ j, derivative (fun V => W V e j) e j V := by
    dsimp only [q]
    simp_rw [H.diagonal h U e]
    exact contract (roll s b U e) (fun k l => derivative (fun V => W V e k) e l V)
  have hk (j) : W' U q j = ∑ k, r k j * W V e k :=
    (weighs_basis _ _ _ _).symm.trans (H U e _)
  let M (j : G.ColorIndex) := ((derivative energy e j V : ℝ) : ℂ)
  have hr (j) : ((derivative energy q j U : ℝ) : ℂ) = ∑ k, r k j * M k := by
    unfold q; rw [Reorients.gradient]; push_cast; rfl
  have hg : ∑ j, W' U q j * (derivative energy q j U : ℝ) = ∑ j, W V e j * M j := by
    simp_rw [hk,hr]
    convert contract (roll s b U e) (fun k l => W V e k * M l) using 1
    simp only [r,Finset.mul_sum,Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]; rw [hg,ht]

lemma ward_star (a β : ℝ) (d : ℕ) (W : Vectors G n) (h : ∀ e j, Slopes (fun U => W U e j)) (U : Config G n) :
    ward a β d (star W) U = star (ward a β d W U) := by
  have he (e : Edge (Site n)) (j) : derivative (fun V => star (W V e j)) e j U =
      star (derivative (fun V => W V e j) e j U) := by
    have hp := (h e j).variation U e (cbasis G j)
    exact hp.star.deriv.trans (congr_arg star hp.deriv.symm)
  simp only [ward,Pi.star_apply, star_sum,star_mul,star_inv₀,star_pow,star_sub,he]
  simp [mul_comm]
end YM.ProjectorNext.Equivariance
