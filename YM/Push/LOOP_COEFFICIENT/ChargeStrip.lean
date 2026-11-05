import YM.Push.LOOP_COEFFICIENT.Charged
import YM.Push.LOOP_COEFFICIENT.LogKernel

/-!
# Passage to a period-limit in the charge test

These strip hypotheses can be at *fixed* L (the identities sought
from this test are not uniform analytic bounds on the charge).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Bloch Laurent Lattice
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {n : Side} {m k a d : Type} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k] [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a]
    {η C : ℝ} {U V : Vertex a d d}

structure ChargeStrip (V : Vertex a d d) (η C : ℝ) : Prop where
  width : 0 < η
  lit : Lit V η
  one q p v : q∈Tube η → p∈ Tube η → (∀ i, ‖v i‖ ≤ 1) → ‖V.one q p v‖ ≤ C
  two q p s v w : q∈Tube η → p∈ Tube η → s∈Tube η → (∀ i, ‖v i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) → ‖V.two q p s v w‖ ≤ C

structure Integrand (f : Momentum → Momentum → ℂ) (η C : ℝ) : Prop where
  width : 0 < η
  smooth p q : p∈Tube η → q∈Tube η → ContDiffAt ℂ ω (uncurry f) (p,q)
  norm_le p q : p∈Tube η → q∈Tube η → ‖f p q‖ ≤ C
  periodic p q x : p∈Tube η → q∈Tube η → f p (q+reciprocal x) = f p q

namespace Integrand
variable {f : CSpace a → CSpace a → Momentum → Momentum → ℂ} (h : ∀ i j, Integrand (f (Pi.single i 1) (Pi.single j 1)) η C)
include h
lemma smooth_mean {p : Momentum} (hp : p∈ Tube η) : ContDiffAt ℂ ω (kernelOf f) p :=
  analyticMatrix fun i j => boxMean_smooth ((Work.F07.stripOpen _).mem_nhds hp) fun x hx k => (h i j).smooth x _ hx (radians_strip k (h i j).width)

omit [DecidableEq m] [Fintype a] in
lemma compare {A : Grid n m a} {M : Matrix m m ℂ}
    (he : ∀ k q : Site n, ∀ p, Matches p q → ∀ i j,sample A A M k q i j = if k+q=0 then meshMean n (f (Pi.single i 1) (Pi.single j 1) p) else 0) :
    Compares A A M (kernelOf f) (C*(2*((1+η/4)/(η/4)))^4 * Real.exp (-(η/4)*n.val)) := by
  constructor
  · intro k q hk; ext i j; rw [he k q (mon q) (mon_matches q),if_neg hk]; rfl
  intro p q hp i j
  rw [he _ q p hp,if_pos (neg_add_cancel q)]
  have hi := h i j
  have hP := Work.F07.realStrip _ hi.width hp.bar
  have hv : Vane (f (Pi.single i 1) (Pi.single j 1) p) η := ⟨hi.width,fun _ hx => ((hi.smooth p _ hP hx).comp (f:=fun q => (p,q)) _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp),fun _ hq x => hi.periodic _ _ x hP hq⟩
  exact mesh_error n hv (fun x hx => hi.norm_le p x hP hx) (by linarith [hi.width]) (by linarith [hi.width]) (by linarith [hi.width])
end Integrand

namespace ChargeStrip
variable (h : ChargeStrip V η C)
include h
omit [Fintype a] in
lemma resp (i j : a) : Integrand (respTrace V (Pi.single i 1) (Pi.single j 1)) η (Fintype.card d * C) := by
  constructor
  · exact h.width
  · intro p q hp hq; exact analyticTrace (h.lit.twoD (x:=(p,q)) contDiffAt_snd (p:=fun x => -x.1) contDiffAt_fst.neg contDiffAt_fst hq (tube_neg hp) hp ..)
  · intro p q hp hq; exact (trace_norm _).trans (mul_le_mul_of_nonneg_left (h.two q _ _ _ _ hq (tube_neg hp) hp (LogStrip.single_bounded _) (LogStrip.single_bounded _)) (by positivity))
  · intro p q x hp hq; simpa only [respTrace,reciprocal_zero,add_zero] using! congr_arg Matrix.trace ((h.lit.two _ _ _ (Pi.single i 1) (Pi.single j 1) hq (tube_neg hp) hp).2 x 0 0)

omit [Fintype a] in
lemma rev (i j : a) : Integrand (reverseTrace V (Pi.single i 1) (Pi.single j 1)) (η/2) (Fintype.card d * C^2) := by
  have hη := h.width; have hs := tube_mono (show η/2 ≤ η by linarith)
  have h₁ {p q : Momentum} (hp : p∈Tube (η/2)) (hq : q∈Tube (η/2)) := tube_mono (show _ ≤ η by linarith : η/2+η/2≤η) (tube_add hq hp)
  refine ⟨half_pos hη,fun p q hp hq => ?_,fun p q hp hq => ?_,fun p q x hp hq => ?_⟩
  · exact analyticTrace (analyticMul (h.lit.oneD (x:=(p,q)) (q:=fun x => x.2+x.1) (p:=fun x => -x.1) (by fun_prop) (by fun_prop) (h₁ hp hq) (hs (tube_neg hp)) _) (h.lit.oneD contDiffAt_snd contDiffAt_fst (hs hq) (hs hp) _))
  · rw [pow_two]; exact (trace_norm _).trans (mul_le_mul_of_nonneg_left (op_cost (h.one _ _ _ (h₁ hp hq) (hs (tube_neg hp)) (LogStrip.single_bounded _)) (h.one _ _ _ (hs hq) (hs hp) (LogStrip.single_bounded _))) (by positivity))
  rw [reverseTrace,add_right_comm, show V.one (q+p+reciprocal x) (-p) (Pi.single i 1) = _ by simpa only [reciprocal_zero,add_zero] using (h.lit.one _ _ (Pi.single i 1) (h₁ hp hq) (hs (tube_neg hp))).2 x 0,
    show V.one (q+reciprocal x) p (Pi.single j 1) = _ by simpa only [reciprocal_zero,add_zero] using (h.lit.one _ _ (Pi.single j 1) (hs hq) (hs hp)).2 x 0]; rfl

variable {s : ℕ → Side} {m k : ℕ → Type} [∀ i, Fintype (m i)] [∀ i, Fintype (k i)] [∀ i, DecidableEq (m i)] [∀ i, DecidableEq (k i)]
    {A : ∀ i, Grid (s i) (m i) a} {B : ∀ i, Grid (s i) (k i) d} {R : ∀ i, (m i → ℝ) → RealTrace (m i) (k i)}
lemma reflects (hs : Expands s) (he : ∀ i, Charged (A i) (B i) (R i) V) : Mirrors A A (fun i => cmat (respCoeff (R i))) (kernelOf (respTrace V)) ∧
    Mirrors A A (fun i => cmat (accCoeff (R i))) (kernelOf (reverseTrace V)) := by
  have hη := h.width
  exact ⟨compares_mirror (fun i => Integrand.compare h.resp (fun k q _ hp => charge₂_sample (he i) k q hp))
      (fun p hp => (Integrand.smooth_mean h.resp (Work.F07.realStrip _ hη hp)).continuousAt) (exp_error_limit hs (by linarith) _),
    compares_mirror (fun i => Integrand.compare h.rev (fun k q _ hp => charge₁_sample (he i) k q hp))
      (fun p hp => (Integrand.smooth_mean h.rev (Work.F07.realStrip _ (half_pos hη) hp)).continuousAt) (exp_error_limit hs (by linarith) _)⟩
end ChargeStrip
end YM.Push.Loops
