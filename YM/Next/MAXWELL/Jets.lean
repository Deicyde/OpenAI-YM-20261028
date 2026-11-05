import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import YM.Analysis.Exchange
import YM.Maxwell.Shell

/-!
# Real Maxwell shell: local solutions and polynomial jets

Infrastructure for the actual (free comparator) producer. Nothing here
holds any estimates on YM histories. Derivatives at ordinary points of
open patches; never assume that the covariance extends smoothly to the
diagonal. Remember the jets in Shell are **coefficients**, not derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis
open WaveOn
open scoped ContDiff Topology BigOperators

variable {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {G : Gauge} {j k l : ℕ}

/-- We also use the real one-color version, and color-blind identities. -/
abbrev Solution (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) := ↥(onShell F j)

section Calculus
variable {U V : Set E4} {f g : Field F} {x : E4}



theorem wave_add (hf : WaveOn U f) (hg : WaveOn U g) : WaveOn U (f+g) := by
  have he (a b c : Axis) (x) (hx : x ∈ U) :
      grad a ((f+g) b c) x = grad a (f b c) x + grad a (g b c) x := by
    change fderiv ℝ (f b c + g b c) x _ = _
    rw [fderiv_add ((hf.smooth _ _ x hx).differentiableAt (by simp))
      ((hg.smooth _ _ x hx).differentiableAt (by simp))]
    rfl
  refine ⟨fun _ _ x hx => (hf.smooth _ _ x hx).add (hg.smooth _ _ x hx), ?_, ?_, ?_⟩
  · intro a b x hx
    simp only [Pi.add_apply]; nth_rw 1 [hf.form a b x hx]; nth_rw 1 [hg.form a b x hx]
    rw [neg_add]
  · intro a b c x hx
    rw [he _ _ _ x hx, he _ _ _ x hx, he _ _ _ x hx]
    calc
      _ = (grad a (f b c) x + grad b (f c a) x + grad c (f a b) x) +
          (grad a (g b c) x + grad b (g c a) x + grad c (g a b) x) := by abel
      _ = 0 := by rw [hf.cycle _ _ _ x hx,hg.cycle _ _ _ x hx, add_zero]
  intro b x hx; simp_rw [he _ _ _ x hx, Finset.sum_add_distrib,
    hf.divergence _ x hx,hg.divergence _ x hx, add_zero]



theorem wave_mono (hv : V ⊆ U) (hf : WaveOn U f) : WaveOn V f :=
  ⟨fun a b x hx ↦ hf.smooth a b x (hv hx), fun a b x hx ↦ hf.form a b x (hv hx),
    fun a b c x hx ↦ hf.cycle a b c x (hv hx), fun b x hx ↦ hf.divergence b x (hv hx)⟩



theorem wave_neg_pull (hf : WaveOn (Neg.neg '' U) f) :
    WaveOn U (fun a b (x : E4) => f a b (-x)) := by
  let N := -(ContinuousLinearMap.id ℝ E4)
  have he (a b c : Axis) (x) (hx : x ∈ U) :
      grad a (fun x => f b c (-x)) x = - grad a (f b c) (-x) := by
    have hw : ContDiffAt ℝ ∞ (f b c) (N x) := hf.smooth b c _ (mem_image_of_mem _ hx)
    change fderiv ℝ (f b c ∘ N) x _ = _
    rw [fderiv_comp x (hw.differentiableAt (by simp)) N.differentiableAt, N.fderiv]
    exact map_neg (fderiv ℝ (f b c) (-x)) _
  refine ⟨fun a b x hx => (hf.smooth a b _ (mem_image_of_mem _ hx)).comp x N.contDiff.contDiffAt,
    fun a b x hx => hf.form a b _ (mem_image_of_mem _ hx),?_,?_⟩
  · intro a b c x hx; rw [he _ _ _ _ hx, he _ _ _ _ hx, he _ _ _ _ hx, ← neg_add, ← neg_add,
      hf.cycle _ _ _ _ (mem_image_of_mem _ hx), neg_zero]
  intro b x hx; simp_rw [he _ _ _ _ hx, Finset.sum_neg_distrib,
    hf.divergence _ _ (mem_image_of_mem _ hx), neg_zero]

theorem wave_sub_pull (r : E4) (hf : WaveOn ((fun x => x-r) '' U) f) :
    WaveOn U (fun a b x => f a b (x-r)) := by
  have he (a b c : Axis) (x) (hx : x ∈ U) : grad a (fun z => f b c (z-r)) x = grad a (f b c) (x-r) := by
    change fderiv ℝ (f b c ∘ ((·-r) : E4 → E4)) x _ = _
    have hw : HasFDerivAt (fun x : E4 => x-r) (ContinuousLinearMap.id ℝ E4) x :=
      (hasFDerivAt_id x).sub_const _
    rw [fderiv_comp x ((hf.smooth b c _ (mem_image_of_mem _ hx)).differentiableAt (by simp))
      hw.differentiableAt, hw.fderiv]; rfl
  refine ⟨fun a b x hx => (hf.smooth a b _ (mem_image_of_mem _ hx)).comp x (contDiffAt_id.sub contDiffAt_const),
    fun a b x hx => hf.form a b _ (mem_image_of_mem _ hx), ?_,?_⟩
  · intro a b c x hx; rw [he _ _ _ _ hx, he _ _ _ _ hx, he _ _ _ _ hx]
    exact hf.cycle _ _ _ _ (mem_image_of_mem _ hx)
  intro b x hx; simp_rw [he _ _ _ _ hx]; exact hf.divergence _ _ (mem_image_of_mem _ hx)

theorem wave_D (hf : WaveOn U f) (hU : IsOpen U) (u : E4) :
    WaveOn U (fun b c => D u (f b c)) := by
  have hw (a b c : Axis) (x) (hx : x ∈ U) :
      grad a (D u (f b c)) x = D u (grad a (f b c)) x :=
    commuteD ((hf.smooth b c x hx).of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from
      WithTop.coe_le_coe.mpr le_top)) ..
  have hd (a b c : Axis) (x) (hx : x ∈ U) : DifferentiableAt ℝ (grad a (f b c)) x :=
    (grad_smooth a (m := ∞) (hf.smooth b c x hx) (by simp)).differentiableAt (by simp)
  refine ⟨fun a b x hx => dSmooth (hf.smooth a b x hx) _ (by simp),?_,?_,?_⟩
  · intro a b x hx
    have he : f a b =ᶠ[𝓝 x] -(f b a) := by
      filter_upwards [hU.mem_nhds hx] with y hy; exact hf.form a b y hy
    rw [GermD _ he, D,fderiv_neg]
    rfl
  · intro a b c x hx; simp_rw [hw _ _ _ x hx]
    have he : grad a (f b c) + grad b (f c a) + grad c (f a b) =ᶠ[𝓝 x] (fun _ => (0:F)) := by
      filter_upwards [hU.mem_nhds hx] with y hy; exact hf.cycle a b c y hy
    have heq := (GermD u he).trans (show D u (fun _ => (0:F)) x = _ from (show _ = 0 by simp [D]))
    simp only [D, fderiv_add ((hd a b c x hx).add (hd b c a x hx)) (hd c a b x hx),
      fderiv_add (hd a b c x hx) (hd b c a x hx),add_apply] at heq
    exact heq
  intro b x hx; simp_rw [hw _ _ _ x hx]
  have he : ∑ a : Axis, grad a (f a b) =ᶠ[𝓝 x] (fun _ => (0:F)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [Finset.sum_apply]; exact hf.divergence _ y hy
  have heq := (GermD u he).trans (show D u (fun _ => (0:F)) x = 0 by simp [D])
  rw [D,fderiv_sum (fun a _ => hd _ _ _ x hx),sum_apply] at heq
  exact heq

end Calculus

/-- Polynomial representatives as homogeneous solutions. -/
def asWave (A : Solution F j) : Field F := fun i l => diagonal (A.val i l)

theorem wavePoly (A : Solution F j) : WaveOn univ (asWave A) where
  smooth _ _ _ _ := (diag_smooth _ _).contDiffAt
  form i l x _ := congr_arg (fun B : Tensor.T E4 F j => diagonal B x)
    ((show ClosedJet _ from A.property.1).antisymmetric i l)
  cycle i l k x _ := (show ClosedJet _ from A.property.1).closed i l k x
  divergence b x _ := A.property.2 b x

/-- Coefficient jet at the marked center. -/
theorem coeff_diagonal (A : T E4 F j) (ha : Sym A) : coeff (diagonal A) j 0 = A := by
  apply ContinuousMultilinearMap.ext; intro u
  induction j with
  | zero => rw [coeff_apply_zero]; exact congr_arg A (Subsingleton.elim ..)
  | succ j ih =>
    rw [← Fin.cons_self_tail u]
    let v := u 0
    let s := Fin.tail u
    let B := A.curryLeft v
    let t : ℝ := (↑(j+1 : ℕ) : ℝ)
    have he : D v (diagonal A) = t • diagonal B := funext fun x => by
      rw [D,differential_diagonal A ha]
      change _ = (↑(j+1 : ℕ) : ℝ) • (diagonal B x)
      rw [Nat.cast_smul_eq_nsmul]; rfl
    have hs := ih B (freeze_sym A ha v) s
    have ht : t ≠ 0 := by dsimp [t]; positivity
    change coeff (diagonal A) (j+1) 0 (Fin.cons v s) = _
    rw [coeff_apply_cons (diag_smooth A _ |>.contDiffAt),he, Tensor.coeff_smul _ (diag_smooth _ _ |>.contDiffAt), smul_apply,hs]
    change t⁻¹ • t • B s = _
    rw [inv_smul_smul₀ ht]
    rfl

theorem coeff_diagonal_ne (A : T E4 F j) (ha : Sym A) (hh : k ≠ j) :
    coeff (diagonal A) k 0 = 0 := by
  apply ContinuousMultilinearMap.ext; intro u
  induction k generalizing j with
  | zero =>
    rw [coeff_apply_zero]
    cases j with
    | zero => exact (hh rfl).elim
    | succ j =>
      change A _ = (0:F)
      exact A.map_coord_zero (0 : Fin (j+1)) rfl
  | succ k ih =>
    rw [← Fin.cons_self_tail u, coeff_apply_cons (diag_smooth A _ |>.contDiffAt)]
    cases j with
    | zero =>
      rw [show diagonal A = fun _ => diagonal A 0 from
        funext fun _ => congr_arg A (Subsingleton.elim ..)]
      have hz : D (u 0) (fun _ => diagonal A 0) = fun _ => (0:F) := by simp [D, funext_iff]
      rw [hz, coeff_zero]; simp
    | succ j =>
      let v := u 0
      let B := A.curryLeft v
      have he : D (u 0) (diagonal A) = (↑(j+1 : ℕ) : ℝ) • diagonal B := funext fun x => by
        rw [D,differential_diagonal A ha];
        change _ = (↑(j+1 : ℕ) : ℝ) • (diagonal B x)
        rw [Nat.cast_smul_eq_nsmul]; rfl
      rw [he, Tensor.coeff_smul _ (diag_smooth _ _ |>.contDiffAt), smul_apply, ih B (freeze_sym A ha v) (by omega)]
      simp

@[simp] theorem asWave_jet (A : Solution F j) : nth (asWave A) j 0 = A.val :=
  funext fun i => funext fun l => coeff_diagonal _ ((show ClosedJet _ from A.property.1).coeffSym i l)

theorem asWave_other (A : Solution F j) (h : k ≠ j) : nth (asWave A) k 0 = 0 := funext fun i => funext fun l =>
  coeff_diagonal_ne _ ((show ClosedJet _ from A.property.1).coeffSym i l) h

theorem coeff_shift (f : E4 → F) (x y : E4) (j : ℕ) :
    coeff (fun z => f (z-y)) j x = coeff f j (x-y) := by
  rw [coeff, coeff, iteratedFDeriv_comp_sub]

/-- Coefficient shift for spacetime derivatives of an insertion. -/
def lower (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (u : E4) :
    Solution F (j+1) →ₗ[ℝ] Solution F j where
  toFun A := ⟨fun i l => (↑(j+1 : ℕ) : ℝ) • (A.val i l).curryLeft u, by
    have H := (wave_D (wavePoly A) isOpen_univ u).jets isOpen_univ (j := j) (x := 0) (mem_univ _)
    convert H using 1
    ext1 i; ext1 l; apply ContinuousMultilinearMap.ext; intro v
    have he := coeff_apply_cons ((wavePoly A).smooth i l 0 (mem_univ _) |>.of_le
      (show (↑(j+1 : ℕ) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) u v
    have ht (w) : coeff (asWave A i l) (j+1) 0 w = A.val i l w :=
      congr_arg (fun M : TwoJet F (j+1) => M i l w) (asWave_jet A)
    rw [ht] at he
    change _ = coeff _ j 0 v
    rw [smul_apply, ContinuousMultilinearMap.curryLeft_apply, he,
      smul_inv_smul₀ (by positivity : (↑(j+1 : ℕ) : ℝ) ≠ 0)]⟩
  map_add' A B := by
    apply Subtype.ext; ext1 i; ext1 l; apply ContinuousMultilinearMap.ext; intro v
    change (↑(j+1 : ℕ) : ℝ) • (A.val i l (Fin.cons u v) + B.val i l (Fin.cons u v)) =
      (↑(j+1 : ℕ) : ℝ) • A.val i l (Fin.cons u v) + (↑(j+1 : ℕ) : ℝ) • B.val i l (Fin.cons u v)
    rw [smul_add]
  map_smul' t A := by
    apply Subtype.ext; ext1 i; ext1 l; apply ContinuousMultilinearMap.ext; intro v
    change (↑(j+1 : ℕ) : ℝ) • t • A.val i l (Fin.cons u v) =
      t • (↑(j+1 : ℕ) : ℝ) • A.val i l (Fin.cons u v)
    rw [smul_comm]

theorem lower_apply (u : E4) (A : Solution F (j+1)) (i l : Axis) (v : Fin j → E4) :
    (lower F j u A).val i l v = (↑(j+1 : ℕ) : ℝ) • A.val i l (Fin.cons u v) := rfl

theorem samples_D {U : Set E4} {f : Field F} (H : WaveOn U f) (hU : IsOpen U) (u : E4) {x : E4} (hx : x ∈ U) :
    nth (fun i l => D u (f i l)) j x = (lower F j u ⟨nth f (j+1) x,H.jets hU hx⟩).val := by
  ext1 i; ext1 l; apply ContinuousMultilinearMap.ext; intro v
  rw [lower_apply]; symm
  change (↑(j+1 : ℕ) : ℝ) • coeff (f i l) (j+1) x (Fin.cons u v) = _
  rw [coeff_apply_cons ((H.smooth i l x hx).of_le (WithTop.coe_le_coe.mpr le_top)),
    smul_inv_smul₀ (by positivity : (↑(j+1 : ℕ) : ℝ) ≠ 0)]
  rfl

end YM.Maxwell.Free
