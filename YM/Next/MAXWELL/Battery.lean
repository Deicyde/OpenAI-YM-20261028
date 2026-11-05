import YM.Next.MAXWELL.Lid

/-!
# Reflected one-leg real quadratic form via the Ward charge

Translate a collection of positive insertions (each term still one leg),
at time a. The pairing with the reflection goes downhill; use exactly
the above Maxwell flux, since stress through the plane reads a sum of
squares. Degenerate coefficient combinations and coincident sites within
the collection allowed, gauge invariance not required at this point.

A route to strictness without Fourier or any variety hypotheses: equality
keeps the whole run zero and forces the field to vanish on the halfspace
(later continue and use the dilation Ward charge to detect jets).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Analysis MeasureTheory Box
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j l : ℕ}

def through (a : Axis) (x : E4) := Ortho.move (Signed.reflect a) x

def floated (a : Axis) (x : E4) (t : ℝ) := x+t • basis a

@[simp] lemma floats (a x t) : floated a x t a = x a+t := by simp [floated]
@[simp] lemma after (a x) : through a x a = -(x a) := by simp [through]
@[simp] lemma stays (a t x) : through a (floated a x t) = through a x - t • basis a := by
  ext1 i; by_cases hi : i=a
  · subst i; simp; ring
  simp [through,floated,hi]

@[simp] lemma mirrored_inv (a : Axis) : (Signed.reflect a)⁻¹ = Signed.reflect a :=
  (map_inv Signed.inclusionO (Signed.mirror a)).symm

lemma plane (a : Axis) {x : E4} (h : x a = 0) : through a x = x := by
  ext1 i; by_cases hi : i=a
  · subst i; simp [h]
  simp [through,hi]

def parity (a i : Axis) : ℝ := if a=i then -1 else 1

lemma reflect_entry (a i l : Axis) : (Signed.reflect a).val i l =
    if l=i then parity a i else 0 := by
  change (Signed.mirror a).matrix i l = _
  rw [Signed.matrix_at]
  split_ifs <;> simp_all [Signed.mirror,parity]

lemma plane_pulse {a : Axis} (p : Probe G j) {x : E4} (hx : 0 < x a) (i l : Axis) {y : E4} (hy : y a = 0) :
    pulse (probeTurn (Signed.reflect a) p) (through a x) i l y = parity a i • parity a l • pulse p x i l y := by
  have hm : x ≠ y := by rintro rfl; linarith
  have ht := pulse_orientation (Signed.reflect a) p i l hm
  rw [show Ortho.move (Signed.reflect a) y = y from plane a hy] at ht
  rw [through,ht]; unfold fieldTurn
  rw [mirrored_inv,show Ortho.move (Signed.reflect a) y = y from plane a hy]
  simp [reflect_entry, ite_smul,ite_mul, mul_ite,smul_smul]

section Squares
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma square_cross (a : Axis) (f g : Field F) (z : E4) (h : ∀ i l, g i l z = parity a i • parity a l • f i l z)
    (ht : ∀ i l, f i l z = -f l i z) : cross f g a a z = -(1/2) * ∑ i : Axis, ∑ l : Axis, ‖f i l z‖^2 := by
  have hz : f a a z = 0 := by
    apply (smul_right_injective F (by norm_num : (2:ℝ)≠0))
    change (2:ℝ) • f a a z = (2:ℝ) • (0:F); rw [two_smul,smul_zero]; nth_rw 1 [ht]; simp
  let B (i l) := ‖f i l z‖^2
  have he (i) : ⟪f a i z,g a i z⟫_ℝ = -B a i := by
    by_cases hi : i=a
    · subst i; simp [hz,B]
    simp [h a i, parity,Ne.symm hi,B]
  have hh (i l) : ⟪f i l z,g i l z⟫_ℝ = B i l -
      ((if i=a then 2 * B i l else 0) + if l=a then 2 * B a i else 0) := by
    have hs : B i a=B a i := by unfold B; nth_rw 1 [ht]; simp
    rcases eq_or_ne i a with hi | hi <;> rcases eq_or_ne l a with hl | hl
    · subst i; subst l; simp [hz,B]
    · subst i; rw [he]; simp [hl]; ring
    · subst l; simp [hi,Ne.symm hi, h i a,parity, ← hs, B]; ring
    simp [hi,hl,h i l,parity,Ne.symm hi,Ne.symm hl,B]
  unfold cross
  simp_rw [he,hh]
  change (∑ c : Axis, (-B a c + -B a c)) - _ = -(1/2) * ∑ i : Axis, ∑ l : Axis, B i l
  simp [kr,Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_irrel]
  ring

lemma cross_sum_family {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → Field F) (g : κ → Field F) (a b : Axis) (z) :
    cross (∑ i, f i) (∑ i, g i) a b z = ∑ i, ∑ j, cross (f i) (g j) a b z := by
  let L : Field F →ₗ[ℝ] Field F →ₗ[ℝ] ℝ :=
    { toFun p :=
        { toFun q := cross p q a b z
          map_add' _ _ := cross_adjoin ..
          map_smul' _ _ := cross_stretch .. }
      map_add' p q := by
        apply LinearMap.ext; intro x; change cross (p+q) _ _ _ _ = cross p _ _ _ _ + cross q _ _ _ _
        rw [cross_comm (p+q),cross_adjoin,cross_comm _ p,cross_comm _ q]
      map_smul' t p := by
        apply LinearMap.ext; intro x; change cross (t • p) x a b z=t*cross p x a b z
        rw [cross_comm (t • p),cross_stretch,cross_comm _ p] }
  change L (∑ i, f i) (∑ i, g i) = ∑ i, ∑ j, L (f i) (g j)
  simp only [map_sum,LinearMap.sum_apply]
  rw [Finset.sum_comm]
end Squares

lemma slope_path (a : Axis) (p : Probe G j) (q : Probe G l) (x y : E4) {t : ℝ}
    (h : floated a x t ≠ through a (floated a y t)) :
    let X := fun t => floated a x t
    let Y := fun t => through a (floated a y t)
    HasDerivAt (fun u => K p q (X u) (Y u)) (2*K (raiseLeg (basis a) p) q (X t) (Y t)) t := by
  intro X Y
  let F := fun z : E4 => K p q z (Y t)
  let L := fun u : ℝ => X t + (2*(u-t)) • basis a
  have he : L t=X t := by simp [L]
  have ht : HasDerivAt L ((2:ℝ) • basis a) t := by
    refine (((((hasDerivAt_id' t).sub_const t).const_mul 2).smul_const (basis a)).const_add _).congr_deriv ?_
    simp
  have hf : DifferentiableAt ℝ F (L t) := by
    rw [he];
    exact ((K_smooth p q (X t,Y t) h).comp (f := fun z : E4 => (z,Y t)) (X t)
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hh : (fun u => K p q (X u) (Y u)) = F ∘ L := by
    funext u
    change _ = K p q (L u) (Y t)
    rw [show L u = X u + (u-t) • basis a by
        unfold L X floated; rw [two_mul,add_smul,sub_smul]; abel,
      show Y t = Y u + (u-t) • basis a by unfold Y; rw [stays,stays,sub_smul]; abel,
      K_across]
  rw [hh]; refine (hf.hasFDerivAt.comp_hasDerivAt t ht).congr_deriv ?_
  rw [he,map_smul]; exact congr_arg (fun z : ℝ => (2:ℝ) • z) (K_left_D p q h (basis a))

lemma late_K (p : Probe G j) (q : Probe G l) (x y : E4) (a : Axis) :
    Tendsto (fun t : ℝ => K p q (floated a x t) (through a (floated a y t))) atTop (𝓝 0) := by
  obtain ⟨C,hc,H⟩ := (kernel_pole p q).bounds
  have he : Tendsto (fun t : ℝ => C*t⁻¹^(4+j+l)) atTop (𝓝 0) := by
    have h : 4+j+l≠0 := by omega
    simpa [h] using ((tendsto_inv_atTop_zero (𝕜:=ℝ)).pow (4+j+l)).const_mul C
  refine squeeze_zero_norm' ?_ he
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (|x a + y a|)] with t ht hh
  let z := floated a x t - through a (floated a y t)
  have hz : t ≤ ‖z‖ := calc
    t ≤ z a := by simp only [z, PiLp.sub_apply, floats,after]; rw [abs_le] at hh; linarith [hh.1]
    _ ≤ |z a| := le_abs_self _
    _ ≤ ‖z‖ := PiLp.norm_apply_le z a
  refine (H z (norm_pos_iff.mp (ht.trans_le hz))).trans ?_
  gcongr

section Battery
variable {ι : Type*} [Fintype ι] (a : Axis) {d : ι → ℕ} (x : ι → E4) (p : (i : ι) → Probe G (d i))
    (H : ∀ i, 0 < x i a)

def heatLevel (t : ℝ) := ∑ i, ∑ j, K (p i) (probeTurn (Signed.reflect a) (p j))
  (floated a (x i) t) (through a (floated a (x j) t))

def loss (t : ℝ) := ∑ i, ∑ j, -K (raiseLeg (basis a) (p i)) (probeTurn (Signed.reflect a) (p j))
  (floated a (x i) t) (through a (floated a (x j) t))

def rays (t : ℝ) := ∑ i, pulse (p i) (floated a (x i) t)

def matFloor (R : ℝ) := face (base a R) (lid R) a

lemma mat_coords (R : ℝ) : matFloor a R = Icc (fun _ => -R) (fun _ => R) := by
  unfold matFloor face; congr 1
  ext1 i; simp [base, Ne.symm (Fin.succAbove_ne a i)]

def sqPower (t : ℝ) (z : Section3) :=
  (1/2) * ∑ b : Axis, ∑ c : Axis, ‖rays a x p t b c (inFace a 0 z)‖^2

lemma sq_nonneg (t : ℝ) (z : Section3) : 0 ≤ sqPower a x p t z := by unfold sqPower; positivity

include H

omit [Fintype ι] in
private lemma past (t : ℝ) (ht : 0 ≤ t) (i) : 0 < floated a (x i) t a := by rw [floats]; linarith [H i]

omit [Fintype ι] in
private lemma safe {t : ℝ} (ht : 0 ≤ t) (z : Section3) (i) :
    floated a (x i) t ≠ inFace a 0 z := by intro h; have hv := past a x H _ ht i; rw [h,inFace_at] at hv; exact lt_irrefl _ hv

lemma sq_cont (t : ℝ) (ht : 0 ≤ t) : Continuous (sqPower a x p t) := by
  apply Continuous.mul continuous_const
  refine continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ => Continuous.pow (Continuous.norm ?_) _
  simp only [rays, Finset.sum_apply]
  refine continuous_finsetSum _ fun i _ => continuous_iff_continuousAt.mpr fun z => ?_
  exact (((pulse_wave (p i) _).smooth b c _ (Ne.symm (safe a x H ht z i))).continuousAt.comp (inFace_cont a 0).continuousAt)

lemma level_slope {t} (ht : 0 ≤ t) : HasDerivAt (heatLevel a x p) (-2 * loss a x p t) t := by
  unfold heatLevel loss; simp_rw [Finset.mul_sum,neg_mul_neg]
  apply HasDerivAt.fun_sum; intro i _; apply HasDerivAt.fun_sum; intro j _
  have he : floated a (x i) t ≠ through a (floated a (x j) t) := by
    intro h; have hi := past a x H t ht i; rw [h,after] at hi; have h := past a x H t ht j; linarith
  exact slope_path a _ _ _ _ he

omit H in lemma level_late : Tendsto (heatLevel a x p) atTop (𝓝 0) := by
  have he := tendsto_finsetSum Finset.univ fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    tendsto_finsetSum Finset.univ fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      late_K (p i) (probeTurn (Signed.reflect a) (p j)) (x i) (x j) a
  unfold heatLevel; simpa using he

/-- The total stress flux paid by the bottom face after the shift by t. -/
theorem reads_loss {t} (ht : 0 ≤ t) :
    Tendsto (fun R => ∫ z in matFloor a R, sqPower a x p t z) atTop (𝓝 (loss a x p t)) := by
  let X (i) := floated a (x i) t
  let Q := fun i => probeTurn (Signed.reflect a) (p i)
  let F (i) := pulse (p i) (X i)
  let A := ∑ i, F i
  let Y (i) := through a (X i)
  let L (i) := pulse (Q i) (Y i)
  let B := ∑ i, L i
  have hi (i) : 0 < X i a := past a x H t ht i
  have hj (i) : Y i a < 0 := by simp only [Y,after]; linarith [hi i]
  have hq (z : E4) (hz : z a = 0) (b c : Axis) : B b c z = parity a b • parity a c • A b c z := by
    dsimp only [A,B]
    simp_rw [Finset.sum_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => plane_pulse _ (hi i) b c hz
  have hA (b c : Axis) (z : E4) (hz : z a=0) : A b c z = - A c b z := by
    dsimp only [A]
    simp_rw [Finset.sum_apply,← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
    exact (pulse_wave (p i) (X i)).form b c z (fun h : z=X i => (hi i).ne (by rw [← h,hz]))
  let J (i j : ι) := fun b z => cross (F i) (L j) b a z
  have he (z : Section3) : sqPower a x p t z = ∑ i, ∑ j, -(J i j a (inFace a 0 z)) := by
    have hp := square_cross a A B (inFace a 0 z) (hq _ (inFace_at ..)) (fun i l => hA i l _ (inFace_at ..))
    simp_rw [Finset.sum_neg_distrib]
    change _ = -∑ i, ∑ j, cross (F i) (L j) a a _
    rw [← cross_sum_family]
    change _ = -cross A B a a _
    rw [hp,neg_mul,neg_neg]; rfl
  have hb (R : ℝ) (i j : ι) : IntegrableOn (fun z => -(J i j a (inFace a 0 z))) (matFloor a R) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_of_forall_continuousAt (fun z hz => ?_))
    have h : ContDiffAt ℝ ∞ (cross (F i) (L j) a a) (inFace a 0 z) := cross_diff _ _
      (fun b c => (pulse_wave ..).smooth b c _ (Ne.symm (safe a x H ht z i))) (fun b c => ?_)
    · exact (h.continuousAt.comp (f := inFace a 0) (inFace_cont a 0).continuousAt).neg
    have hy : inFace a 0 z ≠ Y j := by intro h; have hh := hj j; rw [← h,inFace_at] at hh; exact lt_irrefl _ hh
    exact (pulse_wave (Q j) (Y j)).smooth _ _ _ hy
  simp_rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hb _ i j),
    integral_finsetSum _ (fun j _ => hb _ _ j),integral_neg]
  exact tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ =>
    Box.readout a (hi i) (hj j) (p i) (Q j)

theorem lesser_loss (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z in matFloor a R, sqPower a x p t z) ≤ loss a x p t := by
  apply ge_of_tendsto (reads_loss a x p H ht)
  filter_upwards [eventually_ge_atTop R] with S hS
  refine setIntegral_mono_set (ContinuousOn.integrableOn_compact isCompact_Icc
    ((sq_cont a x p H t ht).continuousOn)) (ae_of_all _ (sq_nonneg a x p t)) (Eventually.of_forall fun z hz => ?_)
  have h : matFloor a R ⊆ matFloor a S := by
    rw [mat_coords,mat_coords]; exact Icc_subset_Icc (fun i => neg_le_neg hS) (fun i => hS)
  exact h hz

theorem loss_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ loss a x p t :=
  le_trans (setIntegral_nonneg measurableSet_Icc (fun i _ => sq_nonneg a x p t i)) (lesser_loss a x p H 1 ht)

theorem downhill : AntitoneOn (heatLevel a x p) (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun t ht => ((level_slope a x p H ht).continuousAt.continuousWithinAt))
    (fun t ht => (level_slope a x p H (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
  intro t ht
  have hw : 0 ≤ t := interior_subset ht
  rw [(level_slope a x p H hw).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (loss_nonneg a x p H hw)

theorem reflected_positive {t : ℝ} (ht : 0 ≤ t) : 0 ≤ heatLevel a x p t := by
  apply le_of_tendsto (level_late a x p)
  filter_upwards [eventually_ge_atTop t] with s hs
  exact downhill a x p H ht (ht.trans hs) hs

end Battery
end YM.Maxwell.Free
