import Mathlib.Analysis.Normed.Module.Connected
import YM.Next.MAXWELL.Battery


/-! # Strict positive one-point reflection Gram, already on real Shell -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Analysis MeasureTheory Box Tensor WaveOn
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j l : ℕ}
variable {ι : Type*} [Fintype ι] (a : Axis) {d : ι → ℕ} (x : ι → E4) (p : (i : ι) → Probe G (d i))

lemma power_silent (H : ∀ i, 0 < x i a) {t} (ht : 0 ≤ t) (h : loss a x p t=0) :
    sqPower a x p t = 0 := by
  let F := sqPower a x p t
  have hc : Continuous F := sq_cont a x p H t ht
  funext z
  change F z=0; by_contra he
  let R : ℝ := ‖z‖+1
  have hk (i : SpaceAxis) : |z i| < R := (norm_le_pi_norm z i).trans_lt (by dsimp [R]; linarith)
  have hp : matFloor a R ∈ 𝓝 z := by
    rw [mat_coords]
    let B := Set.pi (univ : Set SpaceAxis) (fun _ => Ioo (-R) R)
    have hm : z ∈ B := fun i _ => abs_lt.mp (hk i)
    refine mem_of_superset ((isOpen_set_pi finite_univ (s:=fun _ => Ioo (-R) R) fun i _ => isOpen_Ioo).mem_nhds hm) ?_
    exact fun y hy => ⟨fun i => (hy i (mem_univ _)).1.le,fun i => (hy i (mem_univ _)).2.le⟩
  have hv : support F ∩ matFloor a R ∈ 𝓝 z := inter_mem (hc.continuousAt.eventually_ne he) hp
  have hq : 0 < ∫ z in matFloor a R, F z :=
    (setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall (sq_nonneg a x p t))
      (hc.continuousOn.integrableOn_compact (show IsCompact (matFloor a R) from isCompact_Icc))).2 (Measure.measure_pos_of_mem_nhds _ hv)
  exact not_lt.mpr ((lesser_loss a x p H R ht).trans h.le) hq

lemma plane_silent (H : ∀ i, 0 < x i a) (h : heatLevel a x p 0 = 0) (b c : Axis) {t : ℝ} (ht : 0 < t)
    {y : E4} (hy : y a = 0) : rays a x p t b c y = 0 := by
  have he : heatLevel a x p =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u (hu : 0 < u)
    exact le_antisymm ((downhill a x p H (self_mem_Ici) hu.le hu.le).trans h.le) (reflected_positive a x p H hu.le)
  have hs := level_slope a x p H ht.le
  have hf : loss a x p t=0 := by
    have hc := hs.unique ((hasDerivAt_const t 0).congr_of_eventuallyEq he); linarith
  let z : Section3 := fun i => y (a.succAbove i)
  have hp : inFace a 0 z=y := by
    rw [← hy]; unfold inFace z; congr; apply Fin.insertNth_self_removeNth
  have hq : (∑ i : Axis, ∑ l : Axis, ‖rays a x p t i l y‖^2)=0 := by
    have he := congr_fun (power_silent a x p H ht.le hf) z
    simp only [sqPower, Pi.zero_apply,hp] at he; linarith
  have hu (i : Axis) : (∑ l : Axis, ‖rays a x p t i l y‖^2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => _root_.sq_nonneg _)).1 hq i (Finset.mem_univ i)
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => _root_.sq_nonneg _)).1 (hu b) c (Finset.mem_univ _)
  simpa using hb

lemma silent_response (H : ∀ i, 0 < x i a) (h : heatLevel a x p 0 = 0) (b c : Axis) {y : E4} (hy : y a < 0) :
    (∑ i, pulse (p i) (x i) b c y) = 0 := by
  let t := - y a
  have ht : 0 < t := neg_pos.mpr hy
  let z := floated a y t
  have hz : z a = 0 := by simp [z,t]
  have he := plane_silent a x p H h b c ht hz
  simp only [rays, Finset.sum_apply,pulse,z,floated,add_sub_add_right_eq_sub] at he
  exact he

variable {x}

lemma power_continues (z : E4) (hz : 0 < z a) (h : heatLevel a (fun _ => z) p 0 = 0) {y : E4} (b c : Axis)
    (hy : y ≠ z) : (∑ i, pulse (p i) z b c y)=0 := by
  let F := fun x : E4 => ∑ i, pulse (p i) z b c x
  ext1 e
  have hp : AnalyticOnNhd ℝ (fun y => F y e) ({z}ᶜ) := by
    intro y hy; refine ContDiffAt.analyticAt ?_
    simp only [F,WithLp.ofLp_sum,Finset.sum_apply]; apply ContDiffAt.sum; intro i _
    have he : (fun y => pulse (p i) z b c y e) =ᶠ[𝓝 y] K (p i) (omegaLeg e b c) z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hy] with x hx
      exact (K_observe _ _ _ _ (Ne.symm hx)).symm
    exact (((kernel_pole (p i) (omegaLeg e b c)).diff (z-y) (sub_ne_zero.mpr (Ne.symm (show y≠z from hy)))).comp y
      (f := fun y => z-y) (contDiffAt_const.sub contDiffAt_id)).congr_of_eventuallyEq he
  apply hp.eqOn_zero_of_preconnected_of_eventuallyEq_zero (z₀:= -basis a) ?_ ?_ ?_ hy
  · refine (isConnected_compl_singleton_of_one_lt_rank ?_ z).isPreconnected
    simp [← Module.finrank_eq_rank]
  · change -basis a ≠ z
    rintro rfl; simp at hz; linarith
  filter_upwards [(isOpen_lt (show Continuous fun y : E4 => y a by fun_prop) continuous_const).mem_nhds
    (show (-basis a) a < 0 by simp)] with x (hx : x a < 0)
  change F x e=0; rw [show F x = 0 from silent_response a (fun i => z) p (fun i => hz) h b c hx]; rfl

/-- stress test with polynomial field of selected order. -/
lemma filter_current (z : E4) {f : Field G.Color} (H : WaveOn univ f)
    (h : ∀ y : E4,y ≠ z → ∀ b c : Axis, (∑ i, pulse (p i) z b c y)=0) :
    (∑ i, (((d i : ℕ):ℝ)+2)*sample (p i) f z) = 0 := by
  let B : ContDiffBump z := ⟨1,2,by norm_num,by norm_num⟩
  let χ : E4 → ℝ := B
  let v := fromCenter 1 z
  let F := fun i => pulse (p i) z
  let J := fun i => current v (F i) f
  have he i : (∑ a : Axis, ∫ y : E4, grad a χ y • J i a y) = (((d i:ℕ):ℝ)+2)*sample (p i) f z := by
    apply neg_injective
    rw [← neg_mul]; exact radial_flux (χ:=χ) isOpen_univ H (p i) B.contDiff B.hasCompactSupport (subset_univ _) B.eventuallyEq_one
  simp_rw [← he]; rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro a _
  rw [← integral_finsetSum _ (fun i _ => shell_cost (show ContDiff ℝ ∞ χ from B.contDiff) B.hasCompactSupport
    (fun y hy => (current_diff (radial_K z) _ (fun j k =>
      (pulse_wave (p i) z).smooth j k y (fun h : y=z => collar (χ:=χ) B.eventuallyEq_one (h ▸ hy)))
      (fun j k => H.smooth j k y (mem_univ _))).continuousAt) a)]
  rw [show (fun y : E4 => ∑ i, grad a χ y • J i a y) = 0 from funext fun y => ?_]
  · exact integral_zero ..
  by_cases ht : y = z
  · subst y; simp [image_eq_zero_of_notMem_tsupport (x := z) (f := grad a χ)
      (fun h => collar (χ:=χ) B.eventuallyEq_one (gradient_part χ a h))]
  have hp (b) : (∑ i, cross (F i) f a b y)=0 := by
    let R : Unit → Field G.Color := fun _ => f
    have he (a b : Axis) : (∑ i, F i) a b y = 0 := by simp only [Finset.sum_apply]; exact h y ht a b
    calc
      _ = cross (∑ i, F i) (∑ i, R i) a b y := by rw [cross_sum_family]; simp [R]
      _ = 0 := by unfold cross; simp_rw [he]; simp
  rw [← Finset.smul_sum, show (∑ i, J i a y)=0 from ?_,smul_zero]; rfl
  unfold J current; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, hp,mul_zero,Finset.sum_const_zero]

/-- At **one** pair of marked sites strictly separated by reflection: whole
mixed jet collection, strict positivity modulo only the relations of the
linear symbols. -/
theorem level_detects (z : E4) (hz : 0 < z a) (h : heatLevel a (fun _ => z) p 0 = 0) (A : TaylorTower G) :
    ∑ i, p i (A (d i)) = 0 := by
  have hw y hy b c := power_continues a p z hz h (y := y) b c hy
  have hp (k : ℕ) : (∑ i, if d i=k then p i (A (d i)) else 0)=0 := by
    let f : Field G.Color := fun a b x => asWave (A k) a b (x-z)
    have H : WaveOn univ f := wave_sub_pull z (wave_mono (subset_univ _) (wavePoly (A k)))
    have he := filter_current p z H hw
    have hx (j) : nth f j z = nth (asWave (A k)) j 0 := by
      funext a b
      change coeff (fun x => asWave _ a b (x-z)) j z = _
      rw [coeff_shift,sub_self]; rfl
    have ht i : ((d i:ℝ)+2)*sample (p i) f z = (k+2:ℝ) * (if d i=k then p i (A (d i)) else 0) := by
      by_cases hq : d i=k
      · subst k; rw [sample_eval _ H isOpen_univ (mem_univ _), if_pos rfl]
        congr 1; exact congr_arg (p i) (Subtype.ext ((hx _).trans (asWave_jet _)))
      simp only [sample,hx,asWave_other (A k) hq,map_zero, if_neg hq,mul_zero]
    simp_rw [ht, ← Finset.mul_sum] at he
    exact (mul_eq_zero.mp he).resolve_left (by positivity)
  calc
    _ = ∑ k ∈ Finset.univ.image d, ∑ i, if d i=k then p i (A (d i)) else 0 := by rw [Finset.sum_comm]; simp
    _ = 0 := Finset.sum_eq_zero fun i _ => hp i

end YM.Maxwell.Free
