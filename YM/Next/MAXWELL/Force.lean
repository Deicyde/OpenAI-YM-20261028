import Mathlib.Analysis.Calculus.ParametricIntegral
import YM.Next.MAXWELL.Contact


/-!
# One-jet and two-source Ward charges

Same actual collar Window, not needing uniformity of shrinking the arm
of the test. Translation center derivatives below keep even the angular
vector field **fixed**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j l : ℕ}

lemma pulse_differentiated (x u : E4) (s : ℝ) (p : Probe G j) (i l : Axis) {y : E4} (h : x+s • u ≠ y) :
    HasDerivAt (fun t : ℝ => pulse p (x+t • u) i l y) (pulse (raiseLeg u p) (x+s • u) i l y) s := by
  let P (t : ℝ) := x+t • u
  let F := responded G (extension p) i l
  have hp : HasDerivAt P u s := by
    refine (((hasDerivAt_id' s).smul_const u).const_add x).congr_deriv ?_
    simp
  have he : ContDiffAt ℝ ∞ F (P s-y) := (response (G := G) (extension p)).smooth i l _ (sub_ne_zero.mpr h)
  have hs := (he.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (hp.sub_const y)
  change HasDerivAt (fun t : ℝ => pulse p (x+t • u) i l y) (D u F _) s at hs
  refine hs.congr_deriv ?_
  ext c
  let g := fun z : E4 => K p (omegaLeg c i l) z y
  let L := (EuclideanSpace.proj c : G.Color →L[ℝ] ℝ)
  have hk : (fderiv ℝ g (P s)) u = K (raiseLeg u p) (omegaLeg c i l) (P s) y :=
    K_left_D _ _ h u
  have hw : g =ᶠ[𝓝 (P s)] L ∘ F ∘ ((·-y) : E4 → E4) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show P s ∈ ({y} : Set E4)ᶜ from h)] with z hz
    exact K_observe p c i l hz
  have hf : HasFDerivAt ((·-y) : E4 → E4) (ContinuousLinearMap.id ℝ E4) (P s) :=
    (hasFDerivAt_id (P s)).sub_const _
  have hg : HasFDerivAt g (L ∘L fderiv ℝ F (P s-y) ∘L ContinuousLinearMap.id ℝ E4) (P s) :=
    (L.hasFDerivAt.comp (P s) ((he.differentiableAt (by simp)).hasFDerivAt.comp (P s) hf)).congr_of_eventuallyEq hw
  rw [K_observe _ _ _ _ h, hg.fderiv] at hk
  exact hk

lemma pulse_cont_pair (p : Probe G j) (a b : Axis) {z : E4 × E4} (h : z.1 ≠ z.2) :
    ContinuousAt (fun z : E4 × E4 => pulse p z.1 a b z.2) z :=
  ((response (G := G) (extension p)).smooth a b (z.1-z.2) (sub_ne_zero.mpr h)).continuousAt.comp (x:=z) (f:=fun z : E4 × E4 => z.1-z.2) (continuousAt_fst.sub continuousAt_snd)

private lemma deriv_current (x u : E4) (s : ℝ) (p : Probe G j) (f : Field G.Color) (v : Drive)
    (a : Axis) {y : E4} (h : x+s • u ≠ y) :
    HasDerivAt (fun t : ℝ => current v (pulse p (x+t • u)) f a y)
      (current v (pulse (raiseLeg u p) (x+s • u)) f a y) s := by
  have ht (a b c d) : HasDerivAt (fun t : ℝ => ⟪pulse p (x+t • u) a b y, f c d y⟫_ℝ)
      (⟪pulse (raiseLeg u p) (x+s • u) a b y,f c d y⟫_ℝ) s := by
    simpa using (pulse_differentiated x u s p a b h).inner ℝ (hasDerivAt_const s (f c d y))
  unfold current cross; refine HasDerivAt.fun_sum fun b _ => HasDerivAt.const_mul (v b y) (HasDerivAt.sub
    (HasDerivAt.fun_sum fun c _ => (ht a c b c).add (ht b c a c)) ?_)
  exact HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun l _ => ht i l i l)

section Charge
variable {U : Set E4} (hU : IsOpen U) {f : Field G.Color} (H : WaveOn U f)
variable {v : Drive} (hv : Killing v)
variable {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
variable {x : E4} (hw : χ =ᶠ[𝓝 x] fun _ => 1)

include H hv hχ Hχ hs hw

private theorem flux_pulse_integrable (a : Axis) (p : Probe G j) :
    Integrable fun y => grad a χ y • current v (pulse p x) f a y :=
  shell_cost hχ Hχ (fun y hy => (current_diff hv _ (fun i l =>
    (pulse_wave p x).smooth i l y (fun he : y=x => collar hw (he ▸ hy)))
    (fun i l => H.smooth i l y (hs (tsupport_fderiv_subset ℝ hy)))).continuousAt) a

private theorem deriv_flux (p : Probe G j) (u : E4) : HasDerivAt (fun t : ℝ => singleFlux v χ (pulse p (x+t • u)) f)
    (singleFlux v χ (pulse (raiseLeg u p) x) f) 0 := by
  classical
  unfold singleFlux exportFlux; apply HasDerivAt.neg; apply HasDerivAt.fun_sum; intro a _
  let X (t : ℝ) := x+t • u
  have hx : X 0 = x := by simp [X]
  have hc : Continuous X := by unfold X; fun_prop
  let V := tsupport (fderiv ℝ χ)
  have hK : IsCompact V := Hχ.fderiv _
  have ht : ∀ᶠ t in 𝓝 (0:ℝ), χ =ᶠ[𝓝 (X t)] fun _ => 1 := (show Tendsto X (𝓝 0) (𝓝 x) from hx ▸ (show Tendsto X (𝓝 0) (𝓝 (X 0)) from hc.continuousAt)) hw.eventuallyEq_nhds
  obtain ⟨r,hr,hr'⟩ := Metric.nhds_basis_closedBall.mem_iff.mp ht
  let A := Metric.closedBall (0:ℝ) r
  have ha : A ∈ 𝓝 (0:ℝ) := Metric.closedBall_mem_nhds _ hr
  let P {j : ℕ} (p : Probe G j) (t : ℝ) (y : E4) := grad a χ y * current v (pulse p (X t)) f a y
  let q := raiseLeg u p
  have Ht {j : ℕ} (p : Probe G j) {t} (ht : t ∈ A) : Integrable (P p t) :=
    flux_pulse_integrable H hv hχ Hχ hs (hr' ht) a p
  have sep {t} (ht : t ∈ A) {y} (hy : y ∈ V) : X t ≠ y := fun he => collar (hr' ht) (he ▸ hy)
  have hg : ContinuousOn (fun z : ℝ × E4 => P q z.1 z.2) (A ×ˢ V) := by
    intro z hz; obtain ⟨ht,hy⟩ := hz
    have Hu := hs (tsupport_fderiv_subset ℝ hy)
    have hp (a b) : ContinuousAt (fun w : ℝ × E4 => pulse q (X w.1) a b w.2) z :=
      (pulse_cont_pair q a b (z := (X z.1,z.2)) (sep ht hy)).comp (x:=z) (f := fun w : ℝ × E4 => (X w.1,w.2))
        ((hc.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd)
    have Hi (a b) : ContinuousAt (fun w : ℝ × E4 => f a b w.2) z :=
      (H.smooth a b z.2 Hu).continuousAt.comp continuousAt_snd
    apply ContinuousAt.continuousWithinAt; unfold P current cross
    have sum {q : Axis → ℝ × E4 → ℝ} (h : ∀ i ∈ (Finset.univ : Finset Axis), ContinuousAt (q i) z) :
        ContinuousAt (fun p => ∑ i, q i p) z := tendsto_finsetSum _ h
    apply ((gradient_smooth hχ a).continuous.comp continuous_snd).continuousAt.mul
    refine sum (fun b _ => ((hv.diff b).continuous.continuousAt.comp continuousAt_snd).mul
      (ContinuousAt.sub ?_ (continuousAt_const.mul ?_)))
    · exact sum (fun i _ => ((hp ..).inner (Hi ..)).add ((hp ..).inner (Hi ..)))
    exact sum fun i _ => sum fun j _ => (hp ..).inner (Hi ..)
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:ℝ) r).prod hK).exists_bound_of_continuousOn hg
  let B := V.indicator fun _ => C
  have he : HasDerivAt (fun t : ℝ => ∫ y : E4, P p t y) (∫ y : E4, P q 0 y) 0 :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := P q) (bound := B) ha
      (Eventually.mono ha fun t ht => (Ht p ht).1) (Ht p (mem_of_mem_nhds ha))
      (Ht q (mem_of_mem_nhds ha)).1 ?_ ((continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet) ?_).2
  · simp only [P,hx,q] at he; exact he
  · refine Eventually.of_forall fun y t ht => ?_
    by_cases hy : y ∈ V
    · rw [show B y = C from indicator_of_mem hy _]; exact hC (t,y) ⟨ht,hy⟩
    have hh : grad a χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (gradient_part χ a h)
    simp [B,P,hy,hh]
  refine Eventually.of_forall fun y t ht => ?_
  by_cases hy : y ∈ V
  · exact (deriv_current x u t p f v a (sep ht hy)).const_mul (grad a χ y)
  have hh : grad a χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (gradient_part χ a h)
  simpa only [P,hh,zero_mul] using! hasDerivAt_const t (0:ℝ)

include hU

/-- One contraction at enclosure. Need `variation` wave (prove for
our translations etc separately). No first-position specialization. -/
theorem jet_force (h : WaveOn U (variation v f)) (p : Probe G j) :
    singleFlux v χ (pulse p x) f = - sample p (variation v f) x := by
  induction p using leg_probe_induction generalizing x with
  | zero => simp [pulse_zero,singleFlux,exportFlux,current,cross,sample,extension]
  | add p q hp hq =>
    unfold singleFlux exportFlux at hp hq ⊢
    have ht (a : Axis) (y) : current v (pulse (p+q) x) f a y =
        current v (pulse p x) f a y + current v (pulse q x) f a y := by
      unfold current; simp_rw [pulse_add, cross_comm (_+_) f,cross_adjoin,mul_add, Finset.sum_add_distrib,
        ← cross_comm (pulse p x) f, ← cross_comm (pulse q x) f]
    simp_rw [ht, smul_add]; simp_rw [integral_add (flux_pulse_integrable H hv hχ Hχ hs hw _ p)
      (flux_pulse_integrable H hv hχ Hχ hs hw _ q)]
    rw [Finset.sum_add_distrib,neg_add, hp hw,hq hw, ← neg_add,sample_addLeg]
  | smul t p hp =>
    unfold singleFlux exportFlux at hp ⊢
    have ht (a : Axis) (y) : current v (pulse (t • p) x) f a y = t * current v (pulse p x) f a y := by
      unfold current; simp_rw [pulse_scale,cross_comm (t • _) f,cross_stretch, ← cross_comm (pulse p x) f,
        Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..
    simp_rw [ht, show ∀ a y, grad a χ y • (t * current v (pulse p x) f a y) =
      t * (grad a χ y • current v (pulse p x) f a y) from fun a y => mul_left_comm .., integral_const_mul, ← Finset.mul_sum]
    rw [← mul_neg, hp hw, mul_neg,sample_smulLeg]
  | vars u c i l =>
    induction j generalizing x with
    | zero =>
      rw [sample_leg u c i l h hU (hs (enclosed _ hw)),coeff_apply_zero];
      rw [show leg u c i l = omegaLeg c i l by unfold omegaLeg; rw [show u = fun _ => 0 from Subsingleton.elim ..]]
      exact local_force hU f H v hv χ hχ Hχ hs hw i l c
    | succ j ih =>
      let p := leg (Fin.tail u) c i l
      let X (t : ℝ) := x+t • u 0
      have hx : X 0 = x := by simp [X]
      have hc : Continuous X := by unfold X; fun_prop
      have he := deriv_flux H hv hχ Hχ hs hw p (u 0)
      have hu : HasDerivAt X (u 0) 0 := by
        refine (((hasDerivAt_id' (0:ℝ)).smul_const (u 0)).const_add x).congr_deriv ?_
        simp
      have hs' : X 0 ∈ U := hx.symm ▸ hs (enclosed _ hw)
      have hg := (((sample_smooth p h hs').differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hu).neg
      have hd : singleFlux v χ (pulse (raiseLeg (u 0) p) x) f = -D (u 0) (sample p (variation v f)) x := by
        refine he.unique ((hg.congr_deriv (by rw [hx]; rfl)).congr_of_eventuallyEq ?_)
        filter_upwards [(show Tendsto X (𝓝 0) (𝓝 x) from hx ▸ (show Tendsto X (𝓝 0) (𝓝 (X 0)) from hc.continuousAt)) hw.eventuallyEq_nhds] with t ht
        exact ih (Fin.tail u) ht
      rw [sample_deriv p (u 0) (fun a b => (h.smooth a b x (hs (enclosed _ hw))).of_le
        (WithTop.coe_le_coe.mpr le_top)), sample_deriv_label _ p h hU (hs (enclosed _ hw))] at hd
      unfold p at hd; rw [raises, Fin.cons_self_tail] at hd
      let t : ℝ := (↑(j+1 : ℕ) : ℝ)
      have ht' (a : Axis) (y) : current v (pulse (t • leg u c i l) x) f a y =
          t * current v (pulse (leg u c i l) x) f a y := by
        unfold current; simp_rw [pulse_scale,cross_comm (t • _) f,cross_stretch, ← cross_comm (pulse (leg u c i l) x) f,
          Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..
      rw [show (↑(j+1 : ℕ):ℝ) = t from rfl, sample_smulLeg, singleFlux,exportFlux] at hd
      simp_rw [ht',show ∀ a y, grad a χ y • (t * current v (pulse (leg u c i l) x) f a y) =
        t * (grad a χ y • current v (pulse (leg u c i l) x) f a y) from fun a y => mul_left_comm ..,
        integral_const_mul, ← Finset.mul_sum] at hd
      rw [← mul_neg, ← mul_neg] at hd
      exact mul_left_cancel₀ (by dsimp [t]; positivity : t≠0) hd

end Charge

end YM.Maxwell.Free
