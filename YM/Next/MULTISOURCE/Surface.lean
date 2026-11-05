import YM.Next.MULTISOURCE.Milk
import YM.Next.MULTISOURCE.Tournesol


/-! Coherent scalar bank → all genuine jets. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Wilson Lattice Finset Filter MeasureTheory Marker MvPolynomial
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {G : Gauge} {c f : Side}
variable {P : Rep G c} {Q : Rep G f} {S : StepData c f}


lemma push_uniform {X : Type*} (V : Config G c) (β : ℝ) (K : Set X)
    (F : ℕ → X → Config G f→ℂ) (H : X → Config G f → ℂ) (ht : S.IsKernel β G)
    (he : ∀ z∈K, Integrable (H z) (prior G _)) (hm : ∀ i, ∀ z∈K, Integrable (F i z) (prior G _))
    (h : TendstoUniformlyOn (fun i (x : X × Config G f) => F i x.1 x.2) (Function.uncurry H) atTop (Set.prod K Set.univ)) :
    TendstoUniformlyOn (fun i z => S.push β (F i z) V) (fun z => S.push β (H z) V) atTop K := by
  obtain ⟨A,hA⟩ := ht.bound; let B := |A|+1; have hb : 0 < B := by unfold B; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr; intro ε hh
  let y := (ε / 2) / B; have hy : 0 < y := div_pos (half_pos hh) hb
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h y hy] with i hi z hz
  simp only [StepData.push, dist_eq_norm]; rw [← integral_sub (StepData.push_slice ht V _ (he z hz))
    (StepData.push_slice ht V _ (hm i z hz))]
  have hc : ∀ U, ‖S.density β U V • H z U - S.density β U V • F i z U‖ ≤ y * B := by
    intro U
    have hg : dist (H z U) (F i z U) < y := hi (z,U) ⟨hz,Set.mem_univ _⟩
    rw [dist_eq_norm] at hg; rw [mul_comm y,← smul_sub,norm_smul]
    rw [Real.norm_of_nonneg (ht.positive U V)]
    exact mul_le_mul ((hA U V).trans ((le_abs_self _).trans (by unfold B; simp))) hg.le (norm_nonneg _) hb.le
  have hf := norm_integral_le_of_norm_le_const (μ:=prior G f) (Eventually.of_forall hc)
  simp only [Measure.real_def,measure_univ, ENNReal.toReal_one,mul_one] at hf
  apply hf.trans_lt; unfold y; rw [div_mul_cancel₀ _ hb.ne']; exact half_lt_self hh

lemma serialize {κ C E σ Λ w η : ℝ} {K : Set (I→ℂ)} (T : Reservoir P I) (A : Census I)
    (ht : Q.Lawful σ C Λ E w) (D : I → Pulse G f) (hc : ∀ i, Envelope (D i).1 ∧ ∀ j, Envelope ((D i).2 j)) (U : Config G c)
    (hx : T.Tested κ K) (he : S.IsKernel Q.beta G) (hp : 0<η) (hf : boxes η ⊆ K)
    (h : ∀ z∈ K, T.signal z=S.push Q.beta (perturbs Q D z)) (q : A.Mode) :
    (many P A (fun i => T.taste (power i.sites)) U).part q=S.push Q.beta (jet Q A D q) U := by
  let r := η/2; have hr : 0<r := half_pos hp; have hv : r<η := half_lt_self hp
  choose g hg H using fun n => list_push S Q.beta he (cup Q D n) (filled Q D n) (cup_pass Q ht D hc n) U
  let u (z : I→ℂ) := S.push Q.beta (perturbs Q D z) U
  have hu : TendstoUniformlyOn (fun n z => eval z (g n)) u atTop (boxes r) := by
    simp_rw [hg]; exact push_uniform U Q.beta (boxes r) (fun i z V => eval z (cup Q D i V)) _ he
      (fun z _ => signal_cast Q ht D hc z) (fun i z _ => cup_pass Q ht D hc i z) (palette Q ht D hc r)
  let s := power q.val
  have hh : ∀ᶠ i in atTop,coeff s (g i)=S.push Q.beta (jet Q A D q) U := by
    filter_upwards [eventually_ge_atTop (Fintype.card I)] with n hn
    rw [H, cup_print Q D A q n hn]
  have hs : TendstoUniformlyOn (fun n z => eval z (displayU T n U)) u atTop (boxes r) := by
    have hh := adequate T hx U hr hv hf
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hA => ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hh ε hA] with i hi z hz
    have hg : z∈K := hf (fun i => (hz i).trans hv.le)
    rw [← show T.signal z U=u z from congr_fun (h z hg) U]; exact hi z hz
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((spare T hx U A q hp hf).sub (tendsto_const_nhds.congr' (hh.mono fun _ he => he.symm))) (settle _ _ u s hr hs hu))
end YM.Multi.Desk
