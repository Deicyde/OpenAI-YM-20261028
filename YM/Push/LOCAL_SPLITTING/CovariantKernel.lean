import YM.Push.LOCAL_SPLITTING.Marginal
import YM.Work.A15

/-! Local marginal passes have true gauge and matched-hierarchy covariance on
any observation support, even if paths, tags and switches in the fine
variables are nonlocal for that support. Not the assertion that a whole
pushforward of a local observable only uses edges near the marked subset.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Filter Lattice Wilson RG MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)

theorem pdf_gauge (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) (k : Site f → G.El) (U : Config G f) (V : Config G c) :
    pdf S β J (gauge k U) (gauge (k ∘ S.ratio.embed) V) = pdf S β J U V := by
  apply Finset.sum_congr rfl; intro i _
  have he : S.likelihood (Lattice.gauge k U) i=S.likelihood U i := by
    unfold StepData.likelihood; apply congr_arg₂
    · refine Finset.prod_congr rfl fun j _ => ?_; rw [expandAt_gauge]; exact (S.patch.frame_gauged h ..).1
    refine Finset.prod_congr rfl fun j _ => ?_; rw [S.updateGauged h]; exact (S.patch.bond_gauge (h:=h) ..).1
  rw [he]; unfold noisy; apply congr_arg
  refine Finset.prod_congr rfl fun j _ => ?_; unfold StepData.prediction; rw [S.updateGauged h, (S.patch.bond_gauge (h:=h) ..).2]
  have hh (u v x y : G.El) : S.penaltyWeight β (u*x*v⁻¹*(u*y*v⁻¹)⁻¹)=S.penaltyWeight β (x*y⁻¹) := by
    unfold StepData.penaltyWeight; rw [show u*x*v⁻¹*(u*y*v⁻¹)⁻¹=u*(x*y⁻¹)*u⁻¹ by group,G.price_conj]
  simp only [Lattice.gauge,Function.comp_apply,hh]







variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pass_gauge (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) {F : Config G f → E} (hg : GaugeInvariant F) : GaugeInvariant (pass S β J F) := by
  intro k V
  let a := k ∘ S.ratio.parent
  have hc : Continuous (gauge a : Config G f → Config G f) := by unfold Lattice.gauge; fun_prop
  have he : Injective (gauge a) := fun x y he => funext fun j => by simpa [Lattice.gauge] using congr_fun he j
  have hi := (hc.isClosedEmbedding he).measurableEmbedding.integral_map (μ := prior G _) (fun W => pdf S β J W (gauge k V) • F W)
  rw [(prior_gauge a).map_eq] at hi
  conv_rhs at hi => simp only [hg a]; rw [← show a ∘ S.ratio.embed=k from funext fun i => congr_arg k (S.ratio.embed_parent i)]
  simp only [pdf_gauge S β J h] at hi; exact hi



theorem pass_local (β : ℝ) (X : Support c) (F : Config G f → E) : LocalOn X (pass S β (edges X) F) := by
  intro V Y h; unfold pass pdf weights noisy
  congr! 2 with U; apply congr_arg (· • F U : ℝ → E); refine Finset.sum_congr rfl fun i _ => congr_arg (S.likelihood U i * ·) (Finset.prod_congr rfl fun j hj => ?_)
  obtain ⟨_,h1,h2⟩ := Finset.mem_filter.mp hj
  rw [h _ h1 h2]

theorem pass_continuous (β : ℝ) (J : Edges c) (h : S.patch.Branches S.kernel G) {F : Config G f → E} (hf : Integrable F (prior G f)) : Continuous (pass S β J F) := by
  -- local change of variables via `plog`, enough that the torus itself is finite
  rw [continuous_iff_continuousAt]; intro V
  let q (U : Config G c) : Directions G c := fun i => G.plog (G.mat (U i * (V i)⁻¹))
  have he (i) : Continuous (fun U : Config G c => U i * (V i)⁻¹) := by fun_prop
  have hQ : Tendsto q (𝓝 V) (𝓝 0) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    have hi := ((he i).tendsto V); rw [mul_inv_cancel] at hi
    simpa [q,comp_def] using G.plog_diff.continuousAt.tendsto.comp ((G.mat_one ▸ G.continuous_mat.continuousAt.tendsto).comp hi)
  have ht : ∀ᶠ U in 𝓝 V, increment V (q U) = U := by
    suffices he : ∀ i, ∀ᶠ U in 𝓝 V, G.lieExp (q U i) = U i * (V i)⁻¹ by
      filter_upwards [eventually_all.mpr he] with U hu; funext i; rw [increment,hu, inv_mul_cancel_right]
    intro i; exact ((he i).tendsto V).eventually ((show V i * (V i)⁻¹ = 1 by group).symm ▸ G.plog_right)
  have h0 := (smooth_pass S β J h hf V 0).continuousAt.tendsto.comp hQ
  rw [comp_apply,Work.G07.at_zero_increment] at h0
  exact h0.congr' (ht.mono fun U hu => congr_arg (pass S β J F) hu)
end YM.Push.Local.Kernel
