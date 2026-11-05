import YM.Extra.WILSON_STARTUP.Metric

/-! # Unmasked top `Planned.peak` compatibility on actual real plane -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Design
open Function Filter RG Wilson Lattice Bloch Work Precision Exterior
open scoped Topology Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {n : Side} (p : Clip)

def diff (p : Clip) (U : Config G n) := ∑ i : Cell n, bulk p * residual G i U

lemma diff_pull (U : Config G n) (s : Signed) : diff p (pull s 0 U) = diff p U := by
  unfold diff; simp_rw [← residual_send]
  exact Equiv.sum_comp (Equiv.ofBijective _ ⟨Face.injective_send s (0:Site n), Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩)
      (fun q : Cell n => bulk p * residual G q U)

lemma main_top (U : Config G n) (hp : p.direct ≤ 1) : mainTerm p (top G p) U = energy U - diff p U := by
  have h (s : Signed) := principal_top p (pull s 0 U) hp
  change ∀ s, _ + diff p (pull s 0 U)=_ at h
  simp_rw [diff_pull,energy_pull,← eq_sub_iff_add_eq] at h
  unfold mainTerm Patch.average
  dsimp only; simp_rw [h]; simp [mul_sub]

theorem match_top (hp : p.direct ≤ 1) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Config G n) (hU : U 0 = 1) (hd : ∀ i,ContDiffAt ℝ ω (fun a => G.mat (U a i)) 0) :
    ∀ j ≤ 4, SameJet j (mainTerm p (top G p) ∘ U) (energy ∘ U) := by
  have hm (q : Cell n) : ContDiffAt ℝ ω (fun a => G.mat (faceValue (U a) q)) 0 := by
    simp only [← read_edges, ← Quad.read_actual]
    exact Quad.readMat_diff.contDiffAt.comp _ (contDiffAt_pi.mpr fun i => hd _)
  have he : ContDiffAt ℝ ω (energy ∘ U) 0 := ContDiffAt.sum fun q _ => F03.price_smooth (hm q)
  let f := fun (q : Cell n) => residual G q ∘ U
  have hr (q) : ContDiffAt ℝ ω (f q) 0 := by
    simp only [f,comp_def,residual,← Quad.surplus_actual]; exact Quad.surplusMat_diff.contDiffAt.comp _ (hm q)
  have hf (q) : FlatAt 5 (f q) 0 := surplus_jet _ (by rw [hU,face_one]) (hm q)
  have ht : mainTerm p (top G p) ∘ U = energy ∘ U - bulk p • ∑ q : Cell n,f q := funext fun a => by
    simp only [comp_apply,main_top p _ hp, Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul, Finset.mul_sum, diff]; rfl
  intro j hj; rw [ht]
  have hS : ContDiffAt ℝ ω (∑ q : Cell n,f q) 0 := by
    rw [show (∑ q : Cell n, f q) = fun a => ∑ q, f q a from funext fun _ => Finset.sum_apply ..]
    exact ContDiffAt.sum fun q _ => hr q
  have ha : ContDiffAt ℝ ω (bulk p • ∑ q : Cell n,f q) 0 := hS.const_smul (bulk p)
  refine ⟨he.sub ha,he,?_⟩
  rw [iteratedFDeriv_sub_apply (he.of_le le_top) (ha.of_le le_top),iteratedFDeriv_const_smul_apply (hS.of_le le_top),
      iteratedFDeriv_sum_apply (fun q _ => (hr q).of_le le_top)]
  simp only [fun q => hf q j (by omega), Finset.sum_const_zero, smul_zero,sub_zero]

theorem peak (hp : p.direct ≤ 1) : ∀ j ≤ 4, SameJet j
    (fun x : fieldDir G n 1 => mainTerm p (top G p) (represent x)) (energy ∘ represent) :=
  match_top p hp represent link_one fun i => (F03.represent_smooth i).contDiffAt

structure Suitable (G : Gauge) (p : Stage) : Prop where
  direct : p.clip.direct ≤ 1
  paths : (top G p.clip).Bounds p.clip p.width p.paths 0

theorem readiness (G : Gauge) {p : Stage} (hp : p.clip.direct ≤ 1) : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p' : Stage,
    p'.clip=p.clip → p'.width=p.width → C₀ ≤ p'.paths → Suitable G p' := by
  obtain ⟨C₀,h,H⟩ := bound_arbitrary _ G hp _ p.width_pos
  exact ⟨C₀,h,fun p' hx hy hz => by rw [← hx] at hp; rw [← hx,← hy] at H; exact ⟨hp,H _ hz 0 le_rfl⟩⟩

theorem layout_ready {a : Levels G} {N : ℕ} (h : Suitable G (a.params N)) :
    (top G (a.params N).clip).Bounds (a.params N).clip (a.params N).width (a.params N).paths (a.clock.loopCap N) := by
  have he := h.paths.two
  refine { h.paths with two := ⟨he.1,he.2.1, he.2.2.trans ?_⟩ }
  unfold Calendar.loopCap Calendar.monitor; positivity
end YM.WilsonStartup.Design
