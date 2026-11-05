import YM.Push.LOOP_COEFFICIENT.Admission
import YM.Push.LOOP_COEFFICIENT.Orientation

/-!
# Finite scalar evaluation and exact Ward, orientation and color tests

Second derivative is the mixed second field variation (precision), not
its Taylor half. For the signed transforms we can transport the graph and
tag simultaneously; no commuting assumptions on A and the spin matrices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Lattice RG Wilson Precision Exterior Tree
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {W : PathData G} {ρ : fieldDir G c 1 → AxisChart G F} {P : ChartRatio G}
    {A : Matrix (Body 1 f) (Body 1 c) ℝ}

-- A helper on feasible full-field germs.
structure Balanced (S : StepData c f) (f : Scene G c f → ℝ) : Prop where
  smooth : ContDiffAt ℝ ω f 0
  stationary : fderiv ℝ f 0 = 0
  nulls (v : Actors G c _) (x : Scene G c _) : Work.F05.bend f 0 (generator S v) x = 0

lemma bend_linear {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H] (L : E →L[ℝ] H)
    {f : H → ℝ} (hf : ContDiffAt ℝ ω f 0) (x y : E) : Work.F05.bend (f ∘ L) 0 x y = Work.F05.bend f 0 (L x) (L y) := by
  rw [Work.F05.bend_apply,Next.Foundations.jets_linear _ (hf.of_le le_top),Work.F05.bend_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1; ext1 i; fin_cases i <;> rfl

lemma Balanced.symmetric {g : Scene G c f → ℝ} (h : Balanced S g) (x y) : Work.F05.bend g 0 x y = Work.F05.bend g 0 y x := h.smooth.isSymmSndFDerivAt_of_omega ..

lemma Balanced.add {g₁ g₂ : Scene G c f → ℝ} (h₁ : Balanced S g₁) (h₂ : Balanced S g₂) : Balanced S (g₁ + g₂) :=
  ⟨h₁.smooth.add h₂.smooth, by rw [fderiv_add (h₁.smooth.differentiableAt (by simp)) (h₂.smooth.differentiableAt (by simp)),h₁.stationary,h₂.stationary,add_zero],
    fun v x => by rw [Work.F05.bend_apply, iteratedFDeriv_add_apply (h₁.smooth.of_le le_top) (h₂.smooth.of_le le_top), _root_.add_apply,
      ← Work.F05.bend_apply,← Work.F05.bend_apply,h₁.nulls,h₂.nulls,add_zero]⟩

namespace Admission
variable (h : Admission F ρ p W A P) (t : S.Choices)
include h
lemma strain_balanced : Balanced S (strain t p W) := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  exact ⟨strain_diff h.branches hw,strain_flat h.branches hw h.simple,fun _ _ => (Work.F05.bend_apply ..).trans (strain_ward h.branches hw h.simple ..)⟩

lemma expense_balanced : Balanced S (expense t p W) := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  exact ⟨expense_diff h.branches hw (h.invert_vector t),expense_flat h.branches hw (h.invert_vector t) h.simple,
    fun _ _ => (Work.F05.bend_apply ..).trans (expense_ward h.branches hw h.simple (h.invert_vector t) ..)⟩

lemma correction_balanced : Balanced S (correction W) := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  exact ⟨correction_diff hw, correction_flat hw h.simple,fun _ _ => (Work.F05.bend_apply ..).trans (correction_ward hw h.simple ..)⟩

lemma modulo_left {J : Scene G c f → ℝ} (hJ : Balanced S J) {x : Scene G c f} (hx : LinearStation t p W x) (y) :
    Work.F05.bend J 0 x y = Work.F05.bend J 0 (graft G S A x.1) y := by
  generalize ha : x.1 = a
  obtain ⟨v,hv⟩ := h.modulo_gauge t hx (h.graft_station t a) ha
  rw [hv,map_add,LinearMap.add_apply,hJ.nulls,add_zero]

lemma equals_kernel {J : Scene G c f → ℝ} (hJ : Balanced S J) {x y : Scene G c f}
    (hx : LinearStation t p W x) (hy : LinearStation t p W y) :
    Work.F05.bend J 0 x y = Work.F05.bend (J ∘ graft G S A) 0 x.1 y.1 := by
  rw [h.modulo_left t hJ hx,hJ.symmetric,h.modulo_left t hJ hy,hJ.symmetric,bend_linear _ hJ.smooth]

include t in
lemma graft_null {J : Scene G c f → ℝ} (hJ : Balanced S J) v x :
    Work.F05.bend (J ∘ graft G S A) 0 (R_g 1 *ᵥ v) x = 0 := by
  have he : R_g 1 *ᵥ v = (generator S (v, (0:Nodes G f))).1 := (generator_fst (S:=S) (v,(0:Nodes G f))).symm
  have hh : LinearStation t p W (generator S (v,0)) := fun a => (h.strain_balanced t).nulls _ _
  rw [he,← show (graft G S A x).1 = x from rfl]
  exact (h.equals_kernel t hJ hh (h.graft_station t x)).symm.trans (hJ.nulls _ _)

include t in
lemma equals_sampled {J : Scene G c f → ℝ} (hJ : Balanced S J) :
    Work.F05.bend (J ∘ sampled F ρ) 0 = Work.F05.bend (J ∘ graft G S A) 0 := by
  have he := sampled_zero F h.critical
  rw [Work.F05.bend_comp_stationary (he.symm ▸ hJ.smooth) (sampled_diff F h.critical) (he.symm ▸ hJ.stationary),he]
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
  rw [LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe,h.equals_kernel t hJ (h.sampled_linearStation t x) (h.sampled_linearStation t y)]
  simp only [sampled_stationary F _ h.critical h.linear]; rfl
end Admission

def charge (t : S.Choices) (p : Clip) (W : PathData G) := correction W + expense t p W

def onBranch (t : S.Choices) (p : Clip) (W : PathData G) (A : Matrix (Body 1 f) (Body 1 c) ℝ) := charge t p W ∘ graft G S A

namespace Admission
variable (h : Admission F ρ p W A P) (t : S.Choices)
include h
lemma charge_balanced : Balanced S (charge t p W) := h.correction_balanced.add (h.expense_balanced t)





/-- Transport the germ then pass through the quotient (comparison of two tag-dependent functionals). -/
lemma on_motion (t' : S.Choices) {J H : Scene G c f → ℝ} (hJ : Balanced S J) (hH : Balanced S H)
    (L : Matrix (BondKey G c) (BondKey G c) ℝ) (R : Matrix (JointKey G c f) (JointKey G c f) ℝ) (hr : ortho R)
    (he : ∀ x : Scene G c f, strain t' p W (L *ᵥ x.1,R *ᵥ x.2) = strain t p W x)
    (hf : ∀ᶠ x in 𝓝 (0:Loops.Links G c), H (L *ᵥ (sampled F ρ x).1, R *ᵥ (sampled F ρ x).2) = J (sampled F ρ x)) (x y) :
    Work.F05.bend (H ∘ graft G S A) 0 (L *ᵥ x) (L *ᵥ y) = Work.F05.bend (J ∘ graft G S A) 0 x y := by
  let M := ContinuousLinearMap.prodMap (clm L) (clm R)
  have hStat (x) (hx : LinearStation t p W x) : LinearStation t' p W (M x) := by
    intro a
    rw [show ((0:Loops.Links G c),a) = M ((0:Loops.Links G c), R.transpose *ᵥ a) from ?_]
    · rw [← bend_linear M (h.strain_balanced t').smooth, show strain t' p W ∘ M = strain t p W from funext he]; exact hx _
    change _ = (L *ᵥ (0:Loops.Links G c), R *ᵥ R.transpose *ᵥ a)
    rw [Matrix.mulVec_zero,Matrix.mulVec_mulVec,hr.rev,Matrix.one_mulVec]
  have hS := sampled_diff F h.critical
  have hz := sampled_zero F h.critical
  have heq := Work.F05.bend_congr (show (H ∘ M) ∘ sampled F ρ =ᶠ[𝓝 0] J ∘ sampled F ρ from hf)
  have hY : fderiv ℝ (H ∘ M) 0 = 0 := by rw [fderiv_comp 0 (M.map_zero.symm ▸ hH.smooth.differentiableAt (by simp)) M.differentiableAt,
    map_zero, hH.stationary, ContinuousLinearMap.zero_comp]
  have hX := (show ContDiffAt ℝ ω H (M 0) from M.map_zero.symm ▸ hH.smooth).comp 0 M.contDiff.contDiffAt
  rw [Work.F05.bend_comp_stationary (hz.symm ▸ hX) hS (hz.symm ▸ hY), hz,h.equals_sampled t hJ] at heq
  have hxy := DFunLike.congr_fun (DFunLike.congr_fun heq x) y
  rw [LinearMap.compl₁₂_apply,ContinuousLinearMap.coe_coe,bend_linear M hH.smooth,h.equals_kernel t' hH (hStat _ (h.sampled_linearStation t x)) (hStat _ (h.sampled_linearStation t y))] at hxy
  simp only [sampled_stationary F _ h.critical h.linear] at hxy
  exact hxy

lemma charge_orientation (s : Signed) x y :
    let L := linkSpin s (1:Config G c)
    Work.F05.bend (onBranch t p W A) 0 (L *ᵥ x) (L *ᵥ y) = Work.F05.bend (onBranch (S.withinChoice s 0 t) p W A) 0 x y := by
  intro L
  let r := S.withinChoice s 0 t
  let R := jointSpin s (1:Loops.Inputs G c f)
  have h1 (x : Loops.Links G c) : vary 1 (L *ᵥ x) = pull s 0 (vary 1 x) := by
    have he := vary_pull s (1:Config G c) x; simpa only [show pull s 0 (1:Config G c) = 1 by ext1; simp [pull,Step.read]] using he
  have h2 (x : Loops.Dual G c f) : vary 1 (R *ᵥ x) = jointPull s (vary 1 x) := by
    have he : jointPull s (1:Loops.Inputs G c f)=1 := by
      ext1 i; cases i <;> simp [jointPull,positions,auxiliaries,pull,Step.read]
    simpa only [he] using! vary_jointPull s (1:Loops.Inputs G c f) x
  apply h.on_motion r t (h.charge_balanced r) (h.charge_balanced t) L R (jointSpin_ortho ..) _ _
  · intro v; unfold strain; rw [h1,h2]; exact completed_pull s h.branches t _ _
  have ht := sampled_zero F h.critical
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  have hc : Tendsto (fun x => vary 1 (sampled F ρ x).2) (𝓝 0) (𝓝 1) := (show Tendsto (vary (1:Loops.Inputs G c f)) (𝓝 0) (𝓝 1) by
      simpa only [vary_zero] using (vary_cont (U:=(1:Loops.Inputs G c f))).tendsto (0:Loops.Dual G c f)).comp
      ((continuous_snd.tendsto (0:Scene G c f)).comp h.sample_tendsto)
  have hh : Tendsto (fun x => jointPull s (vary 1 (sampled F ρ x).2)) (𝓝 0) (𝓝 1) := by
    have he := ((matDiffAt_const (x:=(0:Loops.Links G c)) 1).vary ((clm R).contDiff.contDiffAt.comp _ (sampled_diff F h.critical).snd)).continuousAt.tendsto
    simpa only [ht, Function.comp_apply,Prod.snd_zero,map_zero,vary_zero,show ∀ x, vary 1 (clm R x) = _ from h2] using! he
  filter_upwards [h.sample_shell r,hc.eventually (beam_near h.branches r),hh.eventually (beam_near h.branches t)] with z hz hb hb'
  have ht := scalar_pull s h.branches hw t hz.1 hb hb'
  simp only [charge, Pi.add_apply,expense,h1,h2, correction]
  exact congr_arg₂ (· + ·) (loop_pull s W _) ht

lemma charge_color (u : G.El) x y :
    let k := constantGauge (n:=c) u
    Work.F05.bend (onBranch t p W A) 0 (linkAdj k *ᵥ x) (linkAdj k *ᵥ y) = Work.F05.bend (onBranch t p W A) 0 x y := by
  obtain ⟨σ,C,Λ,hw⟩ := h.paths
  let k := constantGauge (n:=c) u; intro k'
  let q := constantGauge (n:=f) u
  let R := jointAdj q k
  have h1 (x : Loops.Links G c) : vary 1 (linkAdj k *ᵥ x) = Lattice.gauge k (vary 1 x) := by
    rw [← vary_gauge]; congr; ext1; simp [k, Lattice.gauge,constantGauge]
  have h2 (x : Loops.Dual G c f) : vary 1 (R *ᵥ x) = gaugeJoint S q k (vary 1 x) := by
    rw [← vary_joint]; congr; ext1 i; cases i <;> simp [gaugeJoint,k,q,positions,Lattice.gauge,constantGauge]
  apply h.on_motion t t (h.charge_balanced t) (h.charge_balanced t) _ R (adjoints_ortho _) _ _
  · intro v; unfold strain; change completed _ _ _ (vary 1 (linkAdj k *ᵥ _)) _ = _
    rw [h1,h2,completed_gauge h.branches hw]
  have hc : Tendsto (fun x => vary 1 (sampled F ρ x).2) (𝓝 0) (𝓝 1) := (show Tendsto (vary (1:Loops.Inputs G c f)) (𝓝 0) (𝓝 1) by
      simpa only [vary_zero] using (vary_cont (U:=(1:Loops.Inputs G c f))).tendsto (0:Loops.Dual G c f)).comp
      ((continuous_snd.tendsto (0:Scene G c f)).comp h.sample_tendsto)
  have hh : Tendsto (fun x => gaugeJoint S q k (vary 1 (sampled F ρ x).2)) (𝓝 0) (𝓝 1) := by
    have he := ((matDiffAt_const (x:=(0:Loops.Links G c)) 1).vary ((clm R).contDiff.contDiffAt.comp _ (sampled_diff F h.critical).snd)).continuousAt.tendsto
    simpa only [sampled_zero F h.critical, Function.comp_apply,Prod.snd_zero,map_zero,vary_zero,show ∀ x, vary 1 (clm R x) = _ from h2] using! he
  filter_upwards [hc.eventually (beam_near h.branches t),hh.eventually (beam_near h.branches t)] with z hb hb'
  have ht := scalar_gauge h.branches hw t q k (vary 1 (sampled F ρ z).1) hb hb'
  dsimp only [charge,k',Pi.add_apply,expense,correction]
  rw [h2, h1,ht, show positions (gaugeJoint S q k (vary 1 (sampled F ρ z).2)) = Lattice.gauge q (positions _) from rfl, Work.F05.loop_gauge hw]
end Admission
end YM.Push.Loops
