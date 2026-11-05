import YM.Push.LOOP_COEFFICIENT.Rooted

/-!
# Conjugation and gauge Ward at the common real origin
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Lattice Wilson RG Matrix Function Filter Set Precision Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}
    {m k : Type} [Fintype m] [Fintype k]

abbrev Scene (G : Gauge) (c f : Side) := Loops.Links G c × Loops.Dual G c f
abbrev Actors (G : Gauge) (c f : Side) := Nodes G c × Nodes G f
abbrev Worlds (G : Gauge) (c f : Side) := Config G c × Loops.Inputs G c f

def strain (t : S.Choices) (p : Clip) (W : PathData G) (x : Scene G c f) :=
    completed p W t (vary 1 x.1) (vary 1 x.2)

def expense (t : S.Choices) (p : Clip) (W : PathData G) (x : Scene G c f) :=
    scalar p W t (vary 1 x.1) (vary 1 x.2)

def correction (W : PathData G) (x : Scene G c f) := loop W (positions (vary 1 x.2))

def fee (μ : ℝ) (p : Clip) (W : PathData G) (x : Loops.Links G n) := scalarRef μ p W (vary 1 x)

variable {p : Clip} {W : PathData G} {σ C Λ : ℝ} {t : S.Choices}

lemma strain_diff (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) : ContDiffAt ℝ ω (strain t p W) 0 :=
  completed_diff h hw t (x:= (0:Scene G c f)) (vary_zero _) ((matDiffAt_const 1).vary contDiffAt_snd) ((matDiffAt_const 1).vary contDiffAt_fst)

lemma loop_diff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {U : E → Config G n} (hu : MatDiffAt U x)
    (hw : W.Bounds p σ C Λ) : ContDiffAt ℝ ω (loop W ∘ U) x := by
  apply contDiffAt_const.mul
  refine ContDiffAt.sum fun s _ => Work.F02.uncut_contDiffAt hw.width hw.two (A:=pull s 0 ∘ U) (fun i => ?_)
  dsimp only [Function.comp_apply]; unfold pull Step.read; split
  · exact mat_inv_diff (hu _)
  exact hu _

lemma correction_diff (hw : W.Bounds p σ C Λ) : ContDiffAt ℝ ω (correction (c:=c) (f:=f) W) 0 :=
  loop_diff (U:=fun x : Scene G c f => positions (vary 1 x.2)) (x:=0) (fun i => ((matDiffAt_const (x:=(0:Scene G c f)) (1:Loops.Inputs G c f)).vary contDiffAt_snd) (.inl i)) hw

lemma expense_diff (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hv : IsUnit (vector p W t 1 1)) :
    ContDiffAt ℝ ω (expense t p W) 0 := by
  have hU := (matDiffAt_const (x:=(0:Scene G c f)) (1:Loops.Inputs G c f)).vary contDiffAt_snd
  have hV := (matDiffAt_const (x:=(0:Scene G c f)) (1:Config G c)).vary contDiffAt_fst
  have h1 : vary (1:Loops.Inputs G c f) (0:Scene G c f).2 = 1 := vary_zero _
  exact (contDiffAt_const.mul (logdet_contDiff (smooth_vector h hw t (U:=fun z => vary 1 z.2) (V:=fun z => vary 1 z.1) (x:=(0:Scene G c f)) h1 hU hV) (by
    simp only [Prod.fst_zero,Prod.snd_zero,vary_zero]; exact (isUnit_iff_isUnit_det _).mp hv))).sub
    (logdet_contDiff (smooth_ghost (mu S) (x:=(0:Scene G c f)) (U:=fun z => positions (vary (1:Loops.Inputs G c f) z.2)) (fun i => hU (.inl i))) ((isUnit_iff_isUnit_det _).mp (ghost_pos _ _ mu_pos).isUnit))

lemma fee_diff (hw : W.Bounds p σ C Λ) {μ : ℝ} (hμ : 0 < μ) (hv : IsUnit (reference μ p W (n:=n) 1)) :
    ContDiffAt ℝ ω (fee (n:=n) μ p W) 0 :=
  (contDiffAt_const.mul (logdet_contDiff (smooth_reference hμ hw (U:=vary (1:Config G n)) vary_diff) (by
    simp only [vary_zero]; exact (isUnit_iff_isUnit_det _).mp hv))).sub
    (logdet_contDiff (smooth_ghost μ vary_diff) ((isUnit_iff_isUnit_det _).mp (ghost_pos _ _ hμ).isUnit))

lemma joint_cohort_flat {f : Array G m × Array G k → ℝ} (h : G.Simple) (hd : DifferentiableAt ℝ f 0)
    (hi : ∀ u : G.El, (fun x => f (Cohort u x.1,Cohort u x.2)) =ᶠ[𝓝 0] f) : fderiv ℝ f 0 = 0 := by
  let A := Array G m
  let B := Array G k
  let L := ContinuousLinearMap.inl ℝ A B
  let R := ContinuousLinearMap.inr ℝ A B
  have he : Tendsto L (𝓝 0) (𝓝 0) := by simpa using L.continuous.tendsto (0:A)
  have hE : Tendsto R (𝓝 0) (𝓝 0) := by simpa using R.continuous.tendsto (0:B)
  have hL : fderiv ℝ f 0 ∘L L = 0 := by
    have ht : DifferentiableAt ℝ f (L 0) := by rwa [map_zero]
    rw [show fderiv ℝ f 0 ∘L L = fderiv ℝ (f ∘ L) 0 by rw [fderiv_comp 0 ht L.differentiableAt,L.fderiv,map_zero]]
    exact cohort_flat h (ht.comp 0 L.differentiableAt) (fun u => (he.eventually (hi u)).mono fun v hv => by simpa [L, Function.comp] using! hv)
  have hR : fderiv ℝ f 0 ∘L R = 0 := by
    have ht : DifferentiableAt ℝ f (R 0) := by rwa [map_zero]
    rw [show fderiv ℝ f 0 ∘L R = fderiv ℝ (f ∘ R) 0 by rw [fderiv_comp 0 ht R.differentiableAt,R.fderiv,map_zero]]
    exact cohort_flat h (ht.comp 0 R.differentiableAt) (fun u => (hE.eventually (hi u)).mono fun v hv => by simpa [R, Function.comp] using! hv)
  apply ContinuousLinearMap.ext
  rintro ⟨v,w⟩
  change fderiv ℝ f 0 (v,w) = 0
  rw [show (v,w)=L v+R w by simp [L,R], map_add,
    show fderiv ℝ f 0 (L v)=0 from DFunLike.congr_fun hL v, show fderiv ℝ f 0 (R w)=0 from DFunLike.congr_fun hR w,add_zero]

def constantGauge (u : G.El) : NodeField G n := fun _ => u

lemma vary_link_color (u : G.El) (a : Loops.Links G n) : vary 1 (Cohort u a) = Lattice.gauge (constantGauge u) (vary 1 a) := by
  funext i; simp only [vary_one, Lattice.gauge,constantGauge,paint_cohort,exp_adjoint]

lemma vary_joint_color (u : G.El) (a : Loops.Dual G c f) : vary 1 (Cohort u a) =
    gaugeJoint S (constantGauge u) (constantGauge u) (vary 1 a) := by
  funext i; simp only [vary_one,paint_cohort,exp_adjoint]; rcases i with i|i <;> simp [constantGauge,gaugeJoint,auxiliaries,positions, Lattice.gauge]

lemma strain_flat (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hG : G.Simple) : fderiv ℝ (strain t p W) 0 = 0 :=
  joint_cohort_flat hG ((strain_diff h hw).differentiableAt (by simp)) (fun u => Eventually.of_forall (fun x => by
    unfold strain; simp only [vary_link_color,vary_joint_color (S:=S),completed_gauge h hw]))

lemma correction_flat (hw : W.Bounds p σ C Λ) (hG : G.Simple) : fderiv ℝ (correction (c:=c) (f:=f) W) 0 = 0 :=
  joint_cohort_flat hG ((correction_diff hw).differentiableAt (by simp)) (fun u => Eventually.of_forall (fun x => by
    change loop W (positions (vary 1 (Cohort u x.2))) = _; rw [show positions (vary 1 (Cohort u x.2)) = Lattice.gauge (constantGauge u) (positions (vary 1 x.2)) by
      funext i; simp [positions, paint_cohort,exp_adjoint, Lattice.gauge,constantGauge],Work.F05.loop_gauge hw]; rfl))

lemma expense_flat (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hv : IsUnit (vector p W t 1 1)) (hG : G.Simple) :
    fderiv ℝ (expense t p W) 0 = 0 :=
  joint_cohort_flat hG ((expense_diff h hw hv).differentiableAt (by simp)) (fun u => by
    have he : Tendsto (fun x : Scene G c f => vary (1:Loops.Inputs G c f) x.2) (𝓝 0) (𝓝 1) := by
      simpa only [Prod.snd_zero,Function.comp_apply,vary_zero] using! (vary_cont (U:= (1:Loops.Inputs G c f))).continuousAt.comp
        (continuous_snd (X:=Loops.Links G c)).continuousAt (x:=0) |>.tendsto
    have ht : Tendsto (fun x : Scene G c f => vary (1:Loops.Inputs G c f) (Cohort u x.2)) (𝓝 0) (𝓝 1) := by
      have hc := vary_cont (U:= (1:Loops.Inputs G c f)) |>.comp ((Cohort u).toContinuousLinearMap.continuous.comp
        (continuous_snd (X:=Loops.Links G c)))
      simpa only [Function.comp_apply, Prod.snd_zero, LinearMap.coe_toContinuousLinearMap, map_zero,vary_zero] using! hc.continuousAt (x:=0) |>.tendsto
    filter_upwards [he.eventually (beam_near h t),ht.eventually (beam_near h t)] with x hx hy
    change Beam t (vary 1 (Cohort u x.2)) at hy
    rw [vary_joint_color (S:=S)] at hy
    unfold expense; rw [vary_joint_color (S:=S),vary_link_color]; exact scalar_gauge h hw t _ _ _ hx hy)

lemma fee_flat (hw : W.Bounds p σ C Λ) {μ : ℝ} (hμ : 0 < μ) (hv : IsUnit (reference μ p W (n:=n) 1)) (hG : G.Simple) :
    fderiv ℝ (fee (n:=n) μ p W) 0 = 0 :=
  cohort_flat hG ((fee_diff hw hμ hv).differentiableAt (by simp)) (fun u => Eventually.of_forall fun x => by
    rw [Function.comp_apply,fee, vary_link_color,scalarRef_gauge hw]; rfl)

section ward
variable {X E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma ward_calculus {H : X × E → E} {f : E → ℝ} (hH : ContDiffAt ℝ ω H 0) (he : H 0 = 0) (hf : ContDiffAt ℝ ω f 0)
    (hz : fderiv ℝ f 0 = 0) (hw : ∀ᶠ x in 𝓝 0,H (0,x)=x) (hg : ∀ᶠ x : X × E in 𝓝 0,f (H x) = f x.2)
    (u : X) (v : E) : iteratedFDeriv ℝ 2 f 0 ![fderiv ℝ H 0 (u,0),v] = 0 := by
  let L := ContinuousLinearMap.inr ℝ X E
  let P := ContinuousLinearMap.snd ℝ X E
  have hD : fderiv ℝ H 0 (0,v) = v := by
    change (H ∘ L) =ᶠ[𝓝 0] id at hw
    have he := hw.fderiv_eq (𝕜:=ℝ)
    rw [fderiv_id, fderiv_comp 0 ((show ContDiffAt ℝ ω H (L 0) by rwa [map_zero]).differentiableAt (by simp)) L.differentiableAt,
      map_zero,L.fderiv] at he
    exact DFunLike.congr_fun he v
  change (f ∘ H) =ᶠ[𝓝 0] (f ∘ P) at hg
  have heq := DFunLike.congr_fun (Work.F05.bend_congr hg) (u,0)
  rw [Work.F05.bend_comp_stationary (he.symm ▸ hf) hH (he.symm ▸ hz),he,
    Work.F05.bend_comp_stationary (P.map_zero.symm ▸ hf) P.contDiff.contDiffAt (P.map_zero.symm ▸ hz),P.fderiv] at heq
  have hh := DFunLike.congr_fun heq (0,v)
  simp only [LinearMap.compl₁₂_apply,Work.F05.bend_apply] at hh
  rw [← hD]; refine hh.trans ?_
  rw [← Work.F05.bend_apply]; change Work.F05.bend _ _ 0 v = 0; rw [map_zero]; rfl
end ward

def switchGauge (S : StepData c f) (x : Actors G c f × Scene G c f) : Scene G c f :=
  let u := vary 1 x.1.1; let k := vary 1 x.1.2
  (displacement 1 (Lattice.gauge u (vary 1 x.2.1)), displacement 1 (gaugeJoint S k u (vary 1 x.2.2)))

lemma switchGauge_diff : ContDiffAt ℝ ω (switchGauge (G:=G) S) 0 :=
  ((matDiffAt_const _).displacement (gauge_diff ((matDiffAt_const 1).vary contDiffAt_fst.fst)
    ((matDiffAt_const 1).vary contDiffAt_snd.fst)) (by simp)).prodMk
  ((matDiffAt_const _).displacement (gaugeJoint_diff ((matDiffAt_const 1).vary contDiffAt_snd.snd) ((matDiffAt_const 1).vary contDiffAt_fst.fst)
    ((matDiffAt_const 1).vary contDiffAt_fst.snd)) (by simp))

def generator (S : StepData c f) (v : Actors G c f) := fderiv ℝ (switchGauge S) 0 (v,0)

lemma Scene_ward {F : Worlds G c f → ℝ}
    (hv : ∀ᶠ x : Actors G c f × Scene G c f in 𝓝 0,
      F (Lattice.gauge (vary 1 x.1.1) (vary 1 x.2.1),gaugeJoint S (vary 1 x.1.2) (vary 1 x.1.1) (vary 1 x.2.2)) = F (vary 1 x.2.1,vary 1 x.2.2))
    (hd : ContDiffAt ℝ ω (fun x : Scene G c f => F (vary 1 x.1,vary 1 x.2)) 0) (hf : fderiv ℝ (fun x : Scene G c f => F (vary 1 x.1,vary 1 x.2)) 0 = 0)
    (u v) : iteratedFDeriv ℝ 2 (fun x : Scene G c f => F (vary 1 x.1,vary 1 x.2)) 0 ![generator S u,v] = 0 := by
  apply ward_calculus (H:=switchGauge (G:=G) S) switchGauge_diff (by simp [switchGauge]) hd hf
  · have he := continuous_fst.tendsto (0:Scene G c f); have hh := continuous_snd.tendsto (0:Scene G c f)
    filter_upwards [he.eventually (displacement_vary 1),hh.eventually (displacement_vary 1)] with x hc hh
    exact Prod.ext (by simpa [switchGauge] using! hc) (by simpa [switchGauge] using! hh)
  have h1 := (gauge_diff (x:= (0:Actors G c f × Scene G c f)) ((matDiffAt_const 1).vary contDiffAt_fst.fst) ((matDiffAt_const 1).vary contDiffAt_snd.fst)).continuousAt.tendsto
  have h2 := (gaugeJoint_diff (x:=(0:Actors G c f × Scene G c f)) (S:=S) ((matDiffAt_const 1).vary contDiffAt_snd.snd)
    ((matDiffAt_const 1).vary contDiffAt_fst.fst) ((matDiffAt_const 1).vary contDiffAt_fst.snd)).continuousAt.tendsto
  simp only [Prod.fst_zero,Prod.snd_zero,vary_zero,gauge_one,gaugeJoint_one] at h1 h2
  filter_upwards [h1.eventually (vary_displacement 1),h2.eventually (vary_displacement 1),hv] with x h1 h2 hv
  dsimp only [switchGauge]; rw [h1,h2]; exact hv

lemma strain_ward (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hG : G.Simple) (u v) :
    iteratedFDeriv ℝ 2 (strain t p W) 0 ![generator S u,v] = 0 := Scene_ward (F:=uncurry (completed p W t))
      (Eventually.of_forall (fun _ => completed_gauge h hw ..)) (strain_diff h hw) (strain_flat h hw hG) u v

lemma expense_ward (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (hG : G.Simple) (hN : IsUnit (vector p W t 1 1)) (u v) :
    iteratedFDeriv ℝ 2 (expense t p W) 0 ![generator S u,v] = 0 := by
  have hU := ((matDiffAt_const (1:Loops.Inputs G c f)).vary (contDiffAt_snd (p:= (0:Actors G c f × Scene G c f))).snd)
  have h1 := hU.continuousAt.tendsto
  have h2 := (gaugeJoint_diff (S:=S) hU ((matDiffAt_const 1).vary contDiffAt_fst.fst) ((matDiffAt_const 1).vary contDiffAt_fst.snd)).continuousAt.tendsto
  simp only [Prod.fst_zero,Prod.snd_zero,vary_zero,gaugeJoint_one] at h1 h2
  apply Scene_ward (F:=uncurry (scalar p W t)) ?_ (expense_diff h hw hN) (expense_flat h hw hN hG)
  filter_upwards [h1.eventually (beam_near h t),h2.eventually (beam_near h t)] with x h1 h2
  exact scalar_gauge h hw t _ _ _ h1 h2

lemma correction_ward (hw : W.Bounds p σ C Λ) (hG : G.Simple) (u v) :
    iteratedFDeriv ℝ 2 (correction W) 0 ![generator S u,v] = 0 := Scene_ward (F:=fun x => loop W (positions x.2))
      (Eventually.of_forall (fun _ => Work.F05.loop_gauge hw ..)) (correction_diff hw) (correction_flat hw hG) u v
end YM.Push.Loops
