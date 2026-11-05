import YM.Push.LOOP_COEFFICIENT.Rooted

/-! # Coarse signed symmetry (restored on shell) and permutation symmetry of the fine reference -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Lattice RG Wilson Precision Tree Exterior
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {c f n : Side} {S : StepData c f} (s : Signed)

def spins (V : Config G n) (i : Bonds n) : G.Color →ₗ[ℝ] G.Color := if s.flip i.2 then -G.adjoint (V (sendEdge s 0 i))⁻¹ else LinearMap.id

def linkSpin (V : Config G n) := direct (sendEdge s 0) (spins s V)

def siteSpin (G : Gauge) (n : Side) := direct (s.act (R:=Per n)) (fun _ => (LinearMap.id : G.Color →ₗ[ℝ] G.Color))

def jointSpin (U : Loops.Inputs G c f) := direct (Sum.map (sendEdge s 0) (s.act (R:=Per c)))
  (Sum.elim (spins s (positions U)) (fun _ => LinearMap.id))

def jointPull (U : Loops.Inputs G c f) : Loops.Inputs G c f := Sum.elim (pull s 0 (positions U)) (auxiliaries U ∘ s.act)

lemma linkSpin_ortho (V : Config G n) : ortho (linkSpin s V) := direct_ortho _ (StepData.sendBonds s 0).bijective _
  (fun i v => by unfold spins; split <;> simp)

lemma siteSpin_ortho (G : Gauge) (n : Side) : ortho (siteSpin s G n) := direct_ortho _ s.actEquiv.bijective _ (by intros; rfl)

lemma jointSpin_ortho (U : Loops.Inputs G c f) : ortho (jointSpin s U) := direct_ortho _ ((StepData.sendBonds s 0).sumCongr s.actEquiv.toEquiv).bijective _
  (by rintro (i|i) v
      · dsimp only [Sum.elim_inl]; unfold spins; split <;> simp
      · rfl)

private lemma spin_fee (V : Config G n) (u : Bonds n → G.Color) (i : Bonds n) :
    pull s 0 (fun i => bump (V i) (u i)) i = bump (pull s 0 V i) (spins s V i (u (sendEdge s 0 i))) := by
  cases h : s.flip i.2
  · simp [pull,Step.read,posDir,Step.rotate,h,sendEdge,spins]
  · simp only [pull,Step.read,posDir,Step.rotate,h,sendEdge,spins,Bool.false_xor,↓reduceIte,LinearMap.neg_apply,bump_inverse]

lemma vary_pull (V : Config G n) (v : Loops.Links G n) : vary (pull s 0 V) (linkSpin s V *ᵥ v) = pull s 0 (vary V v) := by
  ext1 i; simpa only [vary,linkSpin,paint_direct] using! (spin_fee s V (paint G (Bonds n) v) i).symm

lemma vary_jointPull (U : Loops.Inputs G c f) (v : Loops.Dual G c f) : vary (jointPull s U) (jointSpin s U *ᵥ v) = jointPull s (vary U v) := by
  funext i; rw [vary,jointSpin,paint_direct]; cases i with
  | inr i => rfl
  | inl i => exact (spin_fee s (positions U) (paint G _ v ∘ Sum.inl) i).symm

lemma R_tot_spin (U : Loops.Inputs G c f) : Carries (jointSpin s U) (siteSpin s G f) (R_tot S U) (R_tot S (jointPull s U)) :=
  joint_R_motion (φ:=jointPull s) (fun v => (vary_jointPull s U v).symm) (fun v => by
    have he (x : Site f) : vary (1:NodeField G f) (siteSpin s G f *ᵥ v) x = vary 1 v (s.act x) := by
      rw [siteSpin,vary,paint_direct]; rfl
    funext i; cases i with
    | inl i =>
      change pull _ _ (Lattice.gauge _ _) i = _
      simp_rw [Work.F05.pull_gauge_zero, affine, add_zero,← he]; rfl
    | inr i =>
      change _ * _ * (vary (1:NodeField G f) v (S.ratio.embed (s.act i)))⁻¹ = _ * _ * _⁻¹
      rw [he,S.ratio.signed]; rfl)

lemma mainTerm_pull (p : Clip) (W : PathData G) (V : Config G n) : mainTerm p W (pull s 0 V) = mainTerm p W V := by
  unfold mainTerm Patch.average
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft s)]
  simp only [pull_pull, affine, Signed.act_zero,add_zero]; rfl

lemma loop_pull (W : PathData G) (V : Config G n) : loop W (pull s 0 V) = loop W V := by
  unfold loop Patch.average
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft s)]
  simp only [pull_pull, affine,Signed.act_zero,add_zero]; rfl

lemma Zmap_pull (h : S.patch.Branches S.kernel G) (t : S.Choices) (U : Loops.Inputs G c f) :
    Zmap t (jointPull s U) = pull s 0 (Zmap (S.withinChoice s 0 t) U) := by
  have he := S.prediction_channel h s 0 (positions U) t
  rw [show S.ratio.embed 0=0 from S.ratio.root.map_zero] at he
  rw [Zmap,show positions (jointPull s U) = pull s 0 (positions U) from rfl,he,Zmap,
      Work.F05.pull_gauge_zero]
  simp only [affine,add_zero]; rfl

lemma penalty_pull (V Z : Config G c) : penalty S (pull s 0 V) (pull s 0 Z) = penalty S V Z := by
  unfold penalty
  conv_rhs => rw [← Equiv.sum_comp (StepData.sendBonds s 0)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold pull Step.read
  let a := V (sendEdge s 0 i); let b := Z (sendEdge s 0 i)
  have he : G.price (a⁻¹ * (b⁻¹)⁻¹) = G.price (a * b⁻¹) := by
    rw [show a⁻¹*((b⁻¹)⁻¹)= a⁻¹ * (a*b⁻¹)⁻¹ * (a⁻¹)⁻¹ by group,G.price_conj,G.price_inv]
  split <;> first | exact he | rfl

lemma completed_pull {p : Clip} {W : PathData G} (h : S.patch.Branches S.kernel G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) :
    completed p W t (pull s 0 V) (jointPull s U) = completed p W (S.withinChoice s 0 t) V U := by
  rw [completed,Zmap_pull s h,penalty_pull,show positions (jointPull s U) = pull s 0 (positions U) from rfl,mainTerm_pull,completed]

lemma scalar_pull {p : Clip} {W : PathData G} {σ C Λ : ℝ} {V : Config G c} {U : Loops.Inputs G c f}
    (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices)
    (hS : AtStation p W (S.withinChoice s 0 t) V U) (hb : Beam (S.withinChoice s 0 t) U) (hb' : Beam t (jointPull s U)) :
    scalar p W t (pull s 0 V) (jointPull s U) = scalar p W (S.withinChoice s 0 t) V U := by
  let U' := jointPull s U; let A := jointSpin s U; let V' := pull s 0 V
  let L := completion (S.withinChoice s 0 t) U; let L' := completion t U'
  have ha := jointSpin_ortho s U
  have hh : Carries A A (cost (completed p W (S.withinChoice s 0 t) V) U) (cost (completed p W t V') U') :=
    invariant_cost ha ((Work.F02.mainTerm_contDiffAt hw (A:=positions ∘ vary U') (x:=0) (fun _ => vary_diff _)).add
      (penalty_diff S (matDiffAt_const V') hb'.bonds)) (Filter.Eventually.of_forall (fun v => by
      change completed _ _ _ _ (vary (jointPull s U) _) = _
      rw [show clm A v = jointSpin s U *ᵥ v from rfl,vary_jointPull]; exact completed_pull s h t V _))
  have hl : L * R_tot S U = _ := completion_brace h (S.withinChoice s 0 t) U hb.patch
  have hl' : L' * R_tot S U' = _ := completion_brace h t U' hb'.patch
  change shiftFee _ (ghost _ _) = shiftFee _ (ghost _ _)
  rw [← hl',← hl]; exact (shiftFee_transfer _ _ _ _ A (siteSpin s G f) (hh.left_eq ha)
    (R_tot_spin s U).symm ha.abs_det (siteSpin_ortho ..).abs_det hS.stable L L' (hl.symm ▸ (ghost_pos _ _ mu_pos).isUnit)
    (hl'.symm ▸ (ghost_pos _ _ mu_pos).isUnit)).symm

variable (hs : ∀ i, s.flip i=false)
include hs

lemma R_g_spin (U : Config G n) : Carries (linkSpin s U) (siteSpin s G n) (R_g U) (R_g (pull s 0 U)) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, R_g,R_g,LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]
  apply (paint G (Bonds n)).injective; ext1 i
  simp only [linkSpin,siteSpin, paint_direct,spins,hs, Bool.false_eq_true,↓reduceIte, LinearMap.id_apply,paint_brace,
    pull, posDir, Step.rotate, Step.read,Step.used, sendEdge, affine,add_zero,Bool.false_xor]
  rw [s.act_add, ← show ((posDir i.2).rotate s).vec = s.act (step i.2 : Site n) from Step.vec_rotate ..]; simp [Step.rotate,posDir,hs,Step.vec]

lemma portion_spin (U : Config G n) (i : Axis) (v : Loops.Links G n) :
    portion i (linkSpin s U *ᵥ v) = siteSpin s G n *ᵥ portion (s.perm i) v := by
  funext ⟨j,a⟩; change paint G _ (linkSpin s U *ᵥ _) (j,i) a = paint G _ (siteSpin s G n *ᵥ _) j a
  simp only [linkSpin,siteSpin,paint_direct,spins,hs,Bool.false_eq_true,↓reduceIte,LinearMap.id_apply,paint_apply,portion]
  simp [sendEdge, Step.rotate,posDir,Step.used,affine,hs]

lemma scalarRef_pull {p : Clip} {W : PathData G} {σ C Λ : ℝ} (hw : W.Bounds p σ C Λ) (μ : ℝ) (U : Config G n) :
    scalarRef μ p W (pull s 0 U) = scalarRef μ p W U := by
  have ha := linkSpin_ortho s U
  have hb := siteSpin_ortho s G n
  have hr := R_g_spin s hs U
  have he : Carries _ _ (reference μ p W U) (reference μ p W (pull s 0 U)) := reference_motion ha hb hr (portion_spin s hs U)
    (invariant_cost ha (Work.F02.mainTerm_contDiffAt hw vary_diff)
      (Eventually.of_forall fun v => congr_arg (mainTerm p W) (vary_pull s U v) |>.trans (mainTerm_pull s p W _))) μ
  rw [scalarRef,scalarRef,he.det ha,(ghost_motion hr ha hb μ).det hb]
end YM.Push.Loops
