import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Texas
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Coach
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest


/-! Two gauges, four input logs at one nonabelian physical positive bond. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Lattice Wilson Pressure Precision RG Tree Next Next.Fluctuations Next.SectorChange
  Exterior Laurent Bloch Bid MultiNext.SignedSource AnalyticBridge.LocalGaussianLaws Lift AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {T' : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

abbrev Chord (G : Gauge) := (G.Color × G.Color) × (G.Color × G.Color)
def touch (u : Chord G) := G.lieExp u.1.1 * (G.lieExp u.2.1 * G.lieExp u.2.2) * (G.lieExp u.1.2)⁻¹
def decode (u : Chord G) := G.plog (G.mat (touch u))
@[simp] lemma touch_zero : touch (0:Chord G)=1 := by simp [touch]
@[simp] lemma decode_zero : decode (0:Chord G)=0 := by simp [decode]
lemma decode_analytic (G : Gauge) : ContDiffAt ℝ ω (decode (G:=G)) 0 ∧ Continuous (touch (G:=G)) := by
  unfold decode touch; constructor
  · have he := G.exp_jet
    have hf : ContDiff ℝ ω (fun u : Chord G => G.mat (touch u)) := by
      simp only [touch,G.mat_mul,G.mat_inv]
      apply ContDiff.mul
      · exact (he.comp (contDiff_fst.comp contDiff_fst)).mul ((he.comp (contDiff_fst.comp contDiff_snd)).mul (he.comp (contDiff_snd.comp contDiff_snd)))
      exact ((starL' ℝ:G.Mat≃L[ℝ]G.Mat).contDiff).comp (he.comp (contDiff_snd.comp contDiff_fst))
    exact (show ContDiffAt ℝ ω G.plog (G.mat (touch (0:Chord G))) by rw [touch_zero,G.mat_one]; exact G.plog_diff).comp (g:=G.plog) (f:=fun u => G.mat (touch u)) 0 hf.contDiffAt
  fun_prop
lemma decode_first (u : Chord G) : fderiv ℝ decode 0 u=u.1.1+u.2.1+u.2.2-u.1.2 := by
  have he (v : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • v))) (G.colorMat v) 0 := G.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ)
      (show HasDerivAt (fun t : ℝ => t • v) v 0 from by simpa using (hasDerivAt_id' (0:ℝ)).smul_const v) (by simp)
  let p := u.1.1+u.2.1+u.2.2-u.1.2
  have h : HasDerivAt (fun s : ℝ => G.mat (touch (s • u))) (G.colorMat p) 0 := by
    unfold touch; simp only [G.mat_mul,G.mat_inv]; apply ((he u.1.1 |>.mul ((he u.2.1).mul (he u.2.2))).mul (he u.1.2).star).congr_deriv
    unfold p; simp only [Pi.mul_apply,zero_smul,G.mat_lieExp_zero,G.mat_one,G.colorMat_skew,mul_one,one_mul,star_one,map_sub,map_add]; abel
  exact ((Push.side _ ((decode_analytic G).1.differentiableAt (by simp)) u).unique ((G.plog_diff.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) h
      (show (1:G.Mat)=G.mat (touch ((0:ℝ) • u)) by rw [zero_smul,touch_zero,G.mat_one]))).trans (Pattern.physical p)

lemma decode_cert (G : Gauge) (n : ℕ) : ∃ K r : ℝ, 0<K ∧ 0<r ∧ ∀ u : Chord G, ‖u‖ ≤ r → Through n (decode (G:=G)) u K ∧ G.lieExp (decode u) = touch u := by
  have he := decode_analytic G
  haveI : ProperSpace (Chord G) := FiniteDimensional.proper ℝ _
  obtain ⟨r,hr,H⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 ((he.1.eventually (by simp)).and ((he.2.tendsto 0).eventually (touch_zero.symm ▸ G.plog_right)))
  obtain ⟨C,hc,h⟩ := Push.Uniform.exists_allows (f:=decode (G:=G)) (isCompact_closedBall 0 r) (fun x hx => (H hx).1) n
  exact ⟨C+1,r,by positivity,hr,fun x hx => ⟨(Through.control (h x (mem_closedBall_zero_iff.mpr hx))).mono (by linarith),(H (mem_closedBall_zero_iff.mpr hx)).2⟩⟩

abbrev Deck (G : Gauge) (c f : Side) := Directions G c × Directions G f
section front
variable (T) (F) (x : ℝ) (k : S.Choices) (sw : Bool)

def awaken (p : clear S x F → G.Color) (i : Bond f) := if he : i∉F.trunks then p ⟨⟨i,he⟩,notChilled S F x _⟩ else 0
def expandBare : Prices G (clear S x F) →L[ℝ] Directions G f := LinearMap.toContinuousLinearMap {
  toFun p := awaken F x (gaugeCount (G:=G) p)
  map_add' u v := by funext i; unfold awaken; split <;> simp_all
  map_smul' t v := by funext i; unfold awaken; split <;> simp_all }

def φ := if sw then pegs F (main T) (G:=G) else 0

def chord (p : Deck G c f) (i : Bond f) : Chord G :=
   ((φ T F sw p.1 i.1,φ T F sw p.1 (i.1+Lattice.step i.2)),
    (expandBare F x (forecast T x F k p.1) i + p.2 i,linearCopy S.ratio p.1 i))

def sounds (p : Deck G c f) : Config G f := fun i => touch (chord T F x k sw p i)
def display (p : Deck G c f) : Directions G f := fun i => decode (chord T F x k sw p i)

def mainStroke : Deck G c f →L[ℝ] Directions G f :=
  ((if sw then route T else woody T F).comp (ContinuousLinearMap.fst ℝ _ _)) + ContinuousLinearMap.snd ℝ _ _

lemma expandBare_pick (u : Directions G c) : expandBare F x (first T F x u)=treeMap T F u := by
  funext i; change awaken _ _ _ i=_
  unfold awaken; split
  next he => rfl
  next he => rw [tree_value]; exact (doc_trunk T F (Flat.labels u) i (by simpa using he)).symm
end front
lemma budget_expandBare (G : Gauge) : ∃ C : ℝ, 0≤C ∧ ∀ {c f : Side} (S : StepData c f) (F : Forest S.ratio) (x : ℝ), ‖expandBare F x (G:=G)‖ ≤ C := by
  obtain ⟨C,hC,H⟩ := sense G
  refine ⟨C,hC,fun S F x => ContinuousLinearMap.opNorm_le_bound _ hC (fun p => (pi_norm_le_iff_of_nonneg (show 0≤C*‖p‖ by positivity)).mpr fun i => ?_)⟩
  change ‖(if he : i∉F.trunks then gaugeCount p (⟨⟨i,he⟩,notChilled S F x _⟩ : clear S x F) else 0:G.Color)‖ ≤ _
  split
  · exact (H _).trans (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr fun j => norm_le_pi_norm p _) hC)
  rw [norm_zero]; positivity
lemma carriedCopy_norm (S : StepData c f) (G : Gauge) : ‖carriedCopy S (G:=G)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => (pi_norm_le_iff_of_nonneg (show 0 ≤ 1*‖v‖ by positivity)).mpr fun i => ?_)
  change ‖linearCopy S.ratio v i‖ ≤ _; rw [one_mul]; unfold linearCopy; split; rw [norm_zero]; positivity
  exact norm_le_pi_norm v _
end YM.PhysicalNext.JointLoad.Heir
