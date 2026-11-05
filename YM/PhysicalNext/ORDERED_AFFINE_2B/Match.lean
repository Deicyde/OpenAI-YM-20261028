import YM.AnalyticBridge.RESET_INCOME_PORT.Cohort
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Directions
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.Extra.MULTISOURCE_TRAJECTORIES.Reserves
import YM.Further.CURVED_GAUSSIAN_JETS.Streets
import YM.Next.MAXWELL.Det
import YM.PhysicalNext.ORDERED_AFFINE_2B.Noise
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Install
import YM.Push.RELAY_MARK.Assembly
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Reprice
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix
import YM.UVNext.COUPLING_RESET.Compare
import YM.UVNext.PRICED_KERNELS.Annuity

/-!
# Use Mapping's table on precisely the SC physical data

Keep the projector on *actual* active coordinates (`held e A`) but
completion including the frozen non-tree links. Memory layout at
`ActualScalar.page`; in bought scanners (`sheets`) equal at every
matched V. No exposing a re-chosen tag or window when issuing the
relative ledger. See also `Mapper.more_rows`: there is no change of
coordinate equiv between the D TABLES themSELVES. Even when spelling
b etc with that smaller table, carry the full F0 (not defined by that
table). Give the necessary constant-book identity (use without projection;
or project AND carry the extra pure constant block). Especially the
k term of noise MUST NOT be assumed read as a Q-tangent under reversal.
Everything under same-data Flags hypotheses, even through equality, see
`Fixed.Fees` for the extension and right-to-left attribution of Y at
those evaluations. Wrong records in the Scanner remain zero; no
neighborhood inference for them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Mapper
open Function Filter Set Lattice Wilson RG Pressure Precision Exterior Tree
open AnalyticBridge AnalyticBridge.ResetIncome SectorTools.ActualScalar
open Further Further.CurvedGaussianJets
open Next Next.Fluctuations Next.SectorChange
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

section compare
variable (e : Plate G S) (h : Doors e) (A : Stores S) (k : S.Choices) (V : Config G c)

def Checks (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (V : Config G c) :=
    ∀ s i, curb (shots S x) A F x s (.inr i) → DifferentiableAt ℝ (fun a=> G.mat (predictGroup V k s i a)) 0

variable (Y : GaussianScalar.Frozen (held e A) G) {Pt : Teller G} (hT : Pt.Funds S e.tube) (ht : Checks e.x k A e.forest V)

include hT ht
lemma at_table : (page e h A k V).D Y = lift k V * scheme e A k V := by
  have hs := funds_branch hT
  obtain ⟨_,_,hb,-⟩ := hT.feeds
  let X := Rows.move e.tube e.x V k (shots S e.x) A e.forest
  let W := page e h A k V
  have hd (v : Action e A) : W.D Y *ᵥ v= distribute k V (values e A k V v) := by
    unfold W; rw [moves,Rows.moved _ _ _ _ _ _ _ hb]
    rw [selected_all _ _ _ _ _ _ _ hs]
    funext i; obtain ⟨⟨s,i|i⟩,j⟩ := i
    · change Rows.slip*(Rows.faceKick e.tube e.x V (logTest e A v) s i) j=values e A k V v _
      exact (faces e A k V hb v s i j).symm
    change Rows.slip*(Rows.noiseKick V k (logTest e A v) s i) j=Rows.slip*(Motion.inChannel s (Q k V) (solo (values e A k V v))) i j
    rw [noise e A k V s i v hs (ht s i)]
  have hv (v : Action e A) : W.D Y *ᵥ v = (lift k V * scheme e A k V) *ᵥ v := by
    rw [hd,← Matrix.mulVec_mulVec,delivers]; rfl
  -- Matrix.ext via its canonical columns
  ext i j
  have he := congr_fun (hv (Pi.single j 1)) i
  simp only [Matrix.mulVec_single,MulOpposite.op_one,one_smul] at he
  exact he

lemma active_exact : GaussianScalar.precision ((page e h A k V).D Y) = gram (scheme e A k V) := by
  unfold GaussianScalar.precision
  rw [at_table e h A k V Y hT ht, Matrix.transpose_mul,←Matrix.mul_assoc,Matrix.mul_assoc (_ᵀ),isometric,Matrix.mul_one]; rfl



omit hT ht in
lemma filled_same (X : GaussianScalar.Wall (Bits (held e A) G)) :
    GaussianScalar.filled (held e A) X = CurvedGaussianJets.mount (held e A) X := by
  let H:=held e A
  have he : GaussianScalar.mergeBits H G = CurvedGaussianJets.tape H G := by ext (i|i) <;> rfl
  unfold CurvedGaussianJets.mount GaussianScalar.filled GaussianScalar.meet; rw [he]; rfl

/-- Completed at the REAL common positive Free-key set (AS does not
put Gaussian integration variables on trunks either). -/
lemma full_exact : (page e h A k V).sigma Y = ChangeV.precise (held e A) k e.tube.up e.tube.high (Stores.till e.x) V := by
  unfold GaussianScalar.Fiber.sigma
  rw [active_exact e h A k V Y hT ht]; exact filled_same e A _
end compare

section earned
open AnalyticBridge.SectorAffine

lemma check_price (G : Gauge) (P : Patch) (K : KernelChoices) (hK : P.Branches K G) :
    ∃ r : ℝ, 0<r ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    100*(1+radiusB x) ≤ c.val → ∀ (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (z : PriceCoords G c), ‖z‖ ≤ r → Checks x k A F (field V z) := by
  obtain ⟨r,M,hr,-,h⟩ := chosen_branch G P K hK 1
  refine ⟨r,hr,h.mono fun x hx c f S hP hS hR k A F V hV z hz s i hi => ?_⟩
  let Q := fun q : FieldPair G c f => G.mat (S.prediction (sceneField S V s q) (Oriented.choice s k) i)
  have he : Push.Uniform.Allows 1 Q (z,0) M := (hx S hP hS hR F A V hV s i z hi hz).1 _
  exact (he.analytic.differentiableAt (by simp)).comp (0:Directions G f) (show DifferentiableAt ℝ (fun a: Directions G f => (z,a)) 0 from (contDiffAt_const.prodMk (n:=ω) (f:=fun _=>z) contDiffAt_id).differentiableAt (by simp))

/-- Open neighborhood IN THE GROUP configuration. Used for transferring
CGJ's determinant/track derivative estimates, NOT a neighborhood of
validity across threshold decisions. The matrix test family here has
already frozen the latter. -/
lemma check_zone (G : Gauge) (P : Patch) (K : KernelChoices) (hK : P.Branches K G) :
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    100*(1+radiusB x) ≤ c.val → ∀ (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ᶠ U in 𝓝 V, Checks x k A F U := by
  obtain ⟨r,hr,h⟩ := check_price G P K hK
  refine h.mono fun x hx c f S hp he hR k A F V hV => ?_
  let L (t : Config G c) (e : Edge (Site c)) := G.plog (G.mat (t e*(V e)⁻¹))
  obtain ⟨(hz : L V=0), (hL : ContinuousAt L V), (h' : ∀ᶠ U in 𝓝 V, _ )⟩ := WardBin.exp_local V id V rfl
    (fun i => (continuous_apply i).continuousAt)
  let g := reader G c
  have hc : Tendsto (g ∘ L) (𝓝 V) (𝓝 0) := by
    have hh := (g.continuous.continuousAt.comp hL).tendsto; rwa [Function.comp_apply,hz,map_zero] at hh
  filter_upwards [h',hc.eventually (Metric.closedBall_mem_nhds 0 hr)] with U hU ha
  have ht := hx S hp he hR k A F V hV (g (L U)) (by simpa only [Metric.mem_closedBall,Function.comp_apply,dist_zero_right] using ha)
  change increment V (L U)=U at hU
  rwa [reader_field,hU] at ht
end earned
end YM.PhysicalNext.OrderedAffine2B.Mapper
