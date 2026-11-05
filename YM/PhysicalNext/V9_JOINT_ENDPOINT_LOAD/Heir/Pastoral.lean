import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Hymn
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Repair

/-! # Gauge, localization and regularity of the principal endpoint term

On authentic U & V wherever required; gauges never differentiate the Γ
constraint. At a gauge-invariant E guard (`Natural`) and fixed tag address.
Off V-domain, a Borel Y-local extension. Other operators than gauge /
`Agrees` may require averaging & separately proving equivariant selection
of full supports (`Y` here including guard, classification etc at caller!).
Not projecting the marginal on a recomputed subperiod.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Puff ProofPorts.CommonComplexProduction.Score Push.SectorMeasure
    Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussianLaws ColorBook
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}

section matrices
variable (L : Gaussian.Table ι) (hr : L*L.transpose=1) (hl : L.transpose*L=1)
def volt : Gaussian.Vec ι ≃ᵐ Gaussian.Vec ι where
  toFun x := L*ᵥx
  invFun x := L.transpose*ᵥ x
  right_inv x := by dsimp only; rw [mulVec_mulVec,hr,Matrix.one_mulVec]
  left_inv x := by dsimp only; rw [mulVec_mulVec,hl,Matrix.one_mulVec]
  measurable_toFun := by change Measurable (L *ᵥ ·); unfold Matrix.mulVec dotProduct; fun_prop
  measurable_invFun := by change Measurable (L.transpose *ᵥ ·); unfold Matrix.mulVec dotProduct; fun_prop

variable (Q : Gaussian.Table ι)
include hr hl
lemma skim_posdef : (Density.skim L Q).PosDef ↔ Q.PosDef := by
  have he (Q L : Gaussian.Table ι) (h : Q.PosDef) (hL : L*L.transpose=1) : (Density.skim L Q).PosDef := h.conjTranspose_mul_mul_same (B:=L.transpose)
    (fun x y he => by simpa only [Matrix.mulVec_mulVec,hL, Matrix.one_mulVec] using congr_arg (L *ᵥ ·) he)
  refine ⟨fun h => ?_, fun h => he Q L h hr⟩
  simpa only [Density.skim, transpose_transpose,← Matrix.mul_assoc,hl,Matrix.one_mul,show Q*L.transpose*L=Q from (Matrix.mul_assoc ..).trans (by rw [hl, Matrix.mul_one])]
    using he _ L.transpose h (by rwa [Matrix.transpose_transpose])
end matrices
namespace Museum
variable {Γ : Prices G ι → ℝ} (a : Museum F x A X Y ι)

def Natural (a : Museum F x A X Y ι) (Γ : Prices G ι → ℝ) := ∀ (g : Site c → G.El) z, Γ (a.toned g *ᵥ z)=Γ z
variable (b : Folio.Bulletin x Pt T) (hf' : B.Regular X f')
include b hf'
set_option maxHeartbeats 620000 in
lemma hymn_eq (U W : Config G f) (V Z : Config G c) (h : Agrees Y V Z) : a.hymn T u q d k f' Γ U V = a.hymn T u q d k f' Γ W Z := by
  unfold hymn; rw [a.twilight_local b h]; dsimp only; split
  swap; · rfl
  apply integral_congr_ae; filter_upwards with z
  exact congrArg (Γ z*·) (hf'.sites _ _ (agrees_mono (a.variations b h U W z) fun i hi => Finset.mem_union_left _ hi))

lemma hymn_gauged (hN : a.Natural Γ) (V : Config G c) (g : Site c → G.El) (U : Config G f) : a.hymn T u q d k f' Γ U (gauge g V) = a.hymn T u q d k f' Γ U V := by
  rw [a.hymn_eq b hf' U (gauge (g ∘ S.ratio.parent) U) _ _ (fun _ _ _ => rfl)]
  let L := a.toned g; let Q := a.twilight k T V
  have hL : L*L.transpose=1 := onPage_right _ _ (tag_checked _)
  have hL' : L.transpose*L=1 := onPage_left _ _ (tag_checked _)
  unfold hymn; rw [a.twilight_gauge g b.priced V]; by_cases h : Q.PosDef
  swap; · rw [if_neg (not_iff_not.mpr (skim_posdef L hL hL' Q) |>.mpr h),if_neg h]
  rw [if_pos h,if_pos ((skim_posdef L hL hL' Q).mpr h)]
  have H : MeasurePreserving (volt L hL hL') (Gaussian.cloud Q) (Gaussian.cloud (Density.skim L Q)) := Density.gathered h.posSemidef L
  rw [← H.integral_comp']; apply integral_congr_ae; filter_upwards with z
  rw [show volt L hL hL' z=L *ᵥ z from rfl, hN g z]
  exact congrArg (Γ z * ·) ((hf'.sites _ _ (agrees_mono (a.received_gauge g b.priced V U z) fun i hi => Finset.mem_union_left _ hi)).trans (hf'.symmetry _ _))

variable (T u q d k f' Γ)
def principal := repair (a.hymn T u q d k f' Γ 1)
variable {T u q d k f' Γ}
omit b hf'
variable (hG : G.Simple) (he : Plays C D P B Pt T x) (hf : Seed B o X f') (hτ : B.supBounds o X f' τ)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ)
include hG he hf hτ hY hu hΓ
lemma grown (hΓ' : a.Natural Γ) : P.Regular Y (a.principal T u q d k f' Γ) := by
  refine repair_valid (fun _ _ => a.hymn_gauged he.bulletin hf.good hΓ' _ _ _) (a.hymn_eq he.bulletin hf.good 1 1)
    (fun V hV => he.rehearsed.test.symm ▸ (a.exchange (q:=q) (d:=d) (k:=k) 1 hG he hf hτ hY hu hΓ hV [] (Nat.zero_le _)).1)

lemma priced_principal (U : Config G f) (hV : Healthy P.threshold Y V) (L : List (Directions G c)) (hl : L.length ≤ n) :
    let b := a.concert T u q d k f' Γ U V; let μ := Gaussian.cloud (a.twilight k T V)
    Integrable (fun z => leftDerivs (b z) L V) μ ∧ ((leftDerivs (a.principal T u q d k f' Γ) L V:ℝ):ℂ) = ∫ z,leftDerivs (b z) L V ∂μ := by
  intro b μ; obtain ⟨hd,ha,hh⟩ := a.exchange (q:=q) (d:=d) (k:=k) U hG he hf hτ hY hu hΓ hV L hl
  unfold principal; rw [show a.hymn T u q d k f' Γ 1=a.hymn T u q d k f' Γ U from funext fun V => a.hymn_eq he.bulletin hf.good _ _ _ _ (fun _ _ _ => rfl),left_eq L (repair_at hd)]
  exact ⟨ha,hh⟩
where
  left_eq (l : List (Directions G c)) {f g : Config G c → ℝ} {V : Config G c} (h : f=ᶠ[𝓝 V] g) : leftDerivs f l V=leftDerivs g l V := by
    induction l generalizing V with
    | nil => exact h.eq_of_nhds
    | cons i l ih => exact ((show (fun t : ℝ => leftDerivs f l (increment V (t • i))) =ᶠ[𝓝 0] (fun t : ℝ => leftDerivs g l (increment V (t • i))) from
        ((Puff.swing V i).eventually (eventually_eventually_nhds.mpr h)).mono (fun _ he => ih he))).deriv_eq
end Museum
end YM.PhysicalNext.JointLoad.Heir
