import YM.Ac.Table
import YM.AnalyticNext.QUARTIC_MATCH.Scene
import YM.AnalyticNext.QUARTIC_MATCH.Submersion
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Work.E01
import YM.Work.F03
import YM.Work.F04





/-!
# Auxiliary joint coordinates and critical value

Use actual rooted frames and minimizing predictors. Tree retraction from the joint
redundant fields works by two **real** gauges and local exponential coordinates. No
jacobian claim. Sufficient also to compare under changes of period, orientations etc.
without selecting "coherent" tree gauges. Rooted joint frame (uncentered here).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch
open Filter Function Matrix Precision RG Lattice Exterior Tree Bid Wilson
open Work.F03 Work.F04 Work.F05 Topology
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}
namespace Joint

abbrev Spin (G : Gauge) (c : Side) := Site c → G.El
abbrev LieSpin (G : Gauge) (c : Side) := Site c → G.Color
abbrev Vertical (G : Gauge) (c f : Side) := Dir G f × LieSpin G c
variable {c f n : Side}

def groupEnergy (K : KernelChoices) (Q V : Config G c) := K.penalty * ∑ e, G.price (V e * (Q e)⁻¹)

def fieldAction (S : StepData c f) (t : S.Choices) (p : Clip) (W : PathData G)
    (V : Config G c) (U : Config G f) (Φ : Spin G c) :=
    mainTerm p W U + groupEnergy S.kernel (Lattice.gauge Φ (S.prediction U t)) V

def power (b : LieSpin G c) : Spin G c := fun y => G.lieExp (b y)

theorem power_zero : power (0 : LieSpin G c) = 1 := funext fun _ => G.mat_lieExp_zero

def action (S : StepData c f) (t : S.Choices) (p : Clip) (W : PathData G)
    (z : Dir G c × Vertical G c f) := fieldAction S t p W (represent z.1) (represent z.2.1) (power z.2.2)

lemma gaugeTwice (φ t : Spin G n) (U : Config G n) :
    Lattice.gauge φ (Lattice.gauge t U)=Lattice.gauge (φ*t) U := by
  funext i; simp only [Lattice.gauge, Pi.mul_apply]; group
lemma trivial (U : Config G n) : Lattice.gauge (1 : Spin G n) U=U := by funext i; simp [Lattice.gauge]
lemma uniform (φ : Spin G n) (K : KernelChoices) (U V : Config G n) :
    groupEnergy K (Lattice.gauge φ U) (Lattice.gauge φ V)=groupEnergy K U V := by
  unfold groupEnergy; apply congr_arg
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Lattice.gauge φ V i * (Lattice.gauge φ U i)⁻¹=φ i.1 * (V i * (U i)⁻¹) * (φ i.1)⁻¹ := by
    simp only [Lattice.gauge]; group
  rw [h,G.price_conj]
lemma predicted {S : StepData c f} (h : S.patch.Branches S.kernel G) (t : Spin G f) (U : Config G f)
    (i : S.Choices) : S.prediction (Lattice.gauge t U) i=Lattice.gauge (t ∘ S.ratio.embed) (S.prediction U i) := by
  funext e
  unfold StepData.prediction
  rw [S.updateGauged h, (S.patch.bond_gauge (h:=h) ..).2]; rfl

variable {S : StepData c f} {W : PathData G}

lemma fine_gauge {p : Clip} {σ C Λ} (h : S.patch.Branches S.kernel G) (hW : W.Bounds p σ C Λ)
    (t : S.Choices) (V : Config G c) (U : Config G f) (Φ : Spin G c) (k : Spin G f) :
    fieldAction S t p W V (Lattice.gauge k U) (Φ*(k ∘ S.ratio.embed)⁻¹) = fieldAction S t p W V U Φ := by
  simp only [fieldAction, mainTerm_gauge hW, predicted h, gaugeTwice, inv_mul_cancel_right]
lemma coarse_gauge (p : Clip) (t : S.Choices) (V : Config G c) (U : Config G f) (Φ k : Spin G c) :
    fieldAction S t p W (Lattice.gauge k V) U (k*Φ) = fieldAction S t p W V U Φ := by
  unfold fieldAction; rw [← gaugeTwice, uniform]

variable {g : Ratio c f}

/-- Joint link rotated by the stored auxiliary frame field. -/
def dressed (g : Ratio c f) (z : Vertical G c f) : Config G f :=
    Lattice.gauge (constantGauge (power z.2) g) (represent z.1)
lemma dresses {p : Clip} {σ C Λ} (h : S.patch.Branches S.kernel G) (hW : W.Bounds p σ C Λ) (t : S.Choices)
    (z : Dir G c × Vertical G c f) : action S t p W z = fieldAction S t p W (represent z.1) (dressed S.ratio z.2) 1 := by
  unfold action dressed
  have he (φ : Spin G c) : φ * (constantGauge φ S.ratio ∘ S.ratio.embed)⁻¹ = 1 := by
    funext i; simp [constantGauge, Ratio.embed_parent]
  have hm := fine_gauge h hW t (represent z.1) (represent z.2.1) (power z.2.2) (constantGauge (power z.2.2) S.ratio)
  rwa [eq_comm,he] at hm

def plant (B : Forest g) (a : Dir G c × AxisChart G B) : Vertical G c f :=
    (axisLog B a, 0)

/-- Slice link at the true wiping, still relative to the background from x. -/
def clippedIn (B : Forest g) (z : Dir G c × Vertical G c f) (i : B.Free) :=
    Profiles.wiped B (dressed g z.2) i * (replica g (represent z.1) i)⁻¹

def slice (B : Forest g) (z : Dir G c × Vertical G c f) : AxisChart G B :=
    fun i => G.plog (G.mat (clippedIn B z i))

section rate
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def Smooth (x : X) (Q : X → G.El) : Prop := ContDiffAt ℝ ω (G.mat ∘ Q) x

variable {x : X} {Q V : X → G.El}
theorem Smooth.mul (h : Smooth x Q) (hv : Smooth x V) : Smooth x (fun y => Q y * V y) := by
  simp only [Smooth, Function.comp_def, Gauge.mat_mul]; exact ContDiffAt.mul h hv
theorem Smooth.inv (h : Smooth x Q) : Smooth x (fun y => (Q y)⁻¹) := by
  simp only [Smooth,Function.comp_def, Gauge.mat_inv]
  exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp x h
theorem Smooth.power {b : X → G.Color} (h : ContDiffAt ℝ ω b x) : Smooth x (fun y => G.lieExp (b y)) :=
  G.exp_jet.contDiffAt.comp x h
lemma Smooth.travel {U : X → Config G n} (h : ∀ i, Smooth x (fun y => U y i))
    (b : Site n) (p : Walk) : Smooth x (fun y => travel (U y) b p) := by
  induction p generalizing b with
  | nil => exact contDiffAt_const
  | cons i l ih =>
    apply Smooth.mul _ (ih _); unfold Step.read; split
    · exact (h _).inv
    exact h _
theorem Smooth.tendsto (h : Smooth x Q) : Tendsto Q (𝓝 x) (𝓝 (Q x)) :=
    (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
      h.continuousAt.tendsto
theorem Smooth.plog (h : Smooth x Q) (he : Q x=1) :
    ContDiffAt ℝ ω (fun y => G.plog (G.mat (Q y))) x := by
  have hm : G.mat (Q x) = 1 := by rw [he, G.mat_one]
  exact (hm.symm ▸ G.plog_diff : ContDiffAt ℝ ω G.plog (G.mat (Q x))).comp (f:=G.mat ∘ Q) x h
end rate

lemma plant_zero (B : Forest g) : plant B (0 : Dir G c × AxisChart G B) = 0 :=
  Prod.ext (congr_arg Prod.snd (inclusion_zero B (G:=G))) rfl
lemma plant_smooth (B : Forest g) : ContDiffAt ℝ ω (plant (G:=G) B) 0 :=
  (show ContDiffAt ℝ ω (axisLog B (G:=G)) 0 from (inclusion_smooth B (G:=G)).snd).prodMk contDiffAt_const
lemma dressed_zero (g : Ratio c f) : dressed g (0 : Vertical G c f) = 1 := by
  unfold dressed; rw [show (0:Vertical G c f).1=0 from rfl,link_one,
    show power (0:Vertical G c f).2=1 from power_zero, show constantGauge (1:Spin G c) g=1 from rfl, trivial]
lemma dressed_jet (g : Ratio c f) (e : Edge (Site f)) : Smooth (0 : Vertical G c f) (fun y => dressed g y e) := by
  have hs (x : Site f) : Smooth (0 : Vertical G c f) (fun z => constantGauge (power z.2) g x) :=
    Smooth.power ((contDiffAt_apply _ _ _ _).comp _ contDiffAt_snd :
      ContDiffAt ℝ ω (fun z : Vertical G c f => z.2 (g.parent x)) 0)
  have hw : Smooth (0 : Vertical G c f) fun z => represent z.1 e :=
    (represent_smooth (G:=G) e).contDiffAt.comp _ contDiffAt_fst
  exact ((hs _).mul hw).mul (hs _).inv

lemma clipIn_smooth (B : Forest g) (i : B.Free) : Smooth (0 : Dir G c × Vertical G c f) (fun z => clippedIn B z i) := by
  have hd (e : Edge (Site f)) : Smooth (0 : Dir G c × Vertical G c f) (fun z => dressed g z.2 e) :=
    (dressed_jet (G:=G) g e).comp (f:=Prod.snd) (0 : Dir G c × Vertical G c f) contDiffAt_snd
  have ht (x : Site f) : Smooth (0 : Dir G c × Vertical G c f) (fun z => B.foldAt (dressed g z.2) x) :=
    (Smooth.travel hd _ _).inv
  apply Smooth.mul (((ht _).mul (hd _)).mul (ht _).inv)
  apply Smooth.inv
  unfold replica; split
  · exact contDiffAt_const
  exact (represent_smooth (G:=G) _).contDiffAt.comp _ contDiffAt_fst
lemma clipIn_zero (B : Forest g) (i : B.Free) : clippedIn B (0 : Dir G c × Vertical G c f) i = 1 := by
  unfold clippedIn; rw [Prod.snd_zero, dressed_zero, Prod.fst_zero,link_one, replica_one]
  have hw : Profiles.wick B (1 : Config G f) = 1 := by
    have he := Profiles.wick_root B (exposure B (0:Dir G c) 0)
    rwa [drape_exposure,lifted,link_one,replica_one,exposure_zero] at he
  simp only [Pi.one_apply,inv_one,mul_one]; exact congr_fun hw i

lemma slice_zero (B : Forest g) : slice B (0 : Dir G c × Vertical G c f)=0 := by
  funext i
  simp only [slice,clipIn_zero,G.mat_one,G.plog_one]; rfl
lemma slice_jet (B : Forest g) : ContDiffAt ℝ ω (slice (G:=G) B) 0 :=
  contDiffAt_pi.mpr fun i => (clipIn_smooth (G:=G) B i).plog (clipIn_zero B i)
lemma slice_back (B : Forest g) : ∀ᶠ z : Dir G c × AxisChart G B in 𝓝 0, slice B (z.1,plant B z)=z.2 := by
  have hm (i : B.Free) : ∀ᶠ z : Dir G c × AxisChart G B in 𝓝 0,
      G.plog (G.mat (G.lieExp (z.2 i))) = z.2 i :=
    (((continuous_apply i).comp continuous_snd).tendsto (0 : Dir G c × AxisChart G B)).eventually G.plog_left
  filter_upwards [eventually_all.mpr hm, inclusion_works B] with z hz hx
  have he : dressed g (plant B z)= lifting B (represent z.1) z.2 := by
    unfold plant dressed; dsimp only; rw [power_zero, show constantGauge (1:Spin G c) g=1 from rfl,
      trivial]; exact hx
  funext i
  unfold slice clippedIn
  dsimp only
  rw [he,← drape_exposure]
  change G.plog (G.mat (Profiles.wick B (B.drape (exposure _ _ _)) i * _))=_
  rw [Profiles.wick_root,exposure, mul_inv_cancel_right]
  exact hz i

section value
variable {T : Forest S.ratio} {σ C Λ η : ℝ} {p : Clip} {W : PathData G}
    {b : Dir G c → AxisChart G T}

lemma unframe (t : S.Choices) (W : PathData G) (p : Clip) (U : Config G f) (V : Config G c) :
    fieldAction S t p W V U 1 = mainTerm p W U + noiseTaylor S V U t := by
  rw [fieldAction,trivial]; rfl

lemma reduce (T : Forest S.ratio) (h : S.patch.Branches S.kernel G) (hW : W.Bounds p σ C Λ) (t : S.Choices) :
    action S t p W =ᶠ[𝓝 0] fun z => tested T t p W z.1 (slice T z) := by
  have hs (i : T.Free) : ∀ᶠ z : Dir G c × Vertical G c f in 𝓝 0,
      G.lieExp (slice T z i) = clippedIn T z i := by
    have he := (clipIn_smooth (G:=G) T i).tendsto
    change Tendsto _ _ (𝓝 (clippedIn T 0 i)) at he
    rw [clipIn_zero] at he
    exact he.eventually G.plog_right
  filter_upwards [eventually_all.mpr hs] with z hz
  let U := dressed S.ratio z.2
  have hk : exposure T z.1 (slice T z)=Profiles.wick T U := by
    funext i; rw [exposure, hz, clippedIn, inv_mul_cancel_right]; rfl
  have hm : lifting T (represent z.1) (slice T z)=Profiles.wiped T U := by
    rw [← drape_exposure,hk]; exact Profiles.wears T _
  rw [tested, hm, dresses h hW,unframe]
  simp only [Profiles.wiped, mainTerm_gauge hW,root_noise h _ _ _ (fun i => T.fold_root U i)]
  rfl

variable (h : S.patch.Branches S.kernel G) (hW : W.Bounds p σ C Λ) (hb : Critical T p W b)
    (t : S.Choices)
include h hW hb

lemma root_born : ContDiffAt ℝ ω (action S t p W) 0 := by
  have ht := contDiffAt_fst.prodMk (slice_jet (G:=G) T)
  have hp : ContDiffAt ℝ ω (uncurry (tested T t p W)) ((0:Dir G c),slice T (0:Dir G c × Vertical G c f)) := by
    rw [slice_zero]; exact (hb.2.2 t).1
  have hb : ContDiffAt ℝ ω ((uncurry (tested T t p W)) ∘ (fun z : Dir G c × Vertical G c f => (z.1,slice T z))) 0 :=
    hp.comp (f:=fun z : Dir G c × Vertical G c f => (z.1,slice T z)) _ ht
  exact hb.congr_of_eventuallyEq (reduce T h hW t)

/-- Construct an actual analytic joint stationary graph through that slice. -/
lemma joints :
    let u := plant T ∘ arc b
    u 0=0 ∧ OnShell (action S t p W) u 0 ∧
      action S t p W ∘ arc u =ᶠ[𝓝 0] uncurry (tested T t p W) ∘ arc b := by
  intro u
  have h0 : arc b 0=0 := Prod.ext rfl hb.1
  have hc : u 0=0 := (congr_arg _ h0).trans (plant_zero T)
  have hs : ContDiffAt ℝ ω (plant (G:=G) T) (arc b 0) := by rw [h0]; exact plant_smooth T
  have hu : ContDiffAt ℝ ω u 0 := hs.comp _ (SliceExchange.on_shell t hb).arc_smooth
  exact ⟨hc, ascend (p:=slice T) (root_born h hW hb t) (SliceExchange.on_shell t hb) hb.1 (slice_jet T)
    (reduce T h hW t) hc hu ((crit_home hb).eventually (slice_back T))⟩

/-- Compare actual joint stationarity near the origin without any uniform
stationarity-radius assumption. -/
theorem recognizes (B : Bed) (hv : Comptroller T B p W)
    (he : 0 < η) (hq : PriceGap T p W η) : ∀ᶠ z : Dir G c × Vertical G c f in 𝓝 0,
    vert (action S t p W) z=0 → action S t p W z=tested T t p W z.1 (b z.1) := by
  have ht := vert_pull (L:=id) (slice_jet T) contDiffAt_id (reduce T h hW t)
    (show ContDiffAt ℝ ω (uncurry (tested T t p W)) ((0:Dir G c), slice T (0 : Dir G c × Vertical G c f)) from by
      rw [slice_zero]; exact (hb.2.2 t).1)
  have hm := invertible T p W η he t hq ((hb.2.2 t).1) (hv t).2.1
  have hs := vMap_surjective (slice_jet T) (T:=fun y => plant T ((0:Dir G c),y))
    (show DifferentiableAt ℝ _ _ from (((plant_smooth (G:=G) T).comp (f:=fun y : AxisChart G T => ((0:Dir G c), y)) 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)))
    (plant_zero T) (hold_near (slice_back T))
  have hu : Tendsto (fun z : Dir G c × Vertical G c f => (z.1,slice T z)) (𝓝 0) (𝓝 (0:Dir G c × AxisChart G T)) := by
    have hb := ((slice_jet (G:=G) T).continuousAt).tendsto
    rw [slice_zero] at hb
    exact (continuous_fst.tendsto _).prodMk_nhds hb
  have hk := hu.eventually (near_root (SliceExchange.on_shell t hb) hb.1 hm)
  filter_upwards [ht, reduce T h hW t,hk, hs] with z hz hy ha hs H
  have he : vert (uncurry (tested T t p W)) (z.1,slice T z)=0 := by
    ext i
    obtain ⟨j,rfl⟩ := hs i
    exact DFunLike.congr_fun (hz.symm.trans H) j
  have hw : slice T z = b z.1 := ha he
  exact hy.trans (congr_arg (tested T t p W z.1) hw)
end value
end Joint
end YM.AnalyticNext.QuarticMatch
