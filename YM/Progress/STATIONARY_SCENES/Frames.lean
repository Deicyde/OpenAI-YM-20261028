import YM.Analytic.Frame
import YM.Next.EXTRACTION.Tails
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Work.F03
import YM.Work.F05.Graphs



/-!
# Frames to use on the paid regions

The patch frame and the tree slice are NOT the same choice. Use `S.frames` and its
actual tag rule even off the analytic branch. Here also construct the native analytic
stationary coordinates for the PATCH score on the flat germ and identify with the
actual minimizing frames for *every* site/tag. Proof from the `Branches` interface
(already supplied by our Levels); no Frame hypotheses about interacting fields.
This is a real fixed-period germ, not a uniform IFT or a complex gauge claim.

Use later with `regionHere`: in addition to the Levels' branches we will have honest
macro-size payment on the same torus `f`. `macro_room` shows e.g. that the region
can be placed using actual physical sites. No using it to ignore winding in OTHER
reads. Forest height bound included in every use of Forest; we'll use any, and all k choices
will concern THE SAME Step with shared tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes

open Lattice Filter Function RG Wilson Precision Pressure Bid Tree
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {c f : Side} {S : StepData c f}



/-- For consumers wanting one specific slice. NOT a new tree law for the kernel. -/
def exampleTree (S : StepData c f) : Forest S.ratio :=
  Classical.choice <| Tree.select S.ratio S.patch.odd_side

/-- Anchored whichever actual branch, unused tags too. -/
theorem rooted_frame (U : Config G f) (t : S.SitesChoice) (x : Site c) :
    S.frames U t x S.patch.center = 1 := by
  unfold StepData.frames Patch.frame
  split
  · exact (Patch.min_exists ..).choose_spec.1
  · simp

/-- Full frame coordinates (except imposed root H=1), taken from one tag; near
flat it is the minimizing branch and *all* tags use these. -/
def rootCoordinates (S : StepData c f) (t : S.SitesChoice) (x : Site c)
    (z : Push.In G f) : S.patch.FrameCoordinates G :=
  WithLp.toLp 2 (fun i => G.plog (Push.hats S x t z i.1.val) i.2)

lemma root_zero (h : S.patch.Branches S.kernel G) (t : S.SitesChoice) (x : Site c) :
    rootCoordinates S t x (0 : Push.In G f) = 0 := by
  ext ⟨i,j⟩
  change G.plog (Push.hats S x t 0 i.val) j = ((0:G.Color) j)
  rw [Push.hats_zero (h := h), G.plog_one]

lemma root_smooth (h : S.patch.Branches S.kernel G) (t : S.SitesChoice) (x : Site c) :
    ContDiffAt ℝ ω (rootCoordinates S t x (G := G)) 0 := by
  refine (contDiffAt_piLp 2).2 fun ⟨i,j⟩ => ?_
  have hc : ContDiffAt ℝ ω G.plog (Push.hats S x t 0 i.val) := by
    rw [Push.hats_zero (h := h)]; exact G.plog_diff
  exact (contDiffAt_piLp 2).1 (hc.comp (f := fun v => Push.hats S x t v i.val) (0 : Push.In G f) (Push.scheme S x t (h := h) i.val)) j

lemma realizes_frame (h : S.patch.Branches S.kernel G) (t : S.SitesChoice) (x : Site c) :
    ∀ᶠ z : Push.In G f in 𝓝 0,
      S.patch.frameFromCoordinates G (rootCoordinates S t x z) = S.frames (represent z) t x := by
  have he (i : S.patch.Points) : ∀ᶠ z : Push.In G f in 𝓝 0,
      G.lieExp (G.plog (Push.hats S x t z i)) = S.frames (represent z) t x i := by
    have ht : ContinuousAt (fun z : Push.In G f => S.frames (represent z) t x i) 0 :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
        (Push.hat_cont S x t (h := h) i).tendsto
    have hv := ht.tendsto
    have hh : S.frames (represent (0 : Push.In G f)) t x i = 1 :=
      G.mat_injective ((Push.hats_zero S x t (h := h) i).trans G.mat_one.symm)
    rw [hh] at hv
    exact hv.eventually G.plog_right
  filter_upwards [eventually_all.mpr he] with z hz
  funext i
  unfold Patch.frameFromCoordinates
  split
  · rename_i hh
    subst i
    exact (rooted_frame ..).symm
  · exact hz i

lemma native_score_smooth (S : StepData c f) (x : Site c) :
    ContDiffAt ℝ ω (Analytic.nativeFrameScore (G := G) S x) 0 := by
  let A := Push.In G f × S.patch.FrameCoordinates G
  have ha (i : S.patch.Points) : ContDiffAt ℝ ω
      (fun z : A => G.mat (S.patch.frameFromCoordinates G z.2 i)) 0 := by
    unfold Patch.frameFromCoordinates
    split
    · exact contDiffAt_const
    rename_i he
    let g (z : A) : G.Color := WithLp.toLp 2 (fun j => z.2 (⟨i,he⟩,j))
    have hg : ContDiffAt ℝ ω g 0 :=
      (contDiffAt_piLp 2).mpr (fun j => ((contDiffAt_piLp 2).1
        (show ContDiffAt ℝ ω (Prod.snd : A → _) 0 from contDiffAt_snd) (⟨i,he⟩,j)))
    exact G.exp_jet.contDiffAt.comp _ hg
  unfold Analytic.nativeFrameScore Patch.score Patch.average
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => ?_)
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun j _ => ?_)
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun k _ => ?_)
  refine Work.F03.price_smooth (A := fun z : A => S.patch.via
    (S.patch.frameFromCoordinates G z.2) (Push.product S x z.1) i j k) ?_
  simp only [Patch.via, Push.product, G.mat_mul, G.mat_inv, travel_at]
  exact ((ha i).mul ((Push.writes (G := G) _ _).comp (f := Prod.fst) (0 : A) contDiffAt_fst)).mul
    ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (ha j))

lemma realizes_minimizer (h : S.patch.Branches S.kernel G) (t : S.SitesChoice) (x : Site c) :
    let q := rootCoordinates S t x (G := G)
    ∀ᶠ z in 𝓝 0,
      S.patch.minimizing (Push.product S x z) (S.patch.frameFromCoordinates G (q z)) ∧
        HasFDerivAt (fun b => Analytic.nativeFrameScore S x (z,b)) (0 : S.patch.FrameCoordinates G →L[ℝ] ℝ) (q z) := by
  intro q
  have hi := root_smooth h t x
  have ht : Tendsto (fun z => (z,q z)) (𝓝 0) (𝓝 0) := by
    have hh := (continuousAt_id.prodMk hi.continuousAt).tendsto
    simpa only [id_eq, root_zero h] using! hh
  filter_upwards [Push.threshold S x, realizes_frame h t x,
    ht.eventually ((native_score_smooth (G := G) S x).eventually (by simp))] with z hz he hv
  have hh : S.patch.minimizing (Push.product S x z) (S.patch.frameFromCoordinates G (q z)) := by
    unfold q
    rw [he]
    change S.patch.minimizing _ (S.patch.frame S.kernel (Push.product S x z) _)
    rw [Patch.frame, if_pos hz]
    exact (Patch.min_exists ..).choose_spec
  refine ⟨hh,?_⟩
  let g := fun b => Analytic.nativeFrameScore S x (z,b)
  have hm : IsLocalMin g (q z) := Filter.Eventually.of_forall fun b =>
    hh.2 (S.patch.frameFromCoordinates G b) (Patch.frameFromCoordinates_center ..)
  rw [← hm.fderiv_eq_zero]
  have hs : ContDiffAt ℝ ω g (q z) := hv.comp (f := fun i => (z,i)) (q z) (contDiffAt_const.prodMk contDiffAt_id)
  exact (hs.differentiableAt (by simp)).hasFDerivAt

lemma eventually_best (h : S.patch.Branches S.kernel G) (t : S.SitesChoice) (e : Edge (Site c)) :
    ∀ᶠ v : Push.In G f in 𝓝 0, S.patch.usesBest S.kernel (S.connector (represent v) t e) := by
  have he : ContinuousAt (Push.deck S e t (G := G)) 0 := continuousAt_pi.mpr fun i =>
    ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff).mpr
      (Push.builds S h e t i).continuousAt.tendsto
  have hb : S.patch.usesBest S.kernel (Push.deck S e t (0 : Push.In G f)) := by
    apply lt_of_le_of_lt ((S.patch.bond_min _).choose_spec 1)
    simpa [Patch.bondCost, Push.deck_zero S h e t] using S.kernel.predictor_cut_pos
  exact he.tendsto.eventually (S.patch.best_open.mem_nhds hb)

/-- Counts actual likelihood in the near-identity uses. It's constant in t on
this branch, `card⁻¹`, not one in our (counting) convention. -/
lemma likelihood_here (h : S.patch.Branches S.kernel G) : ∀ᶠ v : Push.In G f in 𝓝 0,
    ∀ t : S.Choices, S.likelihood (represent v) t = (Fintype.card S.Choices : ℝ)⁻¹ := by
  filter_upwards [eventually_all.mpr (Push.threshold S), eventually_all.mpr fun (s : S.SitesChoice) =>
    eventually_all.mpr fun e => eventually_best h s e] with v hv hb t
  have ht (s : S.Choices) : S.likelihood (represent v) s = S.likelihood (represent v) t := by
    unfold Push.product at hv
    unfold StepData.likelihood
    simp only [Patch.frameMass, hv, ↓reduceIte, Patch.predictorMass, hb]
  have HS := S.chosen h (represent v)
  have he : ∑ s : S.Choices, S.likelihood (represent v) s =
      ∑ _s : S.Choices, S.likelihood (represent v) t := Finset.sum_congr rfl fun s _ => ht s
  rw [he] at HS
  have ha : 0 < (Fintype.card S.Choices : ℝ) := by exact_mod_cast Fintype.card_pos
  apply mul_left_cancel₀ ha.ne'
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ ha.ne'] using HS

/-- One analytic coordinate branch per site BEFORE asking for the tags. On one
common neighborhood (for this fixed finite step & period!), all reads of Frame
and bond prediction here are on their minimizing branch. Off the germ we make
no analytic assertion and retain the actual mass/fallback rules. `LocalRatio`
is a separate issue in the tree-slice loop term later. -/
structure FrameField (S : StepData c f) (G : Gauge) where
  q (x : Site c) : Push.In G f → S.patch.FrameCoordinates G
  zero x : q x 0 = 0
  analytic x : ContDiffAt ℝ ω (q x) 0
  roots : ∀ᶠ z in 𝓝 0,
    (∀ x, S.patch.usesMin S.kernel (Push.product S x (z : Push.In G f)) ∧
      S.patch.minimizing (Push.product S x z) (S.patch.frameFromCoordinates G (q x z)) ∧
        HasFDerivAt (fun b => Analytic.nativeFrameScore S x (z,b)) (0 : S.patch.FrameCoordinates G →L[ℝ] ℝ) (q x z)) ∧
    ∀ t : S.Choices,
      (∀ x, S.frames (represent z) t.1 x = S.patch.frameFromCoordinates G (q x z)) ∧
        S.likelihood (represent z) t = (Fintype.card S.Choices : ℝ)⁻¹ ∧
        ∀ e, S.patch.usesBest S.kernel (S.connector (represent z) t.1 e)

def frameField (h : S.patch.Branches S.kernel G) : FrameField S G := by
  classical
  let t₀ := Classical.arbitrary S.SitesChoice
  refine ⟨rootCoordinates S t₀, root_zero h t₀, root_smooth h t₀,?_⟩
  filter_upwards [eventually_all.mpr fun x => Push.threshold S x,
    eventually_all.mpr (realizes_minimizer h t₀), likelihood_here h,
    eventually_all.mpr fun (t : S.SitesChoice) => eventually_all.mpr fun e => eventually_best h t e]
    with z hz hQ hb hw
  refine ⟨fun x => ⟨hz x,hQ x⟩,fun t => ⟨fun x => ?_, hb t, hw t.1⟩⟩
  have hs := hz x
  change S.patch.frame S.kernel (Push.product S x z) _ = _
  rw [Patch.frame, if_pos hs]
  exact (h.frame_unique _ hs).unique (S.patch.min_exists _).choose_spec (hQ x).1

/-- Use inside an actual stationary graph from the Step. Simultaneous
activation. The graphs may only be germs but one can read the same Kernel
choices on THIS genuine U. No period-independent `𝓝` assertion. -/
theorem FrameField.lit (W : FrameField S G) (F : Forest S.ratio) {P : PathData G}
    {p : Clip} {ρ : Dir G c → AxisChart G F} (h : Critical F p P ρ) :
    ∀ᶠ x in 𝓝 (0 : Dir G c),
      let U := lifting F (represent x) (ρ x)
      let z := Work.F03.axisLog F (x,ρ x)
      represent z=U ∧
        (∀ y, S.patch.usesMin S.kernel (expandAt (S.ratio.embed y) U) ∧
          S.patch.minimizing (expandAt (S.ratio.embed y) U) (S.patch.frameFromCoordinates G (W.q y z))) ∧
        ∀ t : S.Choices, S.likelihood U t = (Fintype.card S.Choices : ℝ)⁻¹ ∧
          (∀ y, S.frames U t.1 y = S.patch.frameFromCoordinates G (W.q y z)) ∧
          (∀ e, S.patch.usesBest S.kernel (S.connector U t.1 e) ∧
            S.prediction U t e = S.patch.best (S.connector U t.1 e)) := by
  let f (x : Dir G c) := (x, ρ x)
  have hf : Tendsto f (𝓝 0) (𝓝 0) := Work.F05.crit_home h
  have hv := (Work.F03.inclusion_smooth (G := G) F).continuousAt.tendsto
  rw [Work.F03.inclusion_zero] at hv
  have hk : Tendsto (Work.F03.axisLog F ∘ f) (𝓝 0) (𝓝 0) :=
    ContinuousAt.tendsto continuousAt_snd |>.comp (hv.comp hf)
  filter_upwards [hf.eventually (Work.F03.inclusion_works F), hk.eventually W.roots] with x hx he
  let z := Work.F03.axisLog F (f x)
  have ht : represent z = lifting F (represent x) (ρ x) := hx
  dsimp only
  refine ⟨ht,fun y => ?_,fun t => ?_⟩
  · rw [← ht]; exact ⟨(he.1 y).1,(he.1 y).2.1⟩
  rw [← ht]
  refine ⟨(he.2 t).2.1,(he.2 t).1,fun e => ?_⟩
  have hh : S.patch.usesBest S.kernel (S.connector (represent z) t.1 e) := (he.2 t).2.2 e
  exact ⟨hh,by rw [StepData.prediction,Patch.predict,if_pos hh]⟩

/-- The frame and tree room of an actual admissible step. -/
structure Region (S : StepData c f) (G : Gauge) where
  larger : Larger S (G := G)
  field : FrameField S G
  tree : Forest S.ratio

def buildRegion (h : Larger S (G := G)) : Region S G :=
  ⟨h, frameField h.1, exampleTree S⟩

end YM.Progress.StationaryScenes
