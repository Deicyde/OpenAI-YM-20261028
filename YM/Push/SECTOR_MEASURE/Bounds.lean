import YM.Next.EXTRACTION.Base
import YM.Next.FLUCTUATIONS.Sector
import YM.Next.FOUNDATIONS.Primary
import YM.Ovens.Coffee
import YM.Push.SECTOR_MEASURE.Cells

/-!
# Finite-torus envelopes for tagged and peeled sector factors

Joint bounds incl. *variable output* V, under the exact branch
hypotheses / `Teller.Funds`. These use dominated/mass receipts on the
paths; the compactness parts are **fixed-volume** only. No derivative
across a switch.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Lattice RG Wilson Pressure Pressure.Stores Precision Exterior Bloch Tree MeasureTheory
open Next.Fluctuations.Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}

namespace Env
-- reusable (Borel, not AE-quotiented)
lemma compact {α X : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
    {F : α → X} (h : Continuous F) : Envelope F := by
  obtain ⟨C,H⟩ := (isCompact_range h.norm).bddAbove
  exact ⟨h.measurable, C, fun x => H ⟨x,rfl⟩⟩

lemma along {α A X : Type*} [MeasurableSpace α] [MeasurableSpace A] [MeasurableSpace X] [Norm X]
    {F : A → X} (h : Envelope F) {g : α → A} (m : Measurable g) : Envelope (fun x => F (g x)) := by
  obtain ⟨C,H⟩ := h.cost
  exact ⟨h.meas.comp m, C, fun _ => H _⟩

lemma coupled {α A W : Type*} [MeasurableSpace α] [TopologicalSpace A] [CompactSpace A]
    [SecondCountableTopology A] [MeasurableSpace A] [OpensMeasurableSpace A]
    [NormedAddCommGroup W] [ProperSpace W] [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    {b : α → A} {w : α → W} (hb : Measurable b) (h : Envelope w) (F : A × W → ℝ)
    (hf : Continuous F) : Envelope fun a => F (b a, w a) := by
  obtain ⟨D,HD⟩ := h.cost
  obtain ⟨C,H⟩ := ((isCompact_univ.prod (isCompact_closedBall (0:W) D)).image hf.norm).bddAbove
  refine ⟨hf.measurable.comp (hb.prodMk h.meas), C, fun a => H ⟨(b a,w a),⟨Set.mem_univ _,?_⟩,rfl⟩⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using HD a

lemma sub {α : Type*} [MeasurableSpace α] {F H : α → ℝ} (h : Envelope F) (l : Envelope H) :
    Envelope (fun a => F a - H a) := by
  simp only [sub_eq_add_neg]; exact h.add l.neg

end Env

section kernel
variable {α : Type*} [MeasurableSpace α] {U : α → Config G f} {V : α → Config G c}

lemma env_likelihood (k : S.Choices) (h : S.patch.Branches S.kernel G) (he : Measurable U) :
    Envelope (fun a => S.likelihood (U a) k) := by
  refine ⟨(S.likelihood_meas h k).comp he, 1, fun a => ?_⟩
  rw [Real.norm_of_nonneg (S.likelihood_pos _ _), ← S.chosen h (U a)]
  exact Finset.single_le_sum (fun i _ => S.likelihood_pos _ i) (Finset.mem_univ k)

lemma env_noise {Q : α → Config G c} (S : StepData c f) (β : ℝ) (h : Measurable Q) (l : Measurable V) :
    Envelope (fun a => S.noise β (Q a) (V a)) := by
  let f := fun x : Config G c × Config G c => S.noise β x.1 x.2
  have he : Envelope f := Env.compact (S.noise_cont β)
  have hy : Envelope (fun a => f (Q a, V a)) := Env.along (F:=f) (g:=fun a => (Q a,V a)) he (h.prodMk l)
  exact hy

/-- Density per tagged choice, with per-bond `penaltyZ`. -/
def taggedKernel (S : StepData c f) (β : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c) :=
  S.likelihood U k * S.noise β (S.prediction U k) V

lemma noise_pos (β : ℝ) (Q V : Config G c) : 0 < S.noise β Q V :=
  Finset.prod_pos fun _ _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos β)) (Real.exp_pos _)

lemma kernel_nonneg (β : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c) :
    0 ≤ taggedKernel S β k U V := mul_nonneg (S.likelihood_pos ..) (noise_pos β _ _).le

lemma env_tagged (β : ℝ) (k : S.Choices) (m : S.patch.Branches S.kernel G)
    (h : Measurable U) (l : Measurable V) : Envelope (fun a => taggedKernel S β k (U a) (V a)) :=
  (env_likelihood k m h).mul (env_noise S β ((S.prediction_meas m k).comp h) l)
end kernel

section clip
variable {X : PathData G} {a : Clip} {σ C Λ : ℝ} (h : X.Bounds a σ C Λ)
include h

lemma shorten_cont (R d : ℕ) (i : Cell n) : Continuous (fun U => shorten X R d U i) := by
  obtain ⟨F,m,e⟩ := X.ell_dominated h i
  unfold shorten
  refine continuous_tsum ?_ m ?_
  · intro j
    unfold shortenTerm PathData.ellTerms Slot.atSite expandAt; split <;> fun_prop
  intro j u; unfold shortenTerm; split
  next h' => exact e j u
  next h' => rw [norm_zero]; exact (norm_nonneg _).trans (e j u)

lemma env_crown (R d : ℕ) (t : ℝ) (i : Cell n) : Envelope (fun U => crown X a R d t U i) := by
  have he := shorten_cont h R d i
  have hx := show Continuous (fun U : Config G n => G.chord (faceValue U i)) by unfold faceValue; fun_prop
  unfold crown trunk PathData.clipped
  refine (Envelope.piece (PathData.kept_closed ..).measurableSet
    (Env.compact ?_) (Envelope.const _)).add (Envelope.piece
    ((isClosed_le hx continuous_const).measurableSet) (Env.compact ?_) (Env.compact ?_)) <;> fun_prop

lemma plotted_cont (R d : ℕ) (i : Twin n) : Continuous (fun U => plotted X a R d U i) := by
  unfold plotted; split
  next _ => exact shorten_cont h ..
  next _ => unfold shoot faceValue; fun_prop

lemma env_thinned (R d : ℕ) (s : ℝ) (he : 0 ≤ s) (i : Twin n) :
    Envelope (fun U => thinned X a s d R U i) := by
  unfold thinned; split
  · let Y : Config G n → G.Color := fun U => shorten X R d U i.1
    have hb := (PathData.kept_closed (n:=n) (G:=G) a s i.1.1).measurableSet
    have hm : Envelope Y := Env.compact (shorten_cont h R d i.1)
    obtain ⟨A,H⟩ := hm.cost
    refine ⟨Measurable.ite hb hm.meas measurable_const,max A 0,fun u => ?_⟩
    split
    next _ => exact (H u).trans (le_max_left ..)
    next _ => rw [norm_zero]; exact le_max_right ..
  let Q (U : Config G n) := toll U i.1
  let F (u : ℝ) := if u=0 then (1:ℝ) else min 1 (s/u)
  have hf : Measurable F := Measurable.ite (measurableSet_singleton 0)
    measurable_const (measurable_const.min (measurable_const.div measurable_id))
  have hu (u : Config G n) : F (Q u) ∈ Set.Icc (0:ℝ) 1 := by
    unfold F; split
    · constructor <;> norm_num
    exact ⟨le_min zero_le_one (div_nonneg he (G.chord_nonneg _)), min_le_left ..⟩
  let Y (U : Config G n) := shoot a U i.1
  have hX : Envelope Y := Env.compact (by unfold Y shoot faceValue; fun_prop)
  obtain ⟨A,H⟩ := hX.cost
  have hQ : Measurable Q := toll_meas _ (measurable_id)
  change Envelope fun u => F (Q u) • Y u
  refine ⟨(hf.comp hQ).smul hX.meas, A, fun u => ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (hu u).1]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hu u).2).trans (H u)

/-- Whole finite vector of coarse reads. `s` nonnegative so the
clamp multiplies by at most one, including when toll is zero. -/
lemma env_read (R d : ℕ) (s : ℝ) (he : 0 ≤ s) :
    Envelope (fun (U : Config G n) => thinned X a s d R U) := by
  have hj (j : Twin n) := env_thinned h R d s he j
  refine ⟨measurable_pi_lambda _ fun j => (hj j).meas,?_⟩
  choose A H using fun j => (hj j).cost
  refine ⟨∑ j, max 0 (A j),fun u => ?_⟩
  have hp : ∀ j, 0 ≤ max 0 (A j) := fun _ => le_max_left ..
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hp i))).mpr fun i => ?_
  exact (H i u).trans ((le_max_right ..).trans
    (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)))

end clip

lemma rated_cont (i : Site n) (w : Walk) (s : ℝ) : Continuous (fun U : Config G n => rated U i w s) := by
  refine continuous_clm_apply.mpr fun p => ?_
  change Continuous (fun U : Config G n => s • G.projectColor (G.conjugate (travel U i w) (G.colorMat p)))
  have he : Continuous (fun U : Config G n => G.projectColor (G.conjugate (travel U i w) (G.colorMat p))) :=
    G.projectColor.continuous_of_finiteDimensional.comp (show Continuous _ by unfold Gauge.conjugate; fun_prop)
  fun_prop

lemma lane_cont {α b : Type*} {K : Row α b} (H : K.safe) (i : Co n α) (j : Co n b) (R d : ℕ) :
    Continuous (fun U : Config G n => lane R d U K i j) := by
  unfold lane
  refine continuous_tsum ?_ (H i.2 j.2) ?_
  · intro t
    unfold priced; split
    next _ => exact rated_cont ..
    next _ => exact continuous_const
  intro t u; unfold priced; split
  next _ => exact Work.E03.norm_rated_le ..
  next _ => simp

lemma leap_cont {M : Towers S.patch.L} (H : M.mf.safe) (R : ℕ) (i : Twin f) (j : Twin c) :
    Continuous (fun U : Config G c => leap S M R U i j) := by
  unfold leap
  refine continuous_tsum ?_ (H (S.ratio.residue (mesh i).1,(mesh i).2) (mesh j).2) ?_
  · intro t
    have hl : Continuous (replica (G:=G) S.ratio) := by
      unfold replica
      apply continuous_pi
      intro i; split <;> fun_prop
    dsimp only [casted]; split
    next _ => exact (rated_cont ..).comp hl
    next _ => exact continuous_const
  intro t u; dsimp only [casted]; split
  next _ => exact Work.E03.norm_rated_le ..
  next _ => simp

section peeled
variable {α : Type*} [MeasurableSpace α] {U : α → Config G f} {V : α → Config G c}

lemma funds_branch (h : P.Funds S T) : S.patch.Branches S.kernel G := h.knobs.symm ▸ h.kernel

lemma env_cuts (hT : P.Funds S T) (x : ℝ) (h : Measurable U) (l : Measurable V) :
    (∀ i : Cell f,
      Envelope (fun a => crown T.up T.high (till x) 1 (fiery G x S.patch.L) (U a) i)) ∧
      (∀ j : Cell c, Envelope (fun a => crown T.down T.low (till x) S.patch.L.val (temp x) (V a) j)) := by
  obtain ⟨B,C,hb,hc⟩ := hT.feeds
  rw [← hT.high] at hb; rw [← hT.low] at hc
  exact ⟨fun i => Env.along (env_crown hb _ _ _ i) h, fun j => Env.along (env_crown hc _ _ _ j) l⟩

lemma env_gap (hT : P.Funds S T) (x : ℝ) (h : Measurable U) (l : Measurable V) :
    Envelope (fun a => crownGap T x (U a) (V a)) := by
  obtain ⟨hb,hc⟩ := env_cuts hT x h l
  exact Env.sub (Envelope.sum _ _ hb) (Envelope.sum _ _ hc)

lemma env_incoming (hT : P.Funds S T) (β x : ℝ) (k : S.Choices) (h : Measurable U) (l : Measurable V) :
    Envelope (fun a => incoming T β x k (V a) (U a)) :=
  (env_tagged β k (funds_branch hT) h l).mul
    (((Envelope.const _).mul (env_gap hT x h l)).exp)

open Pressure.Tube

lemma cont_zip {α I J : Type*} [TopologicalSpace α] [Fintype J] {g : α → I → J → Pay G}
    {z : α → J → G.Color} (h : ∀ i j, Continuous (fun a => g a i j))
    (l : ∀ i, Continuous (fun a => z a i)) (i) : Continuous (fun a => zip (g a) (z a) i) :=
  continuous_finsetSum _ fun j _ => (h i j).clm_apply (l j)

lemma cont_unzip {α I J : Type*} [TopologicalSpace α] [Fintype I] {g : α → I → J → Pay G}
    {z : α → I → G.Color} (h : ∀ i j, Continuous (fun a => g a i j))
    (l : ∀ i, Continuous (fun a => z a i)) (j) : Continuous (fun a => unzip (g a) (z a) j) := by
  apply continuous_finsetSum
  intro i _
  exact (ContinuousLinearMap.adjoint.continuous.comp (h i j)).clm_apply (l i)

-- Assist elaboration of finite-dimensional joint compositions.
set_option maxHeartbeats 800000 in
lemma env_assessed (hT : P.Funds S T) (x : ℝ) (k : S.Choices) (h : Measurable U) (l : Measurable V)
    (A : Stores S) : Envelope (fun a => A.assessed T x (U a) (S.prediction (U a) k) (V a)) := by
  obtain ⟨B,D,HX,HY⟩ := hT.feeds
  rw [← hT.high] at HX; rw [← hT.low] at HY
  let s := temp x
  let R := till x
  let W : α → Twin c → G.Color := fun a => T.vision R s (V a)
  have hm : Envelope W := Env.along (env_read HY R S.patch.L.val s (temp_nonneg _)) l
  let Q : α → Config G c := fun a => S.prediction (U a) k
  have he : Measurable Q := (S.prediction_meas (funds_branch hT) k).comp h
  -- Lift formulas other than cut crowns to this domain; vector w is
  -- measurable and bounded, so evaluates these continuous formulas with
  -- finite envelopes.
  let b : α → Config G f × Config G c × Config G c := fun a => (U a,Q a,V a)
  let X := ((Config G f × Config G c × Config G c) × (Twin c → G.Color))
  have costs (F : X → ℝ) (hc : Continuous F) : Envelope (fun a => F (b a,W a)) := by
    apply Env.coupled (b:=b) (w:=W) (h.prodMk (he.prodMk l)) hm F hc
  let z (a : X) := a.2
  let Λ (a : X) := T.Φ R a.1.2.2
  let M (a : X) := T.Φ' R a.1.2.2
  let N (a : X) := T.N R a.1.2.2
  let wh (a : X) := T.Xf R a.1.1
  let wc (a : X) := T.Xn R a.1.2.2
  let K (a : X) := Tube.Z S a.1.2.1 a.1.2.2
  obtain ⟨h1,h2,h3,-⟩ := hT.crosses
  have hc1 : Continuous (fun a : X => a.1.1) := by fun_prop
  have hc : Continuous (fun a : X => a.1.2.2) := by fun_prop
  have hz (i : Twin c) : Continuous (fun a => z a i) := by unfold z X; fun_prop
  have hw (i : Twin f) : Continuous (fun a => wh a i) := (plotted_cont HX ..).comp hc1
  have hh (i : Twin c) : Continuous (fun a => wc a i) := (plotted_cont HY ..).comp hc
  have hcK i : Continuous (fun a => K a i) := by unfold K Tube.Z X; fun_prop
  have hl i j : Continuous (fun a => Λ a i j) :=
    (leap_cont (Row.rights _ _ h3 P.width.le) ..).comp hc
  have hg i j : Continuous (fun a => M a i j) :=
    (lane_cont (Row.rights _ _ h1 P.width.le) ..).comp hc
  have hu i j : Continuous (fun a => N a i j) :=
    (lane_cont (Row.rights _ _ h2 P.width.le) ..).comp hc
  let F a := zip (Λ a) (z a)
  let I a := zip (M a) (z a)
  let L a := zip (N a) (z a)
  have hf i : Continuous (fun a => F a i) := cont_zip hl hz i
  have hi i : Continuous (fun a => I a i) := cont_zip hg hz i
  have hs i : Continuous (fun a => L a i) := cont_zip hu hz i
  obtain ⟨g1,g2⟩ := env_cuts hT x h l
  -- Extract the continuous formulas
  have wF i : Envelope (fun a => T.workF R (U a) (V a) (fiery G x S.patch.L) s i) := by
    refine (g1 i).add (costs (fun a => ∑ j : Bool,
      (‖F a (i,j)‖^2/2 - inner ℝ (F a (i,j)) (wh a (i,j)))) ?_)
    apply continuous_finsetSum
    intro j _; exact ((((hf _).norm.pow _).div_const _).sub ((hf _).inner (hw _)))
  have wI i : Envelope (fun a => T.workI R (Q a) (V a) s i) := by
    refine costs (fun a => monetary S a.1.2.1 a.1.2.2 i + (‖I a i‖^2/2 - inner ℝ (I a i) (K a i))) ?_
    refine Continuous.add ?_ ((((hi _).norm.pow _).div_const _).sub ((hi _).inner (hcK _)))
    unfold monetary wire X; fun_prop
  have wC i : Envelope (fun a => T.workC R (V a) s i) := by
    refine Env.sub (costs (fun a => ∑ j : Bool,
      (inner ℝ (z a (i,j)) (wc a (i,j)) - ‖z a (i,j)‖^2/2)) ?_) (g2 i)
    exact continuous_finsetSum _ fun j _ => ((hz _).inner (hh _)).sub (((hz _).norm.pow _).div_const _)
  have wN i : Envelope (fun a => T.workN R (V a) s i) :=
    costs (fun a => ‖L a i‖^2/2) (((hs i).norm.pow _).div_const 2)
  have wL i : Envelope (fun a => T.workL R (U a) (Q a) (V a) s i) := by
    refine costs (fun a => ∑ j : Bool, inner ℝ (z a (i,j))
      (unzip (Λ a) (wh a) (i,j) + unzip (M a) (K a) (i,j) - wc a (i,j))) ?_
    apply continuous_finsetSum
    intro j _; exact (hz _).inner (((cont_unzip hl hw _).add (cont_unzip hg hcK _)).sub (hh _))
  have wD i : Envelope (fun a => T.workD R (V a) s i) := by
    refine costs (fun a => ∑ j : Bool, inner ℝ (z a (i,j)) (z a (i,j) -
      (unzip (Λ a) (F a) (i,j) + unzip (M a) (I a) (i,j) + unzip (N a) (L a) (i,j))) / 2) ?_
    apply continuous_finsetSum
    intro j _; exact ((hz _).inner ((hz _).sub
      (((cont_unzip hl hf _).add (cont_unzip hg hi _)).add (cont_unzip hu hs _)))).div_const 2
  unfold assessed tally talli talll tallc talln
  refine ((((Envelope.sum _ _ wF).add (Envelope.sum _ _ wI)).add (Envelope.sum _ _ wC)).add
    (Envelope.sum _ _ wN)).add ?_
  exact Envelope.sum _ (fun i a => T.workL R (U a) (Q a) (V a) s i + T.workD R (V a) s i)
    fun i => (wL i).add (wD i)

lemma env_unassigned (hT : P.Funds S T) (x : ℝ) (k : S.Choices)
    (h : Measurable U) (l : Measurable V) (A : Stores S) :
    Envelope (fun a => unassigned A T x (U a) k (V a)) := by
  have he : Measurable (fun a => S.prediction (U a) k) := (S.prediction_meas (funds_branch hT) k).comp h
  obtain ⟨g1,g2⟩ := env_cuts hT x h l
  have hc i : Envelope (fun a => monetary S (S.prediction (U a) k) (V a) i) := by
    let Y := fun a : Config G c × Config G c => monetary S a.1 a.2 i
    have hy : Continuous Y := by unfold Y monetary wire; fun_prop
    exact Env.along (g:=fun a => (S.prediction (U a) k,V a)) (Env.compact hy) (he.prodMk l)
  unfold unassigned
  simp_rw [T.locates]
  exact Env.sub (Env.sub ((Envelope.sum _ _ g1).add (Envelope.sum _ _ hc)) (Envelope.sum _ _ g2))
    (env_assessed hT x k h l A)

lemma env_outgoing (hT : P.Funds S T) (β x : ℝ) (k : S.Choices)
    (h : Measurable U) (l : Measurable V) (A : Stores S) :
    Envelope (fun a => outgoing A T β x k (V a) (U a)) :=
  (env_likelihood k (funds_branch hT) h).mul
    (((Envelope.const _).mul (env_unassigned hT x k h l A)).exp)

end peeled
end YM.Push.SectorMeasure
