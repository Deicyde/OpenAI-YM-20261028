import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Morning
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Glyph
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Bills

/-!
# Reaching on the selected RoomView. VMeasure purchase

MP (measure preserving) into the curvature cloud, for every held F/k,
with the masks of this sector. Use fundamental sign transport *and*
the Rank finger gauge. Now comparing these orientation-specific entries
to the short kernels using Epoch's `Awake` (no sampling
from the short covariance). Genuine needed off-diagonal estimates on
all their incidence stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Corona Value Glyph Thirst
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
    SectorTools.PhysicalGaussianSwitch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

section compass
abbrev passport (s : Signed) (t : Site c) (k : S.Choices) := AnalyticBridge.GaussianFieldAlignment.Channels.ticket s t k

def projected (x : ℝ) (V : Config G c) (s : Signed) (t : Site c) (o : Site c) (Y : RoomView A x F G) : RoomView (book s t A) x (AnalyticBridge.GaussianFieldAlignment.Locations.forest s t F) G :=
    let v:= fingers (pull (K:=G.El) s t V) o
    let p:=cusps A F s t x V Y
    (GaugeRoute.sendFrozen _ v x (book s t A) _ p.1,toGauge v (book s t A) _ x *ᵥ p.2)

-- Counting in curvature coordinates.
def rowView (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) : Matrix (Incidence G f) (In x A F (G:=G)) ℝ :=
    (dKeys A F x).submatrix toPAC id

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (s : Signed) (t : Site c) (o : Site c) (A : Stores S) (F : Forest S.ratio)

abbrev incTable :=
    let B' := book s t A; let M:=forest s t F
    covView (rowView B' M x G) (palette T B' M (passport s t k) x (spine (G:=G) (pull s t V) o) .endpoint)

-- in Rank querying orientation
def transverse (Y : RoomView A x F G) :=
    let c:= projected x V s t o Y
    rowView (book s t A) (forest s t F) x G *ᵥ c.2

lemma Q_sub (Q : Gaussian.Table (In x A F (G:=G))) i j : covView (rowView A F x G) Q i j =
    covView (dKeys A F x (G:=G)) Q (toPAC i) (toPAC j) := by
  unfold covView; simp_rw [Matrix.mul_apply]; rfl

lemma preserves_counts {Pt : Teller G} {U : ℝ} (h : Pt.Funds S T) (hp : StrongScope S.patch Pt U x)
    (hS : Larger (G:=G) S) (hc : 100*(1+radiusB (retime x)) ≤ c.val) (hP : A.flags=RG.flags (temp (retime x)) V) :
    let C:=incTable T (retime x) V k s t o A F
    C.PosSemidef ∧ MeasurePreserving (transverse (retime x) V s t o A F) (viewer T A (retime x) F k V) (cloud C) := by
  intro C
  let M:=book s t A; let v:=pull s t V; let z:=fingers v o (G:=G); let F':=forest s t F; let l:=passport s t k
  let Q:=palette T M F' l (retime x) v .endpoint
  let R:=palette T M F' l (retime x) (spine v o) .endpoint
  have hr := hp.ribbon S T rfl h hS hc
  have hy : R.PosDef := (hr _ F' l (spine v o) (by unfold spine; rw [gauge_flags]; exact turns_marks s t A V _ hP) .endpoint).1
  have ha := turned_law z M F' (retime x) Pt T v l .endpoint 1 Chi.canonical 0 h (show (palette T M F' l (retime x) (Lattice.gauge z v) .endpoint).PosDef from hy)
  have hw : MeasurePreserving (fun y : RoomView A (retime x) F G => (cusps A F s t (retime x) V y).2) (viewer T A (retime x) F k V) (cloud Q) := fanMap A F s t k h (retime x) V (hr A F k _ hP _).1
  have hh : MeasurePreserving (fun y => (projected (retime x) V s t o y).2) (viewer T A (retime x) F k V) (cloud R) := ha.2.2.2.comp hw
  exact ⟨covView_posSemi _ hy.posSemidef,(view_cloud hy.posSemidef (rowView M F' (retime x) G)).comp hh⟩

private lemma follow {I Θ : Type} [Fintype I] [MeasurableSpace Θ] (M : Matrix I I ℝ) (h : M.PosSemidef) (s : M.IsSymm) (K : Measure Θ) [IsProbabilityMeasure K]
    (u : Θ → I → ℝ) (ht : MeasurePreserving u K (cloud M)) : VMeasure Θ I K u (WeightedGaussianMarginal45C.Issue.realRank M s) := by
  have he:= WeightedGaussianMarginal45C.Issue.fullGlyph M h s
  have hq (p : Normal.poly I) := pay_pull ht (fun v => text v p) (he.prices p).aestronglyMeasurable
  refine ⟨inferInstance,fun q=> (hq q).1.mpr (he.prices q),fun p i=> Eq.trans (hq _).2 ((he.ibp p i).trans (hq _).2.symm)⟩

lemma needle {Pt : Teller G} {U : ℝ} (h : Pt.Funds S T) (hp : StrongScope S.patch Pt U x)
    (hS : Larger (G:=G) S) (hc : 100*(1+radiusB (retime x)) ≤ c.val) (hP : A.flags=RG.flags (temp (retime x)) V) :
    let C:=incTable T (retime x) V k s t o A F
    ∃ hd : C.IsSymm, VMeasure (RoomView A (retime x) F G) (Incidence G f) (viewer T A (retime x) F k V)
      (transverse (retime x) V s t o A F) (WeightedGaussianMarginal45C.Issue.realRank C hd) := by
  intro C
  obtain ⟨h1,h2⟩:= preserves_counts T x V k s t o A F h hp hS hc hP
  exact ⟨Matrix.isHermitian_iff_isSymm.mp h1.isHermitian,follow _ h1 _ _ _ h2⟩
end compass

section earned
variable {C : Family G} (B : Binding C) (M : C.Makes) {N i p : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)
local notation "βF" => betaF G (C.path.levels.clock.hatBeta i) (C.S.block i)
local notation "T" => tunnel B N i p
local notation "J" => C.path.levels.clock.J i
local notation "Pt" => tell B i
include M
lemma faithfulSight (hi : i<N) (hh : C.path.levels.clock.J (i+1)=C.path.levels.clock.J i)
    {A : Stores St} {w W : ℕ} {U t ε β β' : ℝ} (h : Dawn (C.path.levels.clock.op i p).patch Pt
      (B.prices.α J) (B.prices.η J) (B.prices.Ω J) w U t ε x β β') (s : Signed) (z o : Site (C.side i p))
    (V : Config G (C.side i p)) {v} (hp : Pose (book s z A) o W x (pull s z V) v) (F : Forest (C.path.levels.clock.op i p).ratio)
    (k : (C.path.levels.clock.op i p).Choices) (i' j : Incidence G (C.side (i+1) p))
    (he' : 100*(1+radiusB (retime x)) ≤ (C.side i p).val)
    (hx : separation o ((C.path.levels.clock.op i p).ratio.parent i'.1)+walls x+1 ≤ W)
    (hy : separation o ((C.path.levels.clock.op i p).ratio.parent j.1)+walls x+1 ≤ W) :
    let P := incTable T (retime x) V k s z o A F
    ‖(P i' j : ℂ) - (short B N p i).Q.cov i' j‖ ≤ ε := by
  intro P
  let D:=V; let A':=book s z A; let S:=pull s z D; let F':=forest s z F
  let C':=B.world.H N (i+1); let C'':=B.world.H N i
  let Z:=(track (stamp C.path.levels N p) i).Q.cov i' j
  apply (norm_sub_le_norm_sub_add_norm_sub _ Z _).trans (le_trans (b:= x^(-(1/8):ℝ)+t) (add_le_add ?_ ?_) h.swim)
  ·
    have H := h.strong.sight St T rfl (ships B N i p M hi) (B.sized i p) he' C' C'' _ _ _ _ (B.prices.eta_pos _) (B.prices.eta_pos _)
      (B.pays.all N (i+1) hi _) (B.pays.all N i hi.le _) (B.paths N (i+1) hi p) (B.sworn N (i+1) hi p) (B.pays.crossings N i p hi)
      (knot B N i p M hi) W A' o S v hp F' (passport s z k) Chi.canonical 0 .endpoint 1
    rw [show P i' j = _ from Q_sub (retime x) A' F' (palette T A' F' (passport s z k) (retime x) (spine S o) .endpoint) i' j]
    unfold Z; rw [planner_Q B _ _ _ hi,← Complex.ofReal_sub,Complex.norm_real]
    exact H.2 _ _ hx hy
  rw [norm_sub_rev]
  exact (telescope B N i p hh hi h.curves h.cool le_rfl).covariance i' j
end earned
end YM.PhysicalNext.InteractingRank
