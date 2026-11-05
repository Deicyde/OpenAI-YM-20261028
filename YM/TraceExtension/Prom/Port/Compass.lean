import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Compass
import YM.TraceExtension.Prom.Port.Epoch
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Compass for dynamic stops. Pulse extension.
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

-- Counting in curvature coordinates.

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (s : Signed) (t : Site c) (o : Site c) (A : Stores S) (F : Forest S.ratio)

-- in Rank querying orientation

end compass

section earned
variable {C : Family G} (B : Binding C) (M : C.Makes) {N i p : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "T" => tunnel B N i p
local notation "Pt" => tell B i
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)

local notation "J" => C.path.levels.clock.J i

include M
lemma faithfulSightSky (hi : i<N)
    {A : Stores St} {w W : ℕ} {U t ε β β' : ℝ} (h : Dawn (C.path.levels.clock.op i p).patch Pt
      (min (B.prices.α (C.path.levels.clock.J (i+1))) (B.prices.α J)) (B.prices.η (C.path.levels.clock.J (i+1))) (max (B.prices.Ω (C.path.levels.clock.J (i+1))) (B.prices.Ω J)) w U t ε x β β') (s : Signed) (z o : Site (C.side i p))
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
  exact (telescopeSky B N i p hi h.curves h.cool le_rfl).covariance i' j
end earned
end YM.PhysicalNext.InteractingRank
