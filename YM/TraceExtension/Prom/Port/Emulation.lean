import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Emulation
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Rail
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Emulation for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}

variable {C : Family G} (B : Binding C) (M : C.Makes) {N i p k : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "D" => C.path.levels
local notation "T" => tunnel B N i p
local notation "Pt" => tell B i
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)

-- separate theorem of the reading and its curvature. Need even if V_θ
-- standalone at arbitrary W's interior (possibly with no higher-rank call
-- available on those roots). Call pose at its estimate cost.
include M
lemma screensSky (hi : i<N) {A : Stores St} (s : Signed) (t : Site (C.side i p)) (Y : Config G (C.side i p)) (a : Site (C.side (i+1) p)) (F : Forest (C.path.levels.clock.op i p).ratio) (k : (C.path.levels.clock.op i p).Choices) (q : Chi)
    {W w o U z ε β β' v} (hP : Pose (book s t A) o W x (pull s t Y) v) (h : Dawn (C.path.levels.clock.op i p).patch Pt
      (min (B.prices.α (C.path.levels.clock.J (i+1))) (B.prices.α (C.path.levels.clock.J i))) (B.prices.η (C.path.levels.clock.J (i+1))) (max (B.prices.Ω (C.path.levels.clock.J (i+1))) (B.prices.Ω (C.path.levels.clock.J i))) w U z ε x β β')
    (he0 : 2*(w*walls y+1)<(C.side (i+1) p).val)
    (hZ : ∀ e∈parasol a (w*walls y), separation o ((C.path.levels.clock.op i p).ratio.parent e.1)+walls x+2 ≤ W) (d : ℝ) (Z : RoomView A (retime x) F G) (hκ : 100*(1+radiusB (retime x)) ≤ (C.side i p).val) :
    let e:= (C.path.levels.clock.op i p).ratio.embed t; let y':=gazed T k q Y (retime x) β d Z; let y₀ := pull s e y'; let v':=pull s t Y
    let X:= constantGauge (fingers v' o) (C.path.levels.clock.op i p).ratio; let W:= w*walls y
    Guards (parasol (affine s e a) W) Z.2 (haze G x β (C.S.block i)) →
    Healthy (phase y) (Spindle.patch W a) y₀ ∧ ∀ j : Incidence G (C.side (i+1) p), separation a j.1+2 ≤ W →
      |rigid (coloring (X a) (Tapes.kiosk (coupling β) a y₀)) j -
        ((purseMean B o v' (coupling β') (N:=N) j).re + transverse (retime x) Y s t o A F Z j)| ≤ ε := by
  intro e y' y₀ v' X W0 h'
  let β1:= betaF G x (C.S.block i); let V:= spine v' o; let k':= passport s t k
  let A':= book s t A; let F':=forest s t F; let R:=projected (retime x) Y s t o Z
  let P:=gazed T k' q V (retime x) β d R
  have hc : Atlas.clim D (i+1)=β1:= calendar_warm i C
  have hw : w*walls β1=W0:= by rw [←hc]
  have hp := ships B N i p M hi
  have hS : (palette T A' F' k' (retime x) V .endpoint).PosDef := by
    apply (h.strong.ribbon St T rfl hp (B.sized i p) hκ A' F' k' V ?_ .endpoint).1

    unfold V spine; rw [gauge_flags]; exact hP.tolls
  let L:=w*walls β1
  have HZ : Guards (parasol a L) R.2 (haze G x β (C.S.block i)) := by
    change Guards (parasol a L) ((toGauge (fingers v' o) A' F' (retime x)) *ᵥ _) _
    apply (gauge_in ..).2
    rw [show L=W0 from hw]; exact pepWeight A F s t (retime x) Y a (W0+8) Z.2 _ h'
  have hW : gauge X y₀=P := by
    change gauge X (pull s ((C.path.levels.clock.op i p).ratio.embed t) y')= _
    rw [show pull s ((C.path.levels.clock.op i p).ratio.embed t) y'= gazed T k' q v' (retime x) β d (cusps A F s t (retime x) Y Z) from (fans A F s t T hp Y k q (retime x) d β Z).symm]
    exact winding A' F' (retime x) β d v' T hp (fingers v' o) k' q (cusps A F s t (retime x) Y Z) hS
  obtain ⟨ha,hL⟩:=laminateSky B M hi h.steady h.heart h.strong o W v hP k' q F' (d:=d) R a (hw.symm ▸ he0) HZ (hw.symm ▸ hZ) hκ
  have hv : Healthy (phase β1) (Spindle.patch L a) P := ha
  rw [← hW] at hv
  change Disjoint _ (RG.flags _ (gauge X y₀)) at hv; rw [gauge_flags] at hv
  refine ⟨?_,fun j H=>?_⟩
  · change Healthy (phase (Atlas.clim D (i+1))) _ y₀; rw [hc, ← hw]; exact hv
  change separation _ _ + 2 ≤ W0 at H; rw [← hw] at H
  exact (hL y₀ X hW j H).trans h.scope

omit M in
lemma hot_fitsSky (g : ℕ) {w l b} (hx : roomTestSky C.path.levels b k p l w) (hm : middleSky C.path.levels b k ≤ i) (hh : i ≤ k) (he : Enclosed g G x) : 100*(1+radiusB (retime x))≤(C.side i p).val :=by
  have hp:= hx.radius; have h:= hx.parent
  have hy:20≤w:=by omega
  apply le_trans _ (hx.suite i hm hh).le
  have hh:20*walls x ≤ w*walls x:= Nat.mul_le_mul_right _ hy
  have ht:= he.brims
  have hv:= he.starts
  have hf:200*radiusB x ≤ walls x:= Nat.mul_le_mul_right _ hv |>.trans_eq (pow_two _).symm
  change _≤2*(w*walls x+1)
  omega

include M
-- constructor; use also at launches with same stencil all-purchases.

end YM.PhysicalNext.InteractingRank
