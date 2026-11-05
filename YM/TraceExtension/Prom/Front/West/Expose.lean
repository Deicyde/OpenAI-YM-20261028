import YM.MergeProof.West.Expose
import YM.TraceExtension.Prom.Front.West.Lins
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Compass
import YM.TraceExtension.Prom.Port.Emulation
import YM.TraceExtension.Prom.Port.Trails
/-!
  Variant of YM.MergeProof.West.Expose for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open YM.Next.Rank.Tapes.West
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

include M
-- constructor; use also at launches with same stencil all-purchases.
set_option maxHeartbeats 400000 in
def e_xposeSky (H : i<k) (g : Course C N p k) (w d : ℕ) (X : Points d)
    {l U z ε b} (hm : middleSky D b k ≤ i) (hx : roomTestSky D b k p l w) (k' : BaleSky C k b p l X H.le)
    (Y : Config G (C.side i p)) {β β'} (hg : β=g.changeβ (i+1)) (hg' : β'=g.changeβ i)
    (h : Dawn (C.path.levels.clock.op i p).patch Pt
      (min (B.prices.α (C.path.levels.clock.J (i+1))) (B.prices.α (C.path.levels.clock.J i))) (B.prices.η (C.path.levels.clock.J (i+1))) (max (B.prices.Ω (C.path.levels.clock.J (i+1))) (B.prices.Ω (C.path.levels.clock.J i))) w U z ε x β β')
    (hY : Healthy (phase x) (d_olmSky X b w (walls x) g.allow H.le k'.1 k'.2.val) Y)
    {τ : ℝ} (ht : τ=phase y)

    (q : Chi) {δ : ℝ} (hp : 0<δ) (hr : 2*δ < firstRadius G) (F : Forest (C.path.levels.clock.op i p).ratio) (c : (C.path.levels.clock.op i p).Choices) :
    MuralSky g (short B N p) X b H hm w k' τ Y ε := by
  let A:=nohole St (retime x) Y
  let K:=k'.1; let v:=k'.2.val; let s:= (Ship.yardSky C b g.allow p).omega K; let t:=spreadCSky C b p ((Station.widerSky ..).trans hm) K
  let o:=core D X b p H.le (Head v); let V:= pull s t Y; let W:=w*walls x
  have hh : Healthy (phase x) (Spindle.patch W o) V := by rw [seenPSky X b _ _ _ hm] at hY; exact (Thirst.s_healthy s t ..).2 hY
  have hC : (book s t A).place=RG.flags (temp (retime x)) V := by
    simp only [place,book,A,nohole,map_empty,biUnion_empty,empty_union]
    exact turns_marks s t _ Y _ (show A.flags=_ from rfl)
  have ha : A.flags=RG.flags (temp (retime x)) Y:=rfl
  have he : clearMargin (book s t A) o W := by unfold clearMargin; rw [hC]; exact Thirst.threshold_fit _ _ h.roam.upper.le _ hh
  let hv:= posing h.roam (le_refl W) he (hx.suite i hm H.le) (turns_marks s t A Y _ rfl) hh
  let V' (Y':RoomView A (retime x) F G):= gazed T c q Y (retime x) β δ Y'
  have hN:= lt_of_lt_of_le H g.allow; have hQ := ships B N i p M hN
  have hS := hot_fitsSky w hx hm H.le h.roam
  let P:=needle T x Y c s t o A F hQ h.strong (B.sized i p) hS ha
  let W0:=w*walls y; let W' a := Peak.readersSky (C:=C) (b:=b) (p:=p) X g.allow (show i+1≤N from Nat.le_trans H g.allow) (K,a)
  let Γ (a : PatchPt X b D p l (show i+1≤k from H)) := shade A F x β q (W' (Head a.val)) W0 (G:=G) (βρ:=retime x)
  have hw : y = betaF G x (C.S.block i) := calendar_warm ..
  let Ω:= viewer T A (retime x) F c Y; let νa a := core D X b p H (Head a)
  let e:= (C.path.levels.clock.op i p).ratio.embed t
  let η:=transverse (retime x) Y s t o A F
  have Hm a : W' (Head a)=affine s e (νa a):= fine_readSky X g.allow _ _ H hm
  have hy a (h' : t_ests X b H v a (C:=C)) θ (hΓ : 0 < Γ a θ) : Healthy τ (d_olmSky X b w (walls y) g.allow (show i+1≤k from H) (C:=C) K a.val) (V' θ) ∧
          ∃ J : G.El,∀ j, spotFt b (i+1) l (show i+1≤k from H) (C:=C) X a.val j →
            |rigid (coloring J (basisFtSky g X b (i+1) g.allow (show i+1≤k from H) (hm.trans (Nat.le_succ _)) K a.val (V' θ))) j -
              ((colorFtSky (short B N p) g b X H hm K v Y j).re + η θ j)| ≤ ε := by
    let L:= νa a.val; unfold Γ at hΓ; rw [Hm] at hΓ
    have hb : Guards (parasol (affine s e L) W0) θ.2 (haze G x β (C.S.block i)) :=
      (paid_veil (A:=A) (F:=F) (G:=G) (parasol (affine s e L) W0) q _ (haze_pos (G:=G) h.steady.visible h.steady.sparks _)).support _ hΓ.ne'
    have hK:= hx.suite (i+1) (hm.trans (Nat.le_succ _)) H
    obtain ⟨h1,h2⟩:= screensSky B M hN s t Y L F c q hv.choose_spec h hK (shades_wSky X hx H hm k' a h') δ θ hS hb
    let X0:=constantGauge (fingers V o) (C.path.levels.clock.op i p).ratio
    have heS : pull s e (V' θ)=watchesSky C b p g.allow (i+1) (hm.trans (Nat.le_succ i)) K (V' θ) := (risingSky g.allow K (V' θ) hm).symm
    refine ⟨?_,X0 L,fun j hj => ?_⟩
    · rw [ht,← under_wSky X g.allow K H hm,← heS]; exact h1
    have hh := h2 j (n_earbySky X b H a.val j hj hx)
    unfold basisFtSky anneals; rw [← heS,← hg]
    -- colorFt aligned only by full watcher
    rw [show colorFtSky (short B N p) g b X H hm K v Y = _ from (show _=purseMean B o V (coupling β') (N:=N) from by rw [hg'];rfl)]
    exact hh
  refine ⟨RoomView A (retime x) F G,inferInstance,Ω,η, WeightedGaussianMarginal45C.Issue.realRank _ P.choose,P.choose_spec,V', gazed_measible c Y q hp hr hQ,?_,Γ,?_,fun a ha V h=>(hy a ha V h).1,fun a ha V h=>(hy a ha V h).2⟩
  · exact fun i H' j h' =>faithfulSightSky B M hN h s t o Y hv.choose_spec F c i j hS (roads_wSky X hx H hm k' i H') (roads_wSky X hx H hm k' j h')
  intro a _
  let p0:=h.strong.ribbon St T rfl hQ (B.sized i p) hS A F c Y rfl .endpoint
  have heP:=shade_auth A F x q (W' (Head a.val)) w Y T c h.steady.visible h.steady.sparks h.strong.cash h.heat h.azure p0
  have hv : w*walls (betaF G x (C.S.block i))=W0 := by unfold W0; rw [← hw]
  change Guarded (shade A F x β q _ W0) _ Ω
  rw [← hv]; exact heP.1
end YM.PhysicalNext.InteractingRank
