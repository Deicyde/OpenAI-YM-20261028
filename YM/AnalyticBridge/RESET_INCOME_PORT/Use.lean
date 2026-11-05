import YM.AnalyticBridge.RESET_INCOME_PORT.Income

set_option warningAsError false

/-!
# Consumer: a reset branch through a genuine income port

On Journal prices from the sector change and concrete (post) Clothing
formula obtain a continuous labelled Curve/root with EVERY all-good output
calibration and the quantitative branch estimates. Includes e.g. the exact
coupling correction col x supplied in that formula with 0 continuity or
pricing assumptions on it a priori. Conditional: to promote to Move still
need arbitrary-coarse-field evaluator equality (including flags etc), actual
production of these Income inputs incl Catalog and the exponential forced
and recipe predicates anywhere they're needed. Not claiming a Program or
any changing trajectories are produced or that col is available.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open Push.PriceCompiler Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P) {q : ResetPrices}
    {s : Set ℝ} {g a E : ℕ → ℕ → ℝ} {N m p : ℕ} {F : Terms B.a m p} {Q : In B.a m p}

lemma disclosed {S v col} (hS : Prereset B q s N m p Q v S) (h : Clothing B q s (N:=N) F S col)
    {U : Config G (B.a.S.side m p)} (hU : RG.flags (B.a.budget m).threshold U=∅) {x l : ℝ} (hx : x∈s)
    (hw : l∈window B.a m q) : (board B N F).residual (target Q) U (predictor B N Q) x l =
      (l-col x)*secondTerm (B.a.params m).clip (B.kin.path N m) U := by
  unfold Template.residual contrast
  rw [hS.flat hx,hS.emit x hx U hU,Real.log_exp,h x hx l hw U hU]
  unfold board Template.leg Template.background predictor largeOp
  obtain ⟨ha,hb,-⟩ := unmasked_precision (B.kin.path N m) (B.a.params m).clip hU
  dsimp only; rw [B.bases,ha,hb]; ring

lemma must_fit {V : Config G (B.a.S.side m p)} {S v col d μ} (hS : Prereset B q s N m p Q v S)
    (h : Clothing B q s (N:=N) F S col) (hv : RG.flags (B.a.budget m).threshold V=∅) :
    let f := (board B N F).residual (target Q) V (predictor B N Q)
    let t := window B.a m q
    Response s t μ f → Zeroes s t f d → (∀ x∈s,d x=col x) := by
  intro f t hr hz x hx
  let r := width B.a m q
  have hq : 0<r := q.rad_pos ..
  have he : 0∈t := ⟨neg_nonpos.mpr hq.le,hq.le⟩; have ht : r∈t := ⟨he.1.trans hq.le,le_rfl⟩
  let v := secondTerm (B.a.params m).clip (B.kin.path N m) V
  have hi i (hh : i∈t) : f x i=(i-col x)*v := disclosed B hS h hv hx hh
  have hμ := (mul_pos hr.margin hq).trans_le (by simpa only [sub_zero] using hr.gain x hx 0 he r ht hq.le)
  rw [hi r ht, hi 0 he] at hμ
  have ht : v ≠ 0 := fun hh => by simp [hh] at hμ
  have h0 := hz.sol x hx; rw [hi _ (hz.admissible hx)] at h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right ht)

/-- Along the actually priced one-step. Don't demand either full s or
output-frame `D'(V)`, just the real all-good values with the common family
prices. -/
theorem rolls (hW : Ringing K g W) (hc : Cosmos Z K W g a E) (hm : m < N)
    (hL : ∀ x∈s, Lives B.bake N (m+1) p (Q x)) (hb : ∀ x∈s,(Q x).beta∈band B.a (m+1))
    (H χ u k) (F : Terms B.a m p) (V : Config G (B.a.S.side m p)) (η : ℕ → ℝ) (hp : PricedReset B.a η q) (hU : Usable B η N m p V)
    (hq : Curve (B.a.budget (m+1)) Q s) (hg : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x) :
    let e := assigned B N m p g a H χ u k
    ∀ (J : ℝ → Journal e) (v : ℝ → ℝ) (t : ℝ → HeadGas.Token) (l : ℝ → ℕ → ℝ) (col : ℝ → ℝ),
      (∀ x∈s,(J x).Read (Q x) (fun V => v x*sites (B.a.S.side m p)-demand B N (Q x) V) (t x)) →
      (∀ x∈s,(J x).Rates (l x) (funds B.a m q / 4)) → Clothing B q s (N:=N) F (fun x => (J x).prints) col →
      Catalog (board B N F) s (window B.a m q) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m) →
        ∃ d, let T := (board B N F).install (target Q) (predictor B N Q) d
             ContinuousOn col s ∧ Curve (B.a.budget m) T s ∧ ∀ x∈s, d x=col x ∧
               |d x| ≤ width B.a m q ∧ (T x).beta = predictor B N Q x + col x ∧
               |(T x).v-v x| ≤ funds B.a m q / 4 ∧ ∀ U, RG.flags (B.a.budget m).threshold U=∅ →
                (T x).eval U = target Q x U := by
  intro e J v t l col hT hJ hd hC
  obtain ⟨he,hI⟩ := journals B hW hc hm Q hL hb H χ u k F V hU.1 hg J v t l hT hJ
    (Or.inl (clothed B hd hU.1)) hC
  obtain ⟨d,hR,hz,ht,hF,_⟩ := correct hp hU hI hq hL
  have hQ := must_fit B he hd hU.1 hR hz
  refine ⟨d,?_⟩; intro T
  refine ⟨ht.congr (fun x hx => (hQ x hx).symm),hF,fun x hx => ?_⟩
  have hw := hz.admissible hx; have hj := hQ x hx
  have hc := hC.valid _ hx _ hw
  refine ⟨hj,abs_le.mpr hw,congr_arg (predictor B N Q x + ·) hj,(he.value_income hU.1 hx).2.1,fun U hi => ?_⟩
  have hb := disclosed B he hd hi hx hw
  have hh : (board B N F).residual (target Q) U (predictor B N Q) x (d x)=0 := by rw [hb,hj]; simp
  have hU' := (he.value_income hi hx).1
  exact ((board B N F).passes hi hc.regular.at_flat hU'.1 hU'.2 hh).2
end YM.AnalyticBridge.ResetIncome
