import YM.AnalyticBridge.VERIFIED_RESET_STEP.Dial
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Topology
import YM.Next.BOUNDARY.Coordinates
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.UVNext.COUPLING_RESET.Precision

/-! Pure output payment gate and an open compatibility rule for auxiliary
recipe predicates, before merging pellets. `BatchPay` instance in Consumer.
No out-band condition; even a one-point start is only requested **in** its
incoming lane and may leave the band after it shoots. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Return
open Function Filter Set Lattice Wilson RG RG.Shoot RG.Supply Pressure MeasureTheory  Next.Fluctuations.Sector 
open Precision UVNext.CouplingReset Collection Input Geo Averaging WilsonStartup Ovens Progress.DirectedRecipe
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)

def forcing (m : ℕ) := Real.exp (-P.g (B.a.clock.J (m+1)) * B.a.clock.monitor (m+1)^2)

/-- These are quantitative compatibility requirements, not buying all claims
on every previously issued Directed! Exponent +3 used on the HRGv E-terms,
hit +1 on incoming separated output polymers *pre* H01, both output-side
reserves. Stage transition may hold or decrease the derivative orders at m,
not buying by consuming width on each entry. `closes` solely an implication
on numerical mass caps (e.g. via `Deployment.recloses` at this level). -/
structure Prices (B : Directed G I Z K P) (N m p : ℕ) (q : ResetPrices) (l : Set ℝ) (H w δ b : ℝ → ℝ) : Prop where
  decent : Decent (B.a.params m).clip (B.a.budget m)
  width : Width (B.a.budget m) (B.a.params m).clip (B.a.params m).width
  early : ∀ x∈l,H x ≤ funds B.a m q / 4
  cubic : ∀ j x, W.betaEntry j ≤ x → ∀ i, Push.PriceCompiler.StepStages j i → CubicGate D q j i x
  fees : ∀ x∈l, let a := B.a.params m; Fees G (B.a.budget m) a.clip a.width a.paths (B.kin.alpha N m) (H x) (w x) (δ x) (b x)
  closes : ∀ x∈l, ∀ A : Activities G (B.a.S.side m p), A.Valid (B.a.budget m) (δ x) (b x) →
    A.Valid (B.a.budget m) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m) ∧ A.KBound (B.a.budget m) (forcing B m)

/-- Interface BEFORE choosing trial solutions; on an arbitrary bake there's
real work to check that its retain/next are met. Consumer instantiates this
for the nontrivial PeriodFuture recipe (with permissions free or additional
permissions to be funded). No claim that an arbitrary incompatible bake works
if only the prices on numerical rows have been paid. -/
def Honors (N m p : ℕ) (l : Set ℝ) (H δ b : ℝ → ℝ) (Q : In B.a m p) := ∀ x ∈ l,
    Lives B.bake N (m+1) p (Q x) → (Q x).beta ∈ band B.a (m+1) → ∀ Δ : ℝ, ∀ (X : Pipes G (B.a.S.side m p)) (d : Tap G (B.a.S.side m p)),
    let r := B.a.budget m; let c := (B.a.params m).clip; let R := B.kin.path N m
    let β := predictor B N Q x+Δ
    Ingredients X d r (δ x) (b x) →
    r.threshold^2 * |Δ| ≤ H x → (∀ U, (trunk R c r X d β 0).eval U * Real.exp (∑' i, d.logarithm i U) = target Q x U / target Q x 1) →
      let T := finish R c r X d β (flatRate B.a m p (Q x))
      B.bake.retain N m p T ∧ B.bake.next N m p T (Q x)

lemma enough_room (m p : ℕ) : 20 < (B.a.S.side m p).val := by have := B.a.fits.sizeT m p; unfold Levels.S; omega

def ledger (N m p : ℕ) (X : Listing G (B.a.S.side m p)) (a : ℝ → Collection.Source G (B.a.S.side m p)) : Terms B.a m p :=
    terms X (B.kin.path N m) (B.a.params m).clip (B.a.budget m) (B.kin.alpha N m) a

def result {m p : ℕ} (N : ℕ) (Q : In B.a m p) (X : Listing G (B.a.S.side m p)) (a : ℝ → Collection.Source G (B.a.S.side m p)) (x : ℝ) :=
    (board B N (ledger B N m p X a)).install (target Q) (predictor B N Q) (fun y => Averaging.delta (X.read (a y))) x

variable {B} {m p N : ℕ} {X : Listing G (B.a.S.side m p)} {a : ℝ → Collection.Source G (B.a.S.side m p)} {Q : In B.a m p} {l : Set ℝ} {H w τ δ b : ℝ → ℝ} {q : ResetPrices}
    (g : G.Simple) (hm : m<N) (hb : Prices B N m p q l H w δ b) (hx : ∀ x∈l, Local X (B.a.budget m) (a x) (H x) (w x))
    (he : ∀ x∈l, target Q x = earlyValue X (B.kin.path N m) (B.a.params m).clip (B.a.budget m) (a x) (Q x).beta (τ x) (B.kin.alpha N m))
    (hc : Compared X (B.a.budget m) a l)
include g hm hb hx
private lemma support_bill (x : ℝ) (h : x∈l) : let R := B.kin.path N m; let c := (B.a.params m).clip; let r := B.a.budget m
    Ingredients (shelves X R r) (branch X R c r (a x) (B.kin.alpha N m)) r (δ x) (b x) :=
  (hx x h).renew g (B.support.cap N m hm.le) hb.decent hb.width _ (enough_room B m p) (hb.fees x h)
lemma records {x : ℝ} (h : x∈l) (d : ℝ) : let v := ledger B N m p X a x d
    v.Valid (B.a.budget m) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m) ∧ v.KBound (B.a.budget m) (forcing B m) :=
  hb.closes _ h _ ((support_bill g hm hb hx x h).gates ..)
lemma catalog (hc : Compared X (B.a.budget m) a l) (t : Set ℝ) : Catalog (board B N (ledger B N m p X a)) l t
    (B.a.clock.allowance m) (B.a.clock.forcedAllowance m) := by
  rw [board,B.bases]; unfold ledger terms
  have hR := B.support.cap N m hm.le
  apply catalogs (hc.completed g hx hR hb.decent hb.width (enough_room B m p) _ continuousOn_const continuousOn_const hb.fees) _ hR
  intro x hi; exact (records g hm hb hx hi 0).1

include he in
lemma settled {x : ℝ} (h : x∈l) : let A := board B N (ledger B N m p X a); let Δ := Averaging.delta (X.read (a x)); let v := vac (a x) (τ x)
    (A.trial (predictor B N Q) x Δ v).eval = target Q x ∧ UVNext.CouplingReset.scalar (target Q) x = v := by
  intro A Δ v
  have hR := B.support.cap N m hm.le
  have hE : (A.trial (predictor B N Q) x Δ v).eval = target Q x := by
    dsimp only [Template.trial,A,board]; rw [B.bases,he x h]; exact (hx _ h).actual g hR hb.decent hb.width _ (enough_room B m p) (hb.fees x h) ..
  exact ⟨hE,A.scalar_eq ((records g hm hb hx h Δ).1.regular.at_flat) (congr_fun hE 1)⟩

include he in
lemma splits_zero {x : ℝ} (h : x∈l) (hp : 0 < target Q x 1) : let R := B.kin.path N m; let c := (B.a.params m).clip
    let r := B.a.budget m; let d := branch X R c r (a x) (B.kin.alpha N m); let _v := UVNext.CouplingReset.scalar (target Q) x
    ∀ U, (trunk R c r (shelves X R r) d (predictor B N Q x + Averaging.delta (X.read (a x))) 0).eval U * Real.exp (∑' i, d.logarithm i U) = target Q x U / target Q x 1 := by
  intro R c r d v U
  rw [eq_div_iff hp.ne',mul_comm _ (target Q x 1),← Real.exp_log hp,show Real.log (target Q x 1) = v*Fintype.card (Site (B.a.S.side m p)) from
    (div_mul_cancel₀ _ (sites_pos _).ne').symm, ← (support_bill g hm hb hx _ h).exact_eval]
  obtain ⟨H,hv⟩ := settled g hm hb hx he h
  unfold Template.trial board at H; rw [← hv,B.bases] at H
  exact congr_fun H U
end YM.AnalyticBridge.VerifiedReset.Return
