import YM.AnalyticBridge.VERIFIED_RESET_STEP.Inputs
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Payment

/-! Main conditional one-step stability at the supplied physical estimates,
even on a singleton call. `result` uses the computed ∆ and actual v from the
field identity. Uses the same trial family (and solves in the purchased
small interval by the genuine two-test service); gives both width and explicit
per-site and inverse-threshold earnings with no favorable-volume error. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Return
open Function Filter Set Lattice Wilson RG RG.Shoot RG.Supply Pressure MeasureTheory Next.SectorChange Next.Fluctuations.Sector Push.SectorMeasure
open Precision UVNext.CouplingReset Collection Input Geo Averaging Progress.DirectedRecipe
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P}
    {m p N : ℕ} {X : Listing G (B.a.S.side m p)} {a : ℝ → Collection.Source G (B.a.S.side m p)} {Q : In B.a m p} {l : Set ℝ} {H w τ δ b : ℝ → ℝ}
    {q : ResetPrices} {η : ℕ → ℝ}
variable (g : G.Simple) (hm : m<N) (hb : Prices B N m p q l H w δ b) (hx : ∀ x∈l, Local X (B.a.budget m) (a x) (H x) (w x))
    (he : ∀ x∈l, target Q x = earlyValue X (B.kin.path N m) (B.a.params m).clip (B.a.budget m) (a x) (Q x).beta (τ x) (B.kin.alpha N m))
    (hc : Compared X (B.a.budget m) a l)
    (hP : PricedReset B.a η q) {V : Work B m p} (hv : Usable B η N m p V)
include g hm hb hx he
include hv in
private lemma yield_shape {x : ℝ} (h : x∈l) (d : ℝ) : let A := board B N (ledger B N m p X a)
    A.residual (target Q) V (predictor B N Q) x d = (d - Averaging.delta (X.read (a x))) * A.leg V := by
  intro A
  refine Fixed.rate A (fun _ => rfl) ((records g hm hb hx h 0).1.regular.at_flat) ?_ (settled g hm hb hx he h).1 d
  exact hv.1
include hv hP in
lemma physical_shape : Template.ShapeControl (board B N (ledger B N m p X a)) l (window B.a m q) (target Q) V (predictor B N Q) := by
  intro x h U
  let A := board B N (ledger B N m p X a); let Δ := Averaging.delta (X.read (a x))
  have hp := (hP m).1.1; have ht := (B.a.budget m).threshold_pos; have hn := sites_pos (B.a.S.side m p)
  exact Fixed.price_shape A (fun _ => rfl) ((records g hm hb hx h Δ).1.regular.at_flat) hv.1 (lt_of_lt_of_le (by positivity) hv.2)
    (settled g hm hb hx he h).1 U (fun d hd => (abs_le.mpr hd).trans (q.unit ..))
omit he in
include hc hv in
lemma earns (h : Prereset B q l N m p Q τ (fun x => X.read (a x))) : Income B N m p q l Q V (ledger B N m p X a) := by
  have hf : 0 ≤ funds B.a m q := mul_nonneg (q.cost_pos ..).le (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  exact h.income hv.1 hb.cubic hm (catalog g hm hb hx hc _) (fun x hx a ha b hb =>
    ⟨0,fun _ => by simp [board, ledger, terms], fun o => by simpa [board, ledger, terms,SumBudget]⟩)
include hv hP hc
lemma remainders (hq : Honors B N m p l H δ b Q) (h : Prereset B q l N m p Q τ (fun x => X.read (a x)))
    (hQ : ∀ x∈l, Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta∈band B.a (m+1)) : Remainder B N m p q l Q V (ledger B N m p X a) := by
  refine ⟨physical_shape g hm hb hx he hP hv,fun x hh d hd => (records g hm hb hx hh d).2,fun x hh d hd v hL => ?_⟩
  let A := board B N (ledger B N m p X a); let Δ := Averaging.delta (X.read (a x))
  have hp := (hP m).1.1; have ht := (B.a.budget m).threshold_pos; have hn := sites_pos (B.a.S.side m p)
  have hleg : 0 < A.leg V := lt_of_lt_of_le (by positivity) hv.2
  have hF : ∀ i, (A.terms x d).E i 1 = 0 := (records g hm hb hx hh 0).1.regular.at_flat
  change (A.trial (predictor B N Q) x d v).eval = target Q x at hL
  have hr : A.residual (target Q) V (predictor B N Q) x d = 0 := sub_eq_zero.mpr
    (A.contrast_eq hF hv.1 (congr_fun hL 1) (congr_fun hL V)).symm
  have hDelta : d = Δ := eq_of_sub_eq_zero (mul_eq_zero.mp ((yield_shape g hm hb hx he hv hh d).symm.trans hr) |>.resolve_right hleg.ne')
  have hV := A.scalar_eq hF (congr_fun hL 1)
  let r := B.a.budget m
  let R := B.kin.path N m; let S := shelves X R r; let d := branch X R (B.a.params m).clip r (a x) (B.kin.alpha N m)
  -- Reuse the Batch witness, not infer any permission on a different payload by shape equality alone!
  dsimp only [Template.trial, board]; rw [hDelta,← hV,B.bases]
  exact hq x hh (hQ x hh).1 (hQ x hh).2 Δ S d ((hx x hh).renew g (B.support.cap N m hm.le) hb.decent hb.width _ (enough_room B m p) (hb.fees x hh))
    (delta_bound g (hx x hh).projects) (splits_zero g hm hb hx he hh ((earns g hm hb hx hc hv h).pos x hh).1)

variable {f r E : Wages} (T : Wood B m p) (d : Bookings B m p f) (χ : Chi)
omit hv he in
theorem reset (hW : Testing.Ringing K f W) (bill : Cosmos Z K W f r E) (atlas_ : ∀ x∈l, atlas B N T d χ r (Q x) X (a x) (τ x))
    (hq : Honors B N m p l H δ b Q) (hC : Curve (B.a.budget (m+1)) Q l) (hQ : ∀ x∈l, Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta∈band B.a (m+1)) :
    let F := result B N Q X a
    Curve (B.a.budget m) F l ∧ ∀ x∈l, let u := (F x).beta - predictor B N Q x
      licensed B N T d χ r (Q x) ∧ B.Move N m p (F x) (Q x) ∧
        |u| ≤ UVNext.CouplingReset.width B.a m q ∧ (B.a.budget m).threshold^2 * |u| ≤ H x ∧ (F x).v = vac (a x) (τ x) := by
  intro F
  obtain ⟨V,hv⟩ := usable B hP hm.le p
  obtain ⟨h',hr⟩ := grants B N T d χ r hW bill hm hQ atlas_ hx hb.early
  obtain ⟨z,hz,hM⟩ := UVNext.CouplingReset.advance hP hm hv (earns g hm hb hx hc hv hr) (remainders g hm hb hx h' hc hP hv hq hr hQ)
    hC (fun x he => (hQ x he).1)
  let A := board B N (ledger B N m p X a); let Δ x := Averaging.delta (X.read (a x)); let G' := A.install (target Q) (predictor B N Q) z
  have hall x (h : x∈l) : F x = G' x ∧ z x = Δ x := by
    have hleg : 0 < A.leg V := by
      have := (hP m).1.1; have := (B.a.budget m).threshold_pos; have := sites_pos (B.a.S.side m p)
      exact lt_of_lt_of_le (by positivity) hv.2
    have hL : (A.trial (predictor B N Q) x (z x) (UVNext.CouplingReset.scalar (target Q) x)).eval = target Q x := (hM x h).1.ident
    have hr := (yield_shape g hm hb hx h' hv h (z x)).symm.trans (sub_eq_zero.mpr (A.contrast_eq ((records g hm hb hx h (z x)).1.regular.at_flat)
      hv.1 (congr_fun hL 1) (congr_fun hL V)).symm)
    have he : z x = Δ x := eq_of_sub_eq_zero (mul_eq_zero.mp hr |>.resolve_right hleg.ne')
    exact ⟨(congrArg (fun d => A.trial _ x d _) he).symm,he⟩
  refine ⟨{ hz with beta := hz.beta.congr fun x h => congrArg Rep.beta (hall x h).1 },fun x h => ?_⟩
  have he : (F x).beta - predictor B N Q x = Δ x := by change predictor B N Q x + Δ x - predictor B N Q x = _; ring
  dsimp only []; rw [he]
  exact ⟨(earnings B N T d χ r hW bill hm _ (hQ x h).1 (hQ x h).2).2.1,(hall x h).1 ▸ (hM x h).1,(hall x h).2 ▸ (hM x h).2,
    delta_bound g (hx x h).projects,(settled g hm hb hx h' h).2⟩
end YM.AnalyticBridge.VerifiedReset.Return
