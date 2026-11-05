import YM.AnalyticBridge.VERIFIED_RESET_STEP.Inputs
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Opening
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Marina


/-!
# Post-L rate selection for compulsory E6 emissions

Renewal to `Move.forced` needs a rate proportional to $p^2$, not $p^δ$,
δ<2. Read back from the integrated excursion estimate **before** passing
to the smaller exponent in `dictionary_fit` and `Statement.postmerge`.
`Pocket` chooses post-L rates as small as required, after µ (itself after
ratio and width). Buys against the *actual β*, labels of all sizes and any
period. Supplied α and Profiles still paired to the same Transition caller
later on. More horizontal growth and exponent-Hit reserves are paid
separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision Next.Scheduling Next.SectorChange
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {K : MapPrices}

abbrev Targets (s : Sheet G) (K : MapPrices) := ∀ j i, ConnectedActivityE6.Target G (Testing.query s K j i)
abbrev Expenses {s : Sheet G} {K : MapPrices} (C : Targets s K) := ∀ j i, ConnectedActivityE6.Target.Expense (C j i)
abbrev Register {s : Sheet G} {K : MapPrices} {C : Targets s K} (D : Rolls s) (L : Expenses C) (v : Return.Wages) (A : ℕ→ℝ) :=
    Planning.Purchase s K C L D v A

-- keep same in/out calendar, even in a plateau. `hC` buys stronger mark
-- **before** giving the supported comparison proof. Factor c permits additional
-- attachment passes without attempting to pay K twice.
lemma eventual_resize (Pt : Teller G) (Q : ConnectedActivityE6.Target G Pt) (L : Side) (μ : ℝ) (hμ : 0<μ)
    (j : ℕ) (F : Postage) (A : Time.Forecast F) (hA : A.hard ≤ μ/16) (c : ℝ) (hc : 0<c) :
    ∀ᶠ x : ℝ in atTop, ∀ β : ℝ, Next.Scheduling.inBand (betaF G x L) β →
      Cash.armK Q L μ x 0 j ≤ c*A.pair.strong (betaF G x L) β := by
  have hF := A.surplus
  have hr : 0<A.hard := F.pos.trans hF
  have h := (Q.tempo L hμ j).below Q.stop (c/2) (by positivity)
  filter_upwards [Delay.shift_pos G L,h] with x hx hv β hb
  let y:=betaF G x L
  have hy : Clock.gap y / 2 ≤ Clock.gap β := (band_gap y β hx hb).1
  have hg : 0 < Clock.gap y := Clock.gp hx
  have hβ : 0 < Clock.gap β := lt_of_lt_of_le (half_pos hg) hy
  let p := Instrument.plain.P y
  let t := Instrument.plain.t y / Clock.gap β
  have hp : 0 < p := Clock.wp _ _
  have ht : 0 ≤ t := div_nonneg (mul_pos hg hp).le hβ.le
  have he : p = Delay.fineMonitor G L x := Clock.watch_two _
  have ht' : t ≤ 2*p := (div_le_iff₀ hβ).mpr (by change Clock.gap y*p ≤ 2*p*_; nlinarith only [hy,hp])
  let u := Q.mark L μ x
  have hu : u= μ/4*p^2 := by rw [he]; unfold u; change μ/2*(1/2)*Delay.fineMonitor G L x^2 = μ/4*_; ring
  have hrate : -u ≤ -A.hard*t^2 := by
    rw [hu]; nlinarith only [mul_le_mul_of_nonneg_left (sq_le_sq₀ ht (ht.trans ht')|>.2 ht') hr.le,
      mul_le_mul_of_nonneg_right hA (sq_nonneg (2*p))]
  let E := Q.mergeScale L μ x j
  have hE : E*(1-1/2:ℝ)⁻¹ ≤ c := by
    change |E| ≤ _ at hv
    norm_num
    linarith [le_abs_self E]
  unfold Cash.armK Time.Forecast.pair Progress.DirectedRecipe.Payments.Pairing.strong
  dsimp only
  calc
    _ = E*(1-1/2:ℝ)⁻¹*Real.exp (-u) := by rw [pow_zero,inv_one,one_mul,mul_comm]
    _ ≤ c * Real.exp (-u) := mul_le_mul_of_nonneg_right hE (Real.exp_nonneg _)
    _ ≤ c * (max 1 A.coeff * Real.exp (-A.hard*t^(2:ℕ))) := mul_le_mul_of_nonneg_left
      ((Real.exp_monotone hrate).trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left ..))) hc.le

structure Pocket {s : Sheet G} {K : MapPrices} {C : Targets s K} {D : Rolls s} {E : Expenses C} {v : Return.Wages} {a : ℕ→ℝ}
    (R : Register D E v a) {F : ℕ→ℕ→Postage} (A : Time.Scouts (F:=F)) : Prop where
  price j i (h : StepStages j i) : (A j i).hard ≤ R.μ j i/32

/-- Pocket after payment on both transitions and θ-independent. Keep μ not
from a different aperture. -/
lemma pockets {C : Targets s K} {E : Expenses C} {v : Return.Wages} {a : ℕ→ℝ} (R : Register D E v a)
    (H : ℕ→ℕ→Postage) : ∃ (F : ℕ→ℕ→Postage) (A : Time.Scouts (F:=F)),
      (∀ j i, (F j i).rate ≤ (H j i).rate) ∧ Pocket R A := by
  have hh (j i : ℕ) : ∃ f : Postage,∃ b : Time.Forecast f, f.rate ≤ (H j i).rate ∧ (StepStages j i → b.hard ≤ R.μ j i/32) := by
    by_cases he : StepStages j i
    · have ha : 0 < R.μ j i := (R.consumes j i he).2.1
      let f : Postage := {H j i with rate := min (H j i).rate (R.μ j i/64), pos := lt_min (H j i).pos (by positivity)}
      have hb : f.rate ≤ R.μ j i/64 := min_le_right ..
      exact ⟨f, ⟨1,one_pos,R.μ j i/32,by linarith only [ha,hb]⟩, min_le_left .., fun _ => le_rfl⟩
    refine ⟨H j i,⟨1,one_pos,(H j i).rate+1,lt_add_one _⟩,le_rfl,fun hj => False.elim (he hj)⟩
  choose F A hV hQ using hh; exact ⟨F,A,hV,⟨hQ⟩⟩

structure Receiving {s : Sheet G} {K : MapPrices} {D : Rolls s} {C : Targets s K} {E : Expenses C} {v : Return.Wages} {a : ℕ→ℝ}
    (R : Register D E v a) {F : ℕ→ℕ→Postage} (A : Time.Scouts (F:=F)) {P : Protection D} (W : Delays P) (c : ℝ) : Prop where
  grow : Planning.Permits R W.betaEntry (fun _ i => (s.profile i).order) (fun _ i=> (s.profile i).power) Chi.canonical
  earns j i (h : StepStages j i) x (h : W.betaEntry j ≤ x) (β : ℝ) (hb : Next.Scheduling.inBand (betaF G x (D.L j)) β) : Cash.armK (C j i) (D.L j) (R.μ j i) x 0 (E j i).degrees ≤
    c*(A j i).pair.strong (betaF G x (D.L j)) β

lemma Pocket.booked {C : Targets s K} {E : Expenses C} {v : Return.Wages} {a : ℕ→ℝ} {R : Register D E v a} {F} {A : Time.Scouts (F:=F)} (h : Pocket R A)
    {u : ℕ→ℕ} (he : Planning.PreBrace s K C E u) (hq : ∀ i,u i ≤ (D.L i).val)
    {P : Protection D} (U : Delays P) {c : ℝ} (hc : 0<c) : ∃ W : Delays P, DelayLe U W ∧ ∀ V : Delays P, DelayLe W V → Receiving R A V c := by
  obtain ⟨m,-,hR,hS⟩ := Planning.awaits he hq R (fun _ i=> (s.profile i).order) (fun _ i=> (s.profile i).power) Chi.canonical
  let B : Delays P := {U with betaEntry := fun i => max (m i) (U.betaEntry i)}
  obtain ⟨W,hW,-,hw⟩ := delay_extra B _ (fun _ _ _=> True) (fun j=> eventually_transitions j _ _ (fun i (hi:StepStages j i)=> by
    have hp : 0 < R.μ j i := (R.consumes j i hi).2.1
    exact eventual_resize _ (C j i) (D.L j) _ hp (E j i).degrees (F j i) (A j i) ((h.price j i hi).trans (by linarith)) c hc)) (by simp)
  refine ⟨W,DelayLe.trans (V:=B) ⟨fun _=>le_max_right ..,le_rfl,le_rfl,le_rfl⟩ hW,fun V hV=>?_⟩
  have hm : m ≤ V.betaEntry := fun i => (le_max_left ..).trans ((hW.trans hV).beta i)
  exact ⟨⟨le_trans hR hm,fun j i hj x hx => hS j i hj x ((hm _).trans hx)⟩,fun j i hi x hx => (hw V hV).1 j x hx i hi⟩
end YM.PhysicalNext.Repeat
