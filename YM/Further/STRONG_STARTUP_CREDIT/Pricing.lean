import YM.Extra.MULTISOURCE_BOUNDS.SystemPrices
import YM.Extra.WILSON_STARTUP.ForMix
import YM.Further.STRONG_STARTUP_CREDIT.Sleeves


set_option warningAsError false

/-!
# Joint quotes for the top; compatibility with Prepared

Amounts HERE sufficient for the startup asks. Other asks still
need numerical and physical work. S is a provisional PRE-L stage and
scheduling recipe; floorL bump keeps all its previous floors. Necessary
other lower bounds must be included before locking it.

Use ANY markers reserve δ at each stage. Includes a FIRST push
bond-observation estimate (use r=0 if not needed: then still prices on
projected support) without any assumption about later raw terms.
`factorial` is for commissioning with the current Multi bounds; not needed
for startup quotes alone. Quotes in launcher are in currencies also
available from `Builder.ingredients`' horizon repricing. No invoking
B on a built schedule and coming back to issue these quotes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.StrongStartup
open Filter Function Lattice Wilson RG RG.Supply Source WilsonStartup Precision Pressure
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Sheet G} {D : Rolls C} {Z : Protection D} {V : Supply.Delays Z}
    {Y : Bar V} {I : Wait Y} {F : Labels.Frames G}

structure Tariffs where
  extra : ℕ → ℝ
  nonnegative i : 0≤ extra i
  rim : ℕ → ℕ

/-- Certified per smoothing index, no length/period/horizon/ancestry
inputs needed. Includes the original funds and (separate) Extras for
WILSON_STARTUP.ForMix. -/
structure Prices (C : Sheet G) (T : Tariffs) (L : Extra.Multi.Sections F) (b : ℕ → ℝ) : Prop where
  ready : Timing.funded F L C b
  mixture : Mixture.funded C b
  stronger (j : ℕ) : j ≥ C.first → ∀ x : ℝ, b j ≤ x → ∀ A : Levels G, ∀ N,
    A.params N=C.profile j → A.clock.hatBeta N=x →
      Escrow A N (T.extra j) (T.nonnegative j) ∧ (A.clock.kernel=C.kernel → BondFuel A N (T.rim j))

theorem before (C : Sheet G) (T : Tariffs) (L : Extra.Multi.Sections F) (hC : ∀ j ≥ C.first,(C.profile j).clip.direct ≤ 1) :
    ∃ b : ℕ → ℝ, ∀ b' : ℕ → ℝ, b ≤ b' → Prices C T L b' := by
  have he (i) : ∀ᶠ x : ℝ in atTop, ∀ A : Levels G, ∀ N,
      C.first ≤ i → A.params N = C.profile i → A.clock.hatBeta N = x →
      (Start.Allows A N ∧ ∀ d ≤ i, Mark.Ready A (L d) N) ∧ Mixture.Extras A N ∧
       Escrow A N (T.extra i) (T.nonnegative i) ∧ (A.clock.kernel=C.kernel → BondFuel A N (T.rim i)) := by
    by_cases hi : C.first ≤ i
    · have ht := eventually_all.mpr fun d : Fin (i+1) => Mark.attain (L d.val)
      filter_upwards [ht,preReserve G (C.profile i) _ (T.nonnegative i) (hC i hi),
        sleeves (T.rim i) C.kernel G, Mixture.afford G (C.profile i)] with x hx he hp hq A N _ hA hN
      have he' := he A N hA hN
      exact ⟨⟨he'.old,fun d hv => hx (⟨d,Nat.lt_succ_of_le hv⟩:Fin (i+1)) A N hN⟩,hq A N hA hN,he',fun hg => hp A N hg hN⟩
    exact Eventually.of_forall fun _ _ _ hx => False.elim (hi hx)
  choose b hb using fun i => eventually_atTop.mp (he i)
  refine ⟨b,fun b' hb' => ?_⟩
  exact ⟨fun j hj x hx A N ha hn => (hb _ x ((hb' j).trans hx) A N hj ha hn).1,
    fun j hj x hx A N ha hn => (hb _ x ((hb' j).trans hx) A N hj ha hn).2.1,
    fun j hj x hx A N ha hn => (hb _ x ((hb' j).trans hx) A N hj ha hn).2.2⟩

/-- Consume for all levels including the zeroth; no N→∞ result needed. -/
theorem spending (hG : G.Simple) {A : Levels G} (ha : Paid I A) {T : Tariffs} {L : Extra.Multi.Sections F}
    (h : Prices C T L V.betaEntry) (N : ℕ) :
    let i := A.clock.J N
    Escrow A N (T.extra i) (T.nonnegative i) ∧ BondFuel A N (T.rim i) := by
  intro i
  have hs := ha.firstZero ▸ A.fits.mono (Nat.zero_le N)
  have hp : A.params N=C.profile i := congr_fun ha.stage _
  have he : V.betaEntry (A.clock.J N) ≤ A.clock.hatBeta N := by
    cases N with
    | zero => simpa only [Calendar.hatBeta,Schedule.scale_zero,mul_zero, add_zero,ha.firstZero,ha.bar] using Y.ready
    | succ j => exact (ha.pays j).trans (Timing.hat_mono A (Gauge.slopeConstant_pos hG).le j.le_succ)
  obtain ⟨hq,hs⟩ := h.stronger i hs _ he A N hp rfl
  exact ⟨hq,hs ha.kernel⟩

/-- All these startup estimates work with the actual delays issuing
`Multi.Prepared` for this Scope and Sections and `Pressure.Ringing` for K.
Preparation doesn't already buy physical one-step costs! Grows
both the beta and scale entries monotonically from a supplied record
so other commitments can still be inserted if honestly priced.
-/
theorem prices (C : Sheet G) (K : MapPrices) (s : Extra.Multi.Scope) (T : Tariffs) (L : Extra.Multi.Sections F)
    (hG : G.Simple) (hC : ∀ j ≥ C.first,(C.profile j).clip.direct ≤ 1)
    (hP : ∀ j : ℕ, ((C.profile j).order.factorial:ℝ) ≤ (C.profile j).columns) :
    ∃ f₀ : ℕ → ℕ, ∃ b : ℕ → ℝ, C.floorL ≤ f₀ ∧
      ∀ (f : ℕ→ℕ), f₀ ≤ f → (∀ b', b ≤ b' → Prices {C with floorL:=f} T L b') ∧
      ∀ D : Rolls {C with floorL:=f}, ∀ t : Extra.Multi.Tariff,
      ∀ m ≥ (0:ℝ), ∀ Θ : Supply.Protection D, ∀ V : Supply.Delays Θ, ∃ W : Supply.Delays Θ,
        W.shells=V.shells ∧ W.growth=V.growth ∧ V.scaleEntry ≤ W.scaleEntry ∧ V.betaEntry ≤ W.betaEntry ∧ b ≤ W.betaEntry ∧
          ∃ U : ℕ → ℕ → ℝ, Testing.Ringing K U W ∧ (∀ i j,U i j ≥ m) ∧
          ∀ (Y : Supply.Bar W) (I : Wait Y) (a : Levels G), Paid I a → Extra.Multi.Prepared s t L a := by
  obtain ⟨b,hb⟩ := before C T L hC
  obtain ⟨v,hv⟩ := Extra.Multi.pricing s L hG C K hP
  refine ⟨fun i => max (C.floorL i) (v i),b,(fun _ => le_max_left ..),fun f hf => ?_⟩
  constructor
  · intro b' he
    have hx := hb b' he
    exact ⟨hx.ready,hx.mixture,hx.stronger⟩
  intro D t m hm Θ V
  let W : Supply.Delays Θ := { V with betaEntry := fun i => max (V.betaEntry i) (b i) }
  obtain ⟨W',h1,h2,h3,h4,h5⟩ := hv f (fun i => (le_max_right ..).trans (hf i)) D t m hm Θ W
  exact ⟨W',h1,h2,h3,(fun i => (le_max_left ..).trans (h4 i)),fun i => (le_max_right ..).trans (h4 i),h5⟩

/-- Buying Suitable and factor budget ex ante together, not after
asking threshold predicates or building `Levels`. The modified
profile is before all downstream uses; nothing asserts a Kin price or
that a prior family automatically adapts. -/
theorem shelves (C : Sheet G) (hC : ∀ j ≥ C.first,(C.profile j).clip.direct ≤ 1) :
    ∃ a c : ℕ→ℝ, ∀ A : Sheet G, A.first=C.first →
      (∀ i : ℕ,(A.profile i).clip=(C.profile i).clip ∧ (A.profile i).width=(C.profile i).width ∧
        (A.profile i).order=(C.profile i).order ∧ a i ≤ (A.profile i).paths ∧ c i ≤ (A.profile i).columns) →
      (∀ i ≥ A.first, WilsonStartup.Design.Suitable G (A.profile i)) ∧
      (∀ i : ℕ, ((A.profile i).order.factorial:ℝ) ≤ (A.profile i).columns) := by
  have h i : ∃ q : ℝ, ∀ P : Stage, C.first ≤ i → P.clip=(C.profile i).clip → P.width=(C.profile i).width →
      q ≤ P.paths → WilsonStartup.Design.Suitable G P := by
    by_cases hh : C.first ≤ i
    · obtain ⟨v,-,hv⟩ := Design.readiness G (p:=C.profile i) (hC i hh)
      exact ⟨v,fun P _ => hv P⟩
    exact ⟨1,fun _ h => False.elim (hh h)⟩
  choose v hv using h
  refine ⟨v,fun i => ((C.profile i).order.factorial:ℝ),fun A ha hP => ⟨?_,?_⟩⟩
  · exact fun i hi => hv i _ (ha ▸ hi) (hP i).1 (hP i).2.1 (hP i).2.2.2.1
  intro i; rw [(hP i).2.2.1]; exact (hP i).2.2.2.2

lemma buy_shelves (C : Sheet G) (a c : ℕ → ℝ) : ∃ A : Sheet G, A.first=C.first ∧ A.kernel=C.kernel ∧ A.floorL=C.floorL ∧
    (∀ i : ℕ,(A.profile i).clip=(C.profile i).clip ∧ (A.profile i).width=(C.profile i).width ∧
      (A.profile i).order=(C.profile i).order ∧ a i ≤ (A.profile i).paths ∧ c i ≤ (A.profile i).columns) ∧
    (∀ i : ℕ, (A.profile i).power=(C.profile i).power ∧ (A.profile i).supportExponent=(C.profile i).supportExponent ∧
      (A.profile i).drift=(C.profile i).drift ∧ (C.profile i).columns ≤ (A.profile i).columns ∧
      (C.profile i).paths ≤ (A.profile i).paths) := by
  let f (i : ℕ) : Stage := { C.profile i with
    columns := max (c i) (C.profile i).columns
    paths := max (a i) (C.profile i).paths
    columns_ge := (C.profile i).columns_ge.trans (le_max_right ..)
    paths_pos := (C.profile i).paths_pos.trans_le (le_max_right ..) }
  exact ⟨{ C with profile:=f },rfl,rfl,rfl,fun _ => ⟨rfl,rfl,rfl,le_max_left ..,le_max_left ..⟩,
    fun _ => ⟨rfl,rfl,rfl,le_max_right ..,le_max_right ..⟩⟩

end YM.Further.StrongStartup
