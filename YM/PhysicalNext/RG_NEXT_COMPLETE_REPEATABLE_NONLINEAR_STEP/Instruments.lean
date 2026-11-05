import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Wall
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rent
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Home


/-! Joint early and late choices for E6 rents and Heir principal expenses.
**Same** chart/coupling/Françoise/sector width, no gratuitous choice of a separate
trajectory for ancestor marks. `budgets` buys these from one pre-L plan,
with window size r for the `Script` ports. Remembers reserve orders on BOTH E6
and Psalm. `Wishes` can be required using the actual compatible supports;
`Base` receipt doesn't ship a per-branch support supplier.

This ports Psalm.Solo.home ordering to the chosen Sheet (using its pricing
subingredients, not changing P.lower or hoping its `P.frozen` equals ours).
Only needs its Cadence+Sustained side, to apply thereto even during an authorized
trajectory, not seeking or asserting the other direction of `Allowed`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {D : Rolls s} {v w : Return.Wages} {a : ℕ→ℝ}
    {C : Programs s} {L : Targets s K} {E : Expenses L} {Z : ChartRatio G} {bt : Baton G} {p t : Return.Wages} {r : ℕ→ℕ→ℕ}
    {P : Protection D} {u : ℕ→ℕ} {B : ℕ→ℕ→Cafe}

structure Base (s : Sheet G) (K : MapPrices) (Z : ChartRatio G) (C : Programs s) (v t : Return.Wages)
    (r : ℕ → ℕ → ℕ) {L : Targets s K} (E : Expenses L) : Prop where
  paid : Earlier s K C v (Solo.raise t) r
  first : Psalm.Refit.First s K Z
  floors : Planning.PreBrace s K L E s.floorL

-- t for support costs; epsilon for WEAK pre-log r prices; increase if needed pre-L
lemma budgets (s : Sheet G) (K : MapPrices) (hZ : LocalRatio Z)
    (r : ℕ→ℕ→ℕ) (t ε : Return.Wages) (Y : ℕ) (ht : ∀ j i,0≤t j i) (he : ∀ j i,-(1/2:ℝ)<ε j i ∧ ε j i<0)
    (l : ℕ) (hl : 500≤l) :
    ∃ (f : ℕ→ℕ) (C : Programs s) (v : Return.Wages) (L : Targets s K) (E : Expenses L), s.floorL≤f ∧
      (∀ j i,(L j i).table=Z ∧ (L j i).halo=l ∧ (E j i).earn=t j i ∧ (E j i).wanting=ε j i ∧ (E j i).degrees=Y) ∧
      ∀ g, f≤g → Base {s with floorL:=g} K Z C v t r E := by
  obtain ⟨b,hb,hx⟩ := Psalm.Refit.first s K hZ
  obtain ⟨f,C,v,hf,hE⟩ := earlier s K r (Solo.raise t) (fun i j=> add_nonneg (ht ..) zero_le_two)
  choose L E hL hQ hC hP hT using fun j i=> aim_budget hZ (Testing.query s K j i) _ _ Y l hl (ht j i) (he j i).1 (he j i).2
  obtain ⟨x,-,he,H⟩ := Planning.sponsors s K L E
  refine ⟨max b (max f x),C,v,L,E,hb.trans (le_sup_left),fun j i=>⟨hL j i,hT j i,hC j i,hP j i,hQ j i⟩,fun g hl => ?_⟩
  have hb : b ≤ g := (le_sup_left (b:=f ⊔ x)).trans hl
  have hf : f⊔x ≤ g := (le_sup_right (a:=b)).trans hl
  have hG : x≤g := (le_sup_right (a:=f)).trans hf
  exact ⟨hE _ ((le_sup_left (b:=x)).trans hf),hx _ hb,
    (fun j i he Y hL=> H.1 j i he Y ((hG j).trans hL)),fun j i he Y hL=> H.2 j i he Y ((hG j).trans hL)⟩

structure Concert (D : Rolls s) (w : Return.Wages) (C : Programs s) (K : MapPrices) (Z : ChartRatio G) (B : ℕ→ℕ→Cafe) (bt : Baton G) : Prop where
  fits : Psalm.Refit.requestW D C bt ≤ w
  cost j i : StepStages j i → s.first ≤ i → 2*storeCost (C j i) ≤ (B j i).r ∧ Outlet (B j i) (Testing.query s K j i) (D.L j) (w j i) Z

lemma Base.width (h : Base s K Z C v t r E) (D : Rolls s) (bt : Baton G) : ∃ f : Return.Wages, ∀ w : Return.Wages, f ≤ w →
    ∃ K' : ℕ→ℝ, Nonempty (Register D E w K') ∧ ∃ B : ℕ→ℕ→Cafe, Concert D w C K Z B bt := by
  obtain ⟨x,hx⟩ := Psalm.Refit.widths (D:=D) C bt h.first
  obtain ⟨y,-,hy⟩ := Planning.waits s K L E D h.floors.1 (fun i=>(D.large i).need)
  let m : Return.Wages := fun j i=> max (x j i) (y j)
  refine ⟨m,fun w he=>?_⟩
  obtain ⟨v,-,-,hV⟩ := hy w fun j i _ => (le_max_right ..).trans (he j i)
  obtain ⟨B,hx,hL⟩ := hx w (fun j i=> (le_max_left ..).trans (he j i))
  exact ⟨v,hV,B,hx,hL⟩

-- identical W, chosen χ retained (adapt only shrinks θ). Applications can
-- take a fixed canonical chi for both families.
lemma Concert.endures (h : Concert D w C K Z B bt) (he : Earlier s K C v (Solo.raise t) r)
    (hZ : LocalRatio Z) (cap : ℕ → ℕ → ℝ) (hc : ∀ j i,0<cap j i) : ∃ p : ℕ→ℕ→JointLoad.Heir.Record,
    (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ cap j i) ∧
    ∀ (Q : ℕ → ℕ → Clockwork.Menu) (U : Delays P), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→Folio.Aux,
      ∃ X : Delays P, OrderedDelays X ∧ DelayLe U X ∧
      ∀ W, DelayLe X W → Psalm.Stage.Cadence Z K W b (Solo.guardMenu Q p) w B C bt p v (Solo.raise t) r J ∧ Solo.Sustained W v := by
  obtain ⟨p,hp,h'⟩ := later D he cap hc
  refine ⟨p,hp,fun Q U => ?_⟩
  let A := Solo.guardMenu Q p
  obtain ⟨V,hV,-,hv⟩ := Solo.sustain U he
  obtain ⟨W,hW,-,hw⟩ := h' _ V
  obtain ⟨Y,hY,-,hy⟩ := Psalm.Stage.prelude (d:=p) (F:=B) (m:=A) W h.fits (fun j i hj hi=> (h.cost j i hj hi).1)
  obtain ⟨b,L,-,hL,hl⟩ := Clockwork.book (w:=w) (K:=K) (b:=B) hZ (fun j i hj hi=> (h.cost j i hj hi).2) A Y
  refine ⟨b,fun J =>?_⟩
  obtain ⟨X,hQ,hX,hx⟩ := Folio.season (Z:=Z) (K:=K) (h:=B) (C:=b) (t:=A) J L
  have hs := hW.trans (hY.trans (hL.trans hX))
  exact ⟨X,hQ,hV.trans hs, fun M hM=> ⟨⟨he,(hl M (hX.trans hM)).1,hw M (hY.trans (hL.trans (hX.trans hM))),hx M hM,
    hy M (hL.trans (hX.trans hM)),fun _ _=> min_le_right ..⟩,hv M (hs.trans hM)⟩⟩
end YM.PhysicalNext.Repeat
