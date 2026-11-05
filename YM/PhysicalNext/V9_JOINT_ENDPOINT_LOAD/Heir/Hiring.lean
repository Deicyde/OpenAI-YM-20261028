import YM.AnalyticBridge.VERIFIED_RESET_STEP.Inherited
import YM.Extra.WEAK_SCALING_ACTLAW.Producer
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Choirs
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Entrance
import YM.Planned.ATOM_REGULAR_ESTIMATE.Bills


/-!
# Joint calendar: before-Wait requests for the principal E station

Wages, support rules and full output reserves aligned *before* one
length is chosen; crossing needs a physical supplier of the same Tower
prices and matching diagrams (e.g.

Wired).

After W and chart radii chosen
and BEFORE Bar/period/operative V etc, thickness for all profiles at each
request, then post-L invoices over both permitted stage transitions.

Not an assertion that all budget/earnings/label hypotheses of
E's interacting recursion have been jointly realized with this schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Suite
open Filter Function Set Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian Push.PriceCompiler Supply Testing AnalyticBridge.LocalGaussianLaws
    AnalyticBridge.VerifiedReset.Time
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {V : Rolls s} {Θ : Protection V} {W : Delays Θ}

abbrev Programs (s : Sheet G) := ℕ → (i : ℕ) → Libretto G (s.profile i).order
variable {C : Programs s} {E t : ℕ → ℕ → ℝ} {r : ℕ → ℕ → ℕ} {D : ℕ → ℕ → Record}

def wide (K : MapPrices) (j i : ℕ) := min (K.α j) (K.α i)
def scale (K : MapPrices) (j i : ℕ) := |K.Ω j| + |K.Ω i|
lemma wide_pos (K : MapPrices) (j i : ℕ) : 0<wide K j i := lt_min (K.alpha_pos j) (K.alpha_pos i)
lemma scale_nn (K : MapPrices) (j i : ℕ) : 0 ≤ scale K j i := by unfold scale; positivity

structure Earlier (s : Sheet G) (K : MapPrices) (C : Programs s) (E t : ℕ → ℕ → ℝ) (r : ℕ → ℕ → ℕ) : Prop where
  agrees (j i) : (C j i).δ = wide K j i ∧ (C j i).N=scale K j i ∧ Release.Quotation (C j i) (s.profile i).power (r j i) (s.profile j).supportExponent (t j i) (E j i)
  matins (j i) {c f : Side} (S : StepData c f) (T : Tube G S) : (query s K j i).Funds S T → ∀ F, Matins T F (s.profile j).power (2*(C j i).C) (C j i).M
  gates (j i) (L : Side) : StepStages j i → s.floorL j ≤ L.val → Release.accepts (r j i) (s.profile j).supportExponent (t j i) L ∧ licensed (C j i).δ (C j i).N L
  pre : Pre s E

theorem earlier (s : Sheet G) (K : MapPrices) (r : ℕ→ℕ→ℕ) (t : ℕ→ℕ→ℝ) (ht : ∀ j i,0≤t j i) :
    ∃ (f : ℕ→ℕ) (C : Programs s) (E : ℕ→ℕ→ℝ), s.floorL ≤ f ∧ ∀ g, f ≤ g → Earlier {s with floorL:=g} K C E t r := by
  choose C hc hn hm using fun j i => leads (query s K j i) (wide K j i) (scale K j i) (wide_pos ..) (scale_nn ..)
  choose E hE using fun j i => Release.quoting (C j i) (s.profile i).power (r j i) (s.profile j).price_pos (ht j i)
  let test j i (L : ℕ) := 20*Release.base (t j i) (r j i) ≤ (L:ℝ)*(s.profile j).supportExponent ∧
    yarn (C j i).δ (C j i).N ≤ (L:ℝ)^2/128 ∧ 8*E j i ≤ credit G (s.profile i)*L
  obtain ⟨f,-,hf,h⟩ := collect_upper s.floorL (fun j L => ∀ i, StepStages j i → test j i L) (fun j => eventually_transitions j _ _ (fun i _ => by
    have hv := tendsto_natCast_atTop_atTop (R:=ℝ)
    filter_upwards [(hv.atTop_mul_const (s.profile j).price_pos).eventually_ge_atTop _,(hv.const_mul_atTop (credit_pos G (s.profile i))).eventually_ge_atTop _, hv.eventually_ge_atTop (128*yarn (C j i).δ (C j i).N),hv.eventually_ge_atTop 1] with L h₁ h₂ h₃ h₄
    exact ⟨h₁,by nlinarith only [h₃,h₄],h₂⟩))
  refine ⟨f,C,E,hf,fun g hg => ⟨fun j i => ⟨hc j i, hn j i, hE j i⟩,hm,fun j i L hi he => ?_,fun j i hi => (h _ _ (hg j) _ hi).2.2⟩⟩
  have he := h _ L.val ((hg j).trans he) _ hi; exact ⟨he.1,he.2.1⟩

structure Offer (K : MapPrices) (V : Rolls s) (C : Programs s) (D : ℕ→ℕ→Record) (r : ℕ→ℕ→ℕ) (j i : ℕ) (x : ℝ) : Prop where
  care (P B : BudgetPoint) : P.threshold=temp x → B.threshold=fiery G x (V.L j) → B.B=radiusB (betaF G x (V.L j)) → P.order=(s.profile i).order → B.order=(s.profile j).order →
      P.power=(s.profile i).power → B.power=(s.profile j).power → (∀ β, betaF G x (V.L j)/2 ≤ β → 0 < coupling β ∧ Lute.Plented (C j i) (D j i) P B (V.L j) (r j i) x (coupling β)) ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.J=j → S.patch.L=V.L j → Seam T (wide K j i) (scale K j i) → Lift.Booth (query s K j i) S T → 100*(1+radiusB x)≤c.val → Plays (C j i) (D j i) P B (query s K j i) T x

def Offers (K : MapPrices) (W : Delays Θ) (C : Programs s) (D : ℕ → ℕ → Record) (r : ℕ → ℕ → ℕ) := ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → s.first ≤ i → Offer K V C D r j i x

def one : Record := ⟨1,one_pos,1,le_rfl,1,one_pos,1,le_rfl,1,le_rfl⟩
theorem later (V : Rolls s) (h : Earlier s K C E t r) (cap : ℕ → ℕ → ℝ) (hc : ∀ j i, 0<cap j i) : ∃ D : ℕ → ℕ → Record,
    (∀ j i, StepStages j i → s.first ≤ i → (D j i).ε ≤ cap j i) ∧ ∀ (Θ : Protection V) (U : Delays Θ), ∃ W : Delays Θ, DelayLe U W ∧ OrderedDelays W ∧ ∀ W', DelayLe W W' → Offers K W' C D r := by
  have H (j i : ℕ) : ∃ D : Record, (StepStages j i → s.first ≤ i → D.ε ≤ cap j i) ∧ ∀ᶠ x in atTop, StepStages j i → s.first ≤ i → Offer K V C (fun _ _ => D) r j i x := by
    by_cases he : StepStages j i ∧ s.first ≤ i
    swap; exact ⟨one,fun a b=>False.elim (he ⟨a,b⟩),Eventually.of_forall fun _ a b => False.elim (he ⟨a,b⟩)⟩
    let Y := Clockwork.patch V he.1 he.2
    obtain ⟨D,hD,-,h'⟩ := songs Y (query s K j i) (C j i) (s.has _) (h.gates _ _ _ he.1 (V.large j).need).2 (s.orders he.1.1) (s.powers he.1.1) (h.matins j i) (r j i) (cap j i) (hc j i)
    refine ⟨D,fun _ _ => hD,h'.mono fun x hx _ _ => ⟨fun P B hv hb he hi hj h₁ h₂ => ?_⟩⟩
    have ha := hx P B hv hb he hi hj h₁ h₂
    refine ⟨ha.1,fun S T hS hL hT => ha.2 S T ?_ (by rwa [(h.agrees j i).1,(h.agrees j i).2.1])⟩
    cases hp : S.patch; rw [hp] at hS hL; unfold Y Clockwork.patch; congr
  choose D hD hh using H
  refine ⟨D,hD,fun Θ U => ?_⟩
  obtain ⟨W,hW,hw,h'⟩ := delay_extra U _ (fun _ _ _ => True) (fun j => eventually_transitions j _ _ fun i hi => (hh j i).mono fun x hx hs => (⟨(hx hi hs).care⟩ : Offer K V C D r j i x)) (by simp)
  exact ⟨W,hW,hw,fun W' hw => (h' W' hw).1⟩
end YM.PhysicalNext.JointLoad.Heir.Suite
