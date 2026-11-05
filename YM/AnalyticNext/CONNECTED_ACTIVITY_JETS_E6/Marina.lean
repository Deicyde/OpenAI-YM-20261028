import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armada
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Bulkhead
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan



/-!
# Priceable deployment of the one-step pre-log integrals

Use AFTER all scoring indexes chosen. Exponent vs β-hat; K already
 prices at many-times *outgoing* forced requirement. Doesn't proceed
 to V History construction. Consumers may preselect periods/any 
 higher floors than these (ensure Direction pays then). For every
 requested stage-budget one Purchase, nondecreasing, retain with direction.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Bid Matter Packets Art Blaze.Scroll Blaze.Vine Blaze.Polar
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {η r q a Y W d C' A b s μ C v B e i: ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
open Blaze Blaze.March Captain PriceCompiler
namespace Target

def earnings (s : ℝ) := Real.exp (-(4:ℝ)*(Vac.Numbers.P s)^((1:ℝ)/5))
def Licenses (X : Expense Q) (L:Side) (W μ c : ℝ) (o : Order G W) (x : ℝ) (j n : ℕ) (χ:Chi) :=
    ∀ (c' f : Side) (S : StepData c' f) (T : Tube G S), Works P L x S T → Stamp T→ ∀ (R:Rep G f) (H:Cash W x μ L Q o c T R),
      ∃ (C' d v t A b r B q i : ℝ) (k : ℕ),
        Nonempty (Captain H j C' d v t A b r B q k χ) ∧ Armada Q L μ X.earn x i B j k ∧
        shiftG x ^ (n*j)* B * Q.overture L μ x (k+n*j) ≤ betaF G x L ^ X.wanting ∧
        collars G i x j n * (salary Q L μ B x j k*(1-1/2)⁻¹) ≤ betaF G x L ^ X.wanting ∧
        Cash.armK Q L μ x 0 X.degrees ≤ earnings x
lemma eventually_robe (Q : Target G P) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Expense Q) (W μ c : ℝ) (o:Order G W), 0<W → 0<μ →
    ∀ j n χ, ∀ᶠ x:ℝ in atTop, Licenses X L W μ c o x j n χ := by
  obtain ⟨m,hm⟩:= entrance P Q; refine ⟨m,fun L hL X W μ c o hW hμ j n χ=> ?_⟩
  by_cases he : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact Eventually.of_forall fun x c f S T h=> (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
  obtain ⟨D,hd,hF,hX⟩:=he; obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:= hm L hL D hd j χ W hW μ hμ o
  have hT : X.earn<Q.exp:= by linarith [X.worth,X.first,X.second]
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price hT j k hB
  have hf := Cash.dictionary_fit Q L X.degrees 0 hμ (show (0:ℝ)≤4 by norm_num) (show (0:ℝ)≤1/5 by norm_num) (by norm_num)
  filter_upwards [H,hq n 0 X.wanting X.reach,hg n 0 X.wanting X.reach,hK,hf] with x h hh hk hA he c f S T hW hx R I
  simp only [pow_zero,mul_one,add_zero] at hk hh
  exact ⟨C,_,_,_,_,_,_,_,_,_,_,h c f S T (hW.patch hF hX) hx R _ I,hA,(le_abs_self _).trans hh,(le_abs_self _).trans hk,he⟩
end Target

open RG.Supply Pressure.Testing
namespace Planning
variable (C : Sheet G) (M : MapPrices) (Q : ∀ j i,YM.ConnectedActivityE6.Target G (query C M j i))
variable (p : ∀ j i,YM.ConnectedActivityE6.Target.Expense (Q j i)) (D : Supply.Rolls C)
open YM.Input Shoot

def PreBrace (x : ℕ→ℕ) := Need C M Q p x ∧ ∀ j i, StepStages j i → ∀ L:Side,x j≤L.val →∀ (W μ c:ℝ) (o: Target.Order G W),
    0<W → 0<μ → ∀ k n χ, ∀ᶠ s:ℝ in atTop, Target.Licenses (p j i) L W μ c o s k n χ
lemma sponsors : ∃ x:ℕ→ℕ, Monotone x ∧ C.floorL≤x ∧ PreBrace C M Q p x := by
  obtain ⟨u,h₁,h,hN⟩:= exists_floors C M Q p; choose m hm using fun j i => Target.eventually_robe (Q j i)
  let g j := max (fromMax m j) (u j); let x:=prefixHi g
  have hu : u ≤ x := fun j=> (le_max_right ..).trans (le_prefixHi g le_rfl)
  refine ⟨x,prefixHi_mono _,h.trans hu,(fun i j hj L hv=> hN i j hj L ((hu _).trans hv)),fun j i he L hp=> hm j i L
    ((le_fromMax m he).trans ((le_max_left ..).trans ((le_prefixHi g le_rfl).trans hp))) _⟩

variable {C M Q p D} {w : ℕ→ℕ→ℝ} {A : ℕ→ℝ}
def Permits (L : Purchase C M Q p D w A) (P : ℕ→ ℝ) (k n : ℕ→ℕ→ℕ) (χ:Chi) := A≤P ∧ ∀ j i,StepStages j i →
    ∀ x:ℝ,P j≤x → Target.Licenses (p j i) (D.L j) (w j i) (L.μ j i) (L.c j i) (L.o j i) x (k j i) (n j i) χ
lemma awaits {x:ℕ→ℕ} (h : PreBrace C M Q p x) (hu : ∀ j,x j≤(D.L j).val) (L : Purchase C M Q p D w A) (k n) (χ:Chi) :
    ∃ P: ℕ→ℝ, Monotone P ∧ Permits L P k n χ := by
  obtain ⟨H,hH,he,hP⟩:= collect_upper A _ fun j=> eventually_transitions j atTop _ (fun i hi=> h.2 j i hi (D.L j) (hu j) _ _
    (L.c j i) (L.o j i) (L.consumes j i hi).1 (L.consumes j i hi).2.1 (k j i) (n j i) χ)
  exact ⟨H,hH,he,fun j i hi x hx=>hP _ _ hx _ hi⟩
end Planning
end YM.ConnectedActivityE6
