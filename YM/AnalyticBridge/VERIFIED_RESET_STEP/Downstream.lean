import YM.AnalyticBridge.VERIFIED_RESET_STEP.Advance
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Opening
import YM.Progress.DIRECTED_RECIPE.Bands
import YM.UVNext.COUPLING_RESET.Stability


/-! Consumer for the actual PeriodFuture-style Directed recipe (on any
Sheet with such Kinetic data & prices, not requiring the particular Beam).
Even when repeated arbitrarily within a stage. Retains the early-to-Move
permissions, does not require callers to prove the exact splitting or bill
on the post-template. No assertion that startup and extraction have yet
been realized together or separately! -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Use
open Filter Function Set Lattice Wilson RG Precision Pressure Collection Next.Scheduling UVNext.CouplingReset Progress.DirectedRecipe
open Input Supply Push.PriceCompiler Ovens Shoot Return Next.SectorChange Time
open scoped Topology BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P} {E : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage}
    {q : ResetPrices} {N m p : ℕ} {Q : In B.a m p} {l : Set ℝ} {H w δ γ τ : ℝ → ℝ}

lemma compatible_ingredients {n : Side} {X : Pipes G n} {t : Tap G n} {p : BudgetPoint} {δ w δ' w' : ℝ} (h : Ingredients X t p δ w)
    (hd : δ ≤ δ') (hw : w ≤ w') : Ingredients X t p δ' w' := by
  obtain ⟨κ,b,u,H,h',he⟩ := h.pays
  exact ⟨κ,b,u,{H with stamp := {H.stamp with boundE := E_rises H.stamp.boundE hd}},h',he.trans hw⟩
lemma respects (h : B.bake = recipe B.kin E F (permissions B.a)) (hm : m<N)
    (hv : ∀ x∈l, H x ≤ portion E F B.a m (Q x).beta ∧ δ x ≤ Echarge E F B.a m (Q x).beta ∧ γ x ≤ Kcharge F B.a m (Q x).beta) :
    Honors B N m p l H δ γ Q := by
  intro x he hl hb Δ X t r c R β hI hΔ ht S
  have hf := hl.loads; rw [h] at hf ⊢
  have hQ := hv x he
  have hw : BatchPay B.kin E F (permissions B.a) N m p (Q x) Δ X t := ⟨compatible_ingredients hI hQ.2.1 hQ.2.2,ht,hΔ.trans hQ.1,trivial⟩
  exact ⟨PeriodFuture.struck hm hf hb hw,hm,hb,Δ,X,t,hw,rfl⟩

variable {A : Scouts (F:=F)} {η : ℕ → ℝ} {f r b : Return.Wages}

/-- Numerical/kin/bake clocks, not a pricing fixed point. All these
need to be bought at the indicated B, with choices before their respective
orders. -/
structure Machine (B : Directed G I Z K P) (E : ℕ → ℕ → Exchange) {F : ℕ → ℕ → Postage}
    (A : Scouts (F:=F)) (η : ℕ → ℝ) (q : ResetPrices) (f r b : Return.Wages) : Prop where
  ready : B.bake = recipe B.kin E F (permissions B.a)
  shops : Opened W P A
  coverage j i : StepStages j i → P.g j ≤ (F j i).rate/4 ∧ credit G (s.profile i) ≤ q.cost j i / 4
  cubic : ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → CubicGate D q j i x
  prices : PricedReset B.a η q
  ring : Testing.Ringing K f W
  bill : Cosmos Z K W f r b

namespace Machine
variable (M : Machine B E A η q f r b) (hm : m<N) (hL : ∀ x∈l,Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta ∈ band B.a (m+1))
include M hm hL
lemma passes : let H := fun _ : ℝ => forecastE B.a m; let w x := forecastK B.a m A (Q x).beta
    let δ := fun _ : ℝ => fraction B.a m; let γ x := quoteHard B.a m F (Q x).beta
    Prices B N m p q l H w δ γ ∧ Honors B N m p l H δ γ Q := by
  have ht := M.coverage _ _ (step_paid B.a m)
  obtain ⟨h,hH⟩ := now B hm M.shops ht.1 (params_eq B.valid m ▸ ht.2) E M.cubic (fun x hx => (hL x hx).2)
  exact ⟨h,respects M.ready hm (fun x hx => ⟨(hH x hx).1,(hH x hx).2,quoteHard_le ..⟩)⟩
variable (g : G.Simple) {X : Listing G (B.a.S.side m p)} {v : ℝ → Collection.Source G (B.a.S.side m p)}
    (T : Wood B m p) (d : Bookings B m p f) (χ : Push.SectorMeasure.Chi)
    (ha : ∀ x∈l, atlas B N T d χ r (Q x) X (v x) (τ x))
    (hh : ∀ x∈l, Local X (B.a.budget m) (v x) (forecastE B.a m) (forecastK B.a m A (Q x).beta)) (hr : Compared X (B.a.budget m) v l)
include g T d χ ha hh hr
lemma run (hc : Curve (B.a.budget (m+1)) Q l) : let z := result B N Q X v
    Curve (B.a.budget m) z l ∧ ∀ x∈l, licensed B N T d χ r (Q x) ∧ B.Move N m p (z x) (Q x) ∧
      |(z x).beta - predictor B N Q x| ≤ width B.a m q ∧ (B.a.budget m).threshold^2 * |(z x).beta - predictor B N Q x| ≤ forecastE B.a m ∧
      (z x).v = vac (v x) (τ x) :=
    reset g hm (M.passes hm hL).1 hh hr M.prices T d χ M.ring M.bill ha (M.passes hm hL).2 hc hL

lemma packet {V : Work B m p} (hv : Usable B η N m p V) : Income B N m p q l Q V (ledger B N m p X v) ∧ Remainder B N m p q l Q V (ledger B N m p X v) := by
  obtain ⟨hS,hQ⟩ := M.passes hm hL
  obtain ⟨h,h'⟩ := grants B N T d χ r M.ring M.bill hm hL ha hh hS.early
  exact ⟨earns g hm hS hh hr hv h',remainders g hm hS hh h hr M.prices hv hQ h' hL⟩
end Machine

structure Offering (B : Directed G I Z K P) {F : ℕ → ℕ → Postage} (A : Scouts (F:=F)) (f r : Return.Wages) : Prop where
  holds N m p : m<N → ∀ l u : ℝ,l ≤ u → let s := Icc l u
    ∀ Q : In B.a m p, Curve (B.a.budget (m+1)) Q s → (∀ x∈s,Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta ∈ band B.a (m+1)) →
      ∃ X v, ∃ (τ : ℝ → ℝ) (T : Wood B m p) (d : Bookings B m p f) (χ : Push.SectorMeasure.Chi), (∀ x∈s,atlas B N T d χ r (Q x) X (v x) (τ x)) ∧
      (∀ x∈s, Local X (B.a.budget m) (v x) (forecastE B.a m) (forecastK B.a m A (Q x).beta)) ∧ Compared X (B.a.budget m) v s

abbrev Origins (B : Directed G I Z K P) := ∀ N p, ∃ F, Curve (B.a.budget N) (n:=B.a.S.side N p) F (band B.a N) ∧
      ∀ β∈band B.a N,(F β).beta=β ∧ Lives B.bake N N p (F β) ∧ B.bake.Starter N p (F β)
lemma supplier (g : G.Simple) (M : Machine B E A η q f r b) (hs : Offering B A f r) (hO : Origins B) : Supplier B η q := by
  refine ⟨hO,fun N p m hm l u hlu Q hc hL ⟨V,hV⟩ => ?_⟩
  obtain ⟨X,v,τ,T,d,χ,h,h',H⟩ := hs.holds N m p hm l u hlu Q hc hL
  exact ⟨V,ledger B N m p X v,hV,M.packet hm hL g T d χ h h' H hV⟩
lemma from_menu (h : B.bake = recipe B.kin E F (permissions B.a)) (hM : Progress.DirectedRecipe.Origins B.kin (permissions B.a)) : Origins B := by
  intro N p
  obtain ⟨X,d,H⟩ := hM N p
  refine ⟨fun x => fromTop B.kin N p x X (d x), H.starts, fun x hx => ⟨rfl,?_,h ▸ starter (H.law x hx) hx E F⟩⟩
  rw [h]
  exact ⟨rfl,rfl,rfl,⟨B.support.cap N N le_rfl,(H.law x hx).ingredients.gates ..⟩, PeriodFuture.begin hx (H.law x hx)⟩
end YM.AnalyticBridge.VerifiedReset.Use
