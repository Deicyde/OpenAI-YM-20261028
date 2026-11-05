import YM.FullVolume.Luna.Berries
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.Source Planned.GuardedAtom Labels MergeProof MergeProof.Matric Extra.Histories Guard Jams
/-! Width and amount purchases. α limbs.W.Delay after any. `d≤` permits ANY observed weight before. -/
open Next.Scheduling.Clock Instrument
variable {G:Gauge}{P:Teller G} (Q:ConnectedActivityE6.Target G P){p v b t q:ℝ}
open Mallow --
open Daisy Lotus Height Blush Graces
variable {L:Side} (T:Tableau q 300)
lemma overheadG (hp:0<p)(hv:0<v)(s:ℝ)(hs:0<s):∀ᶠ x in atTop,∀ (S:Side)(A:Rep G S)(c:Leaf A), let Ω:= jewelDebt c (stella Q) L x
    (T.liftT (fire G L x/2)) * (p*Ω*pottery G L x) ≤ v*A.p.mass c.crest c.weight ∧ (Blush.glyph x)⁻¹*(p*Ω*straw s L G x) ≤ v*A.p.mass c.crest c.weight:=by
   let β':= stella Q; have hr : Rate G L (-β'.rate) (fun x=>(β'.goal L x)⁻¹):= Rate.congr Rate.power ((Delay.shift_pos G L).mono (fun x hx=> (Real.rpow_neg hx.le _).symm)); let B(x):=fire G L x/2
   have ht : Rate G L (-(1/256)) (fun x=> q/(B x)):=by
      refine Rate.congr ((Rate.power (a:=-(1/256))).mul_left (2*q)) ((Delay.shift_pos G L).mono ?_); intro x hx; dsimp only;rw [Real.rpow_neg hx.le];unfold B fire; ring
   have h:= (((ht.pow 301).mul_left (1+T.price)).mul (hr.mul_left p)).mul (Rate.power (a:=-(3/8))); have h' := (hr.mul (efferv (G:=G) hs (β'.rate-1))).mul_left p
   filter_upwards [h.below (by dsimp only [β',stella];norm_num) _ hv,h'.below (by linarith) _ hv,Delay.shift_pos G L] with x hx hy hz S A c Ω
   let m:= A.p.mass c.crest c.weight; let e:=m*Real.exp (-β'.ε*coverNumber A.p.B c.crest); let g:=β'.goal L x; let d:=Delay.fineMonitor G L
   have hf:0≤ m:= c.profit.trans (A.p.loMass _ _ c.profit)
   have he:e≤ m:=mul_le_of_le_one_right hf (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr β'.usable.le) (by positivity)))
   have hu:0≤e:=mul_nonneg hf (Real.exp_pos _).le; let f1:= T.liftT (B x)
   constructor
   · change f1*(p*(e/g)*pottery G L x)≤ _; rw [show f1*(p*(e/g)*_)= (f1*(p*g⁻¹)*pottery G L x)*e from by rw [div_eq_mul_inv]; ring]; exact mul_le_mul ((le_abs_self _).trans hx) he hu hv.le
   change (Blush.glyph x)⁻¹* (p*(e/g)*straw s L G x) ≤ _; rw [show (Blush.glyph x)⁻¹*_= (p*(g⁻¹*((Blush.glyph x)⁻¹*straw s L G x)))*e from by rw [div_eq_mul_inv]; ring];exact mul_le_mul ((le_abs_self _).trans hy) he hu hv.le
open RG.Supply UVNext.CouplingReset Testing Push.PriceCompiler
open Bid
variable {s:Supply.Sheet G}{D:Rolls s}{A: Protection D}{K: MapPrices}{R:Targets s K}{V:Expenses R}{w:ℕ→ℕ→ℝ}{l:ℕ→ℝ}(W:Register D V w l)
-- flexible; choose slack arbitrarily postL.E.R. Reused at J.Stage import.Pés input coda
abbrev saleE (v:ℝ)(j i d:ℕ)(x:ℝ) (Q:ConnectedActivityE6.Target G P) (c:ℝ) (A:RG.Stage) (T:Tableau q 300)(μ:ℝ) (G': Gauge) (L:Side) :=∀ (n:Side)(R:Rep G n)(C:Lotus.Leaf R),
    let p:ℝ := 2*(L.val:ℝ)^d; let Ω := jewelDebt C (stella Q) L x; let B:= fire G L x/2
    T.liftT B*(p*Ω*pottery G L x) ≤ v*R.p.mass C.crest C.weight ∧ (Blush.glyph x)⁻¹* (p*Ω*straw μ L G x)≤ v*R.p.mass C.crest C.weight
def Spire (a: ℕ→ℕ→ℕ→ℝ)(D':Delays A):Prop:= ∀ j i, StepStages j i → ∀ d≤ i,∀ x,D'.betaEntry j ≤ x → saleE (a j i d) j i d x (R j i) 0 (s.profile j) T (W.μ j i) G (D.L j)
lemma ernes (a:ℕ→ℕ→ℕ→ℝ)(h:∀ j i,StepStages j i→∀ d≤ i,0<a j i d)(D':Delays A) : ∃ X:Delays A,DelayLe D' X ∧ ∀ Y:Delays A, DelayLe X Y → Spire T W a Y:=by
    obtain ⟨x,-,hb,hx⟩:= collect_upper D'.betaEntry (fun j (x:ℝ)=>∀ i,StepStages j i →∀ d∈ Finset.range (i+1),saleE (a j i d) j i d x (R j i) 0 (s.profile j) T (W.μ j i) G (D.L j)) (fun j=> eventually_transitions j _ _ (fun i hi=> (Finset.eventually_all _).2 (fun d hd=> overheadG _ T (mul_pos zero_lt_two (pow_pos (Nat.cast_pos.mpr (D.L j).property) d)) (h j i hi d (Nat.le_of_lt_succ (mem_range.mp hd))) _ (W.consumes j i hi|>.2.1))))
    exact ⟨{D' with betaEntry:=x},⟨hb,le_rfl,le_rfl,le_rfl⟩,fun Y hv j i he k hk X h=> hx j X ((hv.beta _).trans h) i he k (mem_range.mpr (by omega))⟩
end YM.PhysicalNext.Repeat.Luna
