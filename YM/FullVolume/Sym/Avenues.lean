import YM.FullVolume.Sym.Fade
import YM.FullVolume.Sym.Glimmer
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
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
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable {P:BudgetPoint}
variable {v δ e b γ B η:ℝ} {n d:ℕ} {C:Tune H v δ}
open Slide Marlin Progress.DirectedRecipe Ovens
section personal
variable {v' σ ρ φ : ℝ} {w:Rung}{p' q': Stars→ℝ}
    {Y:Stars→Side} {r k z : ℕ} (hq:∀ i:Stars,(Y i).val=2*(r+i.val)) (E:sun→∀ i:Stars,Trio.Offer G (Y i))
local notation "D₀"=> Meadow.studio X.halo (radiusB p)
local notation "O" => Chi.canonical
local notation "f₀" => Jams.plays C O γ
local notation "B₀"=> Beam.marquee H P
variable (hd:z≥r+4)(hv:∀ i:Stars,mulch P (v/2) (fun s=> E s i) (p' i) (q' i)) (ht: P.B=radiusB p) (hb:sanction P (Beam.marquee H P).reg (fun i=>(Jams.plays C Chi.canonical γ i).logRead) (v/2) B)
    (hc:sanction P (Beam.marquee H P).reg (fun i=>(rates C O γ k i).logRead) (v/2) B)
def donation (P:BudgetPoint) (s:Tune H v δ) (γ:ℝ) (k z:ℕ)(t:sun):Tap G c:= Marlin.bison (rates s Chi.canonical γ k t) (Trio.ornament hq (E t)) (Trio.insight P (Jams.recital s t) γ k hq z (E t))
-- mix shrink for changing parameter Fee.
lemma stripe_down {v q b:ℝ} (hv:Stripe w v b)(ht:0<v)(hV:v≤q):Stripe w q b:=by
  intro i; let f(x:ℝ):=(x/v)^i
  rw [← Jams.mix_id]; have hp:= ht.trans_le hV
  rw [show mix w (fun x:sun=>((x.val)/q)^i)=_ from Eq.trans (show _=mix w (fun x:sun=>(v/q)^i*f x.val) from (congr_arg _ (funext (fun x=>by unfold f; rw [←mul_pow]; congr 1; field_simp)))) (mix_times _ _),norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_of_nonneg (by positivity : 0 ≤ (v/q)^i)]; exact pow_le_one₀ (by positivity) ((div_le_one hp).mpr hV))).trans (hv i)
lemma bison_walk (B V:sun→Trio.Offer G c) (D:sun→ Collection.Source G c) : mix w (fun i=>(Marlin.bison (D i) (B i) (V i)).regular)=(Marlin.bison (⟨mix w (fun i=>(D i).logRead),mix w (fun i=> (D i).hardRead)⟩) (mix w B) (mix w V)).regular:=by
  ext i x; simp_rw [mix_eval]; let a:= leanU c i; unfold bison; dsimp only [Function.comp_apply]
  rcases leanU c i with y|⟨y,i⟩
  · dsimp only [Sum.elim]; simp_rw [mix_eval]
  dsimp only [Sum.elim,choir]; simp only [Pi.smul_apply, Function.comp_apply,mix_eval]; exact mix_scale ..
local notation "W₀" => donation hq E P C γ k z
local notation "Y'" => Marlin.lodge (B₀) z (2*z)
local notation "E'"=>fun i => Trio.ornament (c:=c) hq (E i)
abbrev torusP (B:BudgetPoint)(y:Stars→ℝ)(z:ℕ)(S b:ℝ) := b + turnFee B*(Trio.oroW B z y * Real.exp (preExponent B*S))
include hv hq hd hc
lemma frieze (hp: ∀ i:Site c, (coverNumber P.B (neighbors z i):ℝ) ≤ σ) : sanction P (Marlin.pluck P Y').reg (fun i=>(poursP P Y' (W₀ i)).logRead) (v/2) (torusP P p' z σ B):=by
  intro w a hw; let V' (x:sun) := Trio.insight P (recital C x) γ k hq z (E x)
  let c':= a*Trio.oroW P z p'; let g:=E'
  have he i:P.Regular (neighbors z i) (mix w g i)∧ P.supBounds i (neighbors z i) (mix w g i) c' := by rw [mix_eval]; exact wired hq E hd hv hw i
  have hu:0≤ c':=(he 0).2.1
  have hV : Meadow.Budget P (leap z) (mix w g) (c'*Real.exp (preExponent P*σ)):= by
    refine ⟨fun _=>c',fun i=>?_, he⟩; apply budget_finite
    · intro i; split; exact mul_nonneg hu (Real.exp_pos _).le; rfl
    rw [Finset.sum_eq_single i]; rw [if_pos (show (leap z i).site=i from rfl)]
    · exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (hp i) (headline P).exponent_pos.le)) hu
    · intro j _ hi; exact if_neg hi
    simp
  unfold donation; change Meadow.Budget P (Y').reg (mix w (fun i=> (Marlin.bison _ (g i) (V' i)).regular)) _
  rw [bison_walk g V' (rates C _ _ k), show a*torusP P p' z σ B=a*B+turnFee P*(c'*Real.exp (preExponent P*σ)) from by unfold torusP c'; ring]; exact Marlin.reg_bison (B₀) z _ _ _ _ (hc w a hw) hV
omit hc
abbrev grail (s:ℕ)(Y:Stars→Side)(q':Stars→ℝ)(B:ℝ) := 2*(2*((ballCost s:ℝ)*B)+lightTax Y q')
local notation "a₀" => grail D₀ Y q' B
include hb ht
set_option quotPrecheck false
lemma funds (hp:∀ i:Site c,(coverNumber P.B (neighbors (2*z) i):ℝ) ≤ ρ) (hP:4≤v):
   league (Y').softer P.B (Tap.logarithm ∘ W₀) ((raiser P).supportExponent+1) (v/4) (Marlin.tithe (2*z) a₀ P ρ):=by
  let s:=a₀; let f i:=(Marlin.tract c s ∘ leanU c) i  -- syntax
  have he u U:= lightP hq E hd k hv ht hb hP u U -- order
  have hh:0 ≤ s:=(he 0 1).nonneg
  refine ⟨f, (Marlin.caps (B₀) z (2*z) P s hh hp).2,fun i U=>?_⟩
  let F (x:sun):=Trio.insight P (recital C x) γ k hq z (E x); let Z(x:sun):=Sum.elim (fun _:ℕ=>0) (Song.choir (-F x))
  change Scout (v/4) (phraseS fun x=> Z x (leanU c i) U) (Marlin.tract c s (leanU c i))
  cases leanU c i
  · exact (Scout.still (by linarith) (0:ℝ)).enlarged (by rw [norm_zero]; rfl)
  next j =>
    have ht:= (he j.2 (j.1.view U)).scale (-(Song.Rim c)); rw [norm_neg,Real.norm_of_nonneg (rim_nn _)] at ht
    refine ht.replace (fun x hx=>?_); let x':sun:= pinch x; change -(Song.Rim c)*F x' j.2 (j.1.view U) =Song.Rim c * (-(F x' j.2 (j.1.view U))); ring
local notation "δ'"=> Tune.softW X L₀ a p
lemma valueP (hp:∀ i:Site c,(coverNumber P.B (neighbors (2*z) i):ℝ) ≤ ρ) (hP:4≤v) {κ C':ℝ} (h : Candy C Chi.canonical (preExponent P) C' P)
   (hr:Payments.Rates P.B φ δ' (Marlin.tithe (2*z) a₀ P ρ) κ): league (fun i=> ((pluck P Y').hard i).support) P.B (fun i=>(poursP P Y' (W₀ i)).hardRead) (P.supportExponent+1) (v/4) φ :=by
  let Y:= Y'; have hB:1≤v/4:= by linarith
  have hs:= funds hq E hd hv ht hb (k:=k) hp hP
  have hh : league (fun i=> (Y.kernel i).support) P.B (Tap.forced ∘ W₀) ((raiser P).supportExponent+1) (v/4) δ':=by
    obtain ⟨k',hk,hx⟩:= postage h ht (γ:=γ) (e:=(raiser P).supportExponent+1) (by unfold preExponent; change P.supportExponent+1+1≤_; linarith)
    exact ⟨k',hk,fun i U=>(hx i U).lessen hB (by linarith)⟩
  exact venture (hak (Y')) W₀ hB (P:=raiser P) hh hs hr
end personal
end YM.PhysicalNext.Repeat.Jams
