import YM.UVExtension.Guild.Fair
import YM.UVExtension.Yard.Allowance
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Guild
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}

private def due (G:Gauge)(L:Side)(b:ℕ)(x:ℝ)(P:RG.Stage)(ε:ℝ): Prop:=
    let u:=gold G L x; let z:= Height.away P
    z*u+u+ z*(planks G L b P x* Real.exp (stout P * coverTicket b)) ≤ ε*(Time.credit G P*δE x)
lemma lending (G : Gauge) (L:Side) (b : ℕ) (P: RG.Stage){ε:ℝ} (ho:0<ε): ∀ᶠ x in atTop,Guild.due G L b x P ε:= by
  have ht : Rate G L (-(23/20)) (gold G L) := Rate.power
  have hh := (((ht.mul_left (away P)).add ht).add (((Trio.skyward G L b P).mul_right (Real.exp (stout P * coverTicket b))).mul_left (away P)))
  let z:= Height.away P; let A:= Time.credit G P
  have hp: 0<A:=Time.credit_pos ..
  filter_upwards [Sienna.contraction G L (a:=1) (b:=ε*A) (by positivity) (show Rate G L (-(23/20)) (fun x=> z*gold G L x+gold G L x+ z*(planks G L b P x*Real.exp (stout P*coverTicket b))) from hh) (show -(23/20:ℝ)< -(11/10) by norm_num),Delay.shift_pos G L,eventually_gt_atTop (0:ℝ)] with x ht hx hX
  have he : δE (betaF G x L)=betaF G x L ^ (-(11/10):ℝ):= by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le]; norm_num
  have hh : δE (betaF G x L) ≤ δE x:= by
    unfold δE; refine Real.rpow_le_rpow (by unfold Clock.gap; positivity) ?_ (by norm_num)
    have hz : x ≤ betaF G x L:= le_add_of_nonneg_right (Work.E04.shift_nonneg G L)
    exact inv_anti₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt hz)
  rw [one_mul,← he] at ht; exact ht.le.trans ((mul_le_mul_of_nonneg_left hh (mul_nonneg ho.le hp.le)).trans_eq (mul_assoc ..))

open Payroll
variable (s:Sheet G) (K:MapPrices) (X:Targets s K)

def Fall (F : ℕ→ℕ): Prop:= ∀ j i, StepStages j i →∀ L:Side,F j ≤ L.val → ∀ W μ a ε o, 0<W→0<μ→0 ≤ a →0<ε → (s.profile i).supportExponent+3<(X j i).exp → (X j i).rate ≤ -(7/16:ℝ) → ∀ᶠ x in atTop, Flew (X j i) (s.profile i) L W μ a o x ε
lemma fallsStart:∃ P:ℕ→ℕ,Fall s K X P:=by choose n hn using fun i j=> collecting (X i j); exact ⟨fromMax n,fun j i h L hh W μ a ε o hW hm ha he=> hn _ _ L ((le_fromMax n h).trans hh) W μ a ε o hW hm ha he _⟩

variable {s K X} {D: Rolls s}{Θ:Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ}

structure Tool (ε t:ℝ):Prop where
    paid : ∀ (L:Side) (G: Gauge)(S:Stage) (K:ℝ),0 ≤ K→∀ᶠ x in atTop,Yard.Grants G L S x t K ε
    hr : 0 < ε
    hx : ε ≤ 1/16
    hit : ε ≤ t
lemma tooling (t:ℝ)(h:0<t):∃ ε:ℝ,Tool ε t:=by
  obtain ⟨ε,hp,hr,hx,ht⟩:= Yard.chapter t h; exact ⟨ε,fun L G S K hy=> ht G L S K hy,hp,hr,hx⟩
def pride (D:Rolls s) (j:ℕ):=(s.profile j).drift+|G.slopeConstant*Real.log (D.L j).val|+1
variable (R:PhysicalNext.Repeat.Register D p u l)
structure Paperwork (ε t:ℝ) (V: Delays Θ) : Prop where
   charter : Tool ε t
   gain : ∀ j i,StepStages j i → ∀ x, V.betaEntry j≤x → Flew (X j i) (s.profile i) (D.L j) (u j i) (R.μ j i) (R.c j i) (R.o j i) x ε
   chord : ∀ j i,StepStages j i → ∀ x, V.betaEntry j ≤ x → Guild.due G (D.L j) (X j i).halo x (s.profile i) ε ∧ Lamppost.Chateau G (D.L j) ε (s.profile i) x ∧ Yard.Grants G (D.L j) (s.profile i) x t (pride D j) ε
variable {ε t : ℝ}
lemma issues (ξ:Tool ε t)(hx:∀ j i,StepStages j i→(p j i).wanting ≤ -(7/16:ℝ) ∧ (s.profile i).supportExponent+3 ≤ (p j i).earn){f:ℕ→ℕ}(hf:Fall s K X f)(hL :∀ j,f j≤(D.L j).val)(V:Delays Θ) : ∃ W:Delays Θ,DelayLe V W∧ ∀ Y:Delays Θ,DelayLe W Y → Paperwork R ε t Y:=by
  let F: ℕ→ℕ→ℝ→Prop:= fun j i x=>Flew (X j i) (s.profile i) (D.L j) (u j i) (R.μ j i) (R.c j i) (R.o j i) x ε
  have hk (j i :ℕ) (h:StepStages j i): ∀ᶠ x in atTop,F j i x:= by
    obtain ⟨hA,hp,hV,hQ⟩:= R.consumes j i h; obtain ⟨hl,hk⟩:=hx _ _ h
    exact hf _ _ h _ (hL j) _ _ _ _ _ hA hp hV ξ.hr (by linarith [(p j i).worth,(p j i).first,(p j i).second]) ((p j i).reach.le.trans hl)
  have hp j i (h:StepStages j i) := (hk j i h).and ((lending G (D.L j) (X j i).halo (s.profile i) ξ.hr).and ((charter (G:=G) (D.L j) (s.profile i) ξ.hr).and (ξ.paid (D.L j) G (s.profile i) (pride D j) (by unfold pride; linarith [(s.profile j).drift_ge, abs_nonneg (G.slopeConstant*Real.log (D.L j).val)]))))
  -- tag infer predicates
  let P (j i:ℕ) (x:ℝ):= F j i x ∧ Guild.due G (D.L j) (X j i).halo x (s.profile i) ε ∧ Lamppost.Chateau G (D.L j) ε (s.profile i) x∧Yard.Grants G (D.L j) (s.profile i) x t (pride D j) ε
  obtain ⟨x,-,hv,hx⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ (P j) (hp j))
  exact ⟨{V with betaEntry:=x},⟨hv,le_rfl,le_rfl,le_rfl⟩, fun Y hy=>⟨ξ,fun j i he y hh=>(hx j y ((hy.beta _).trans hh) i he).1,fun j i he y hh=>(hx j y ((hy.beta _).trans hh) i he).2⟩⟩

section cadence
-- when Factor is set
variable {Z: Metals G} {D:Rolls Z.p} {A : Alloy Z D} {R : Factor A} (U:Paperwork R.shape ε t A.delay)
include U
lemma purchase (hp:Roof.Pew R.v R.t R.prices R.recordP R.span R.shape (Roof.wind R.menu) A.delay ε) (hK: Height.Rich R.shape ε A.delay): Crest R ε:=by
  refine ⟨hp,hK,U.charter.hr,U.charter.hx,fun m=>?_⟩; obtain ⟨hz,-⟩:= U.chord _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)
  obtain ⟨h₁,h₂,h₃,h₄⟩:= Rain.jersey (A:=A) (m:=m)
  unfold preExponent; rw [h₃,h₄]; unfold Time.forecastE; rw [params_eq A.B.valid]; exact hz
end cadence
end YM.UVExtension.Guild
