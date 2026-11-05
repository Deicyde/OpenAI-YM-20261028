import YM.RemainderComparison.Hills.Choir
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Equip
/-!
 # p2 physical aperture: unmarked MODEL strong heat costs Σ approved
 from native stencils on all L after stage. Need to integrate these
 post threshold tests with calendar.Distinguish support allocation σ early. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Seasons
open Function Filter Set Lattice RG Tree Wilson Supply Input Org Shoot
open Push PriceCompiler Push.AbsoluteSums Gauge Pressure Testing SectorMeasure Precision
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Psalm Next.Scheduling AnalyticBridge VerifiedReset
open Extra.Iteration
open Height Roost
open ConnectedActivityE6
open Cadenza
open JointLoad.Heir.Suite
open Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {S:Sheet G} {K:MapPrices} {D : Rolls S} {R : Targets S K} {X : Expenses R}
variable {L:Side} {s f : ℝ→ℝ} (E:RG.Stage) {A₁ A y a b d e :ℝ}
open Hills Sienna Fare Lapis Lantern Meadow Song Collection Quotes Geo
local notation "c"=> E.clip
local notation "X'"=> E.paths
local notation "σ"=> E.width
local notation "Y"=> ConnectedActivityE6.loopBill G L
local notation "p"=> Time.probe E
local notation "M"=> Delay.fineMonitor G L
local notation "I" => (fun x=> betaF G x L)
local notation "P"=> E.supportExponent+3
-- payments for pure occupancy Songbook with B=1 (uses <-1/2 gain). Clipped harmony separate.
variable (G) (L)
local notation "Sx"=> (fun t=> (1+(radiusB t:ℝ))^((E.power)*(E.order)))
local notation "v"=> (fun x=> Pressure.fiery G x L)
def conducts (W:ℝ)(j:ℕ)(V q:ℝ):ℝ:= |VerifiedReset.factor| * V*(turnFee (Time.probe E)*(highFee G j (Time.probe E) E.width* W^j*q))
-- α limit |γ| ≤ A. β-core polynomial.
def cost (A:ℝ)(x:ℝ):= let t:= 2*Pressure.fiery G x L; let a:= 4*betaF G x L+A
                       |VerifiedReset.factor| *A*(turnFee (Time.probe E)*t^2*(lowFee G (Time.probe E) E.width * lowerSize E.clip E.paths))+(conducts  G E t 3 a E.paths+(Seasons.conducts G E t 4 a E.paths+conducts G E t 2 1 (ConnectedActivityE6.loopBill G L x)))
local notation "C₀"=> (fun t=>2*v t)
lemma sings (A:ℝ) : Rate G L (-(1/2)) (cost G L E A):=by
   let t:=C₀; have ht:Rate G L (-(1/2)) t := Rate.flame.mul_left _; have hv := (Rate.hat (G:=G) (L:=L)).mul_left (4:ℝ)|>.add ((Rate.const (G:=G) (L:=L) A).weaken (by norm_num))
   have h (j:ℕ) (Fp:ℝ→ℝ)(Qv:ℝ→ℝ) (a b:ℝ) (hp:Rate G L a Fp)(he:Rate G L b Qv)(hx:a+(-(1/2:ℝ)*j+b)≤ -(1/2)) : Rate G L (-(1/2)) (fun x=> conducts G E (t x) j (Fp x) (Qv x)):= (Rate.mul (hp.mul_left |VerifiedReset.factor|) (((((ht.pow j).mul_left _).mul he)).mul_left _)).weaken hx
   unfold cost; dsimp only; have hE:=Rate.const (G:=G) (L:=L) E.paths
   refine Rate.add ?_ (Rate.add (h 3 _ _ _ _ hv hE (by norm_num)) (Rate.add (h 4 _ _ _ _ hv hE (by norm_num)) (h 2 (fun _=>1) _ _ _ (Rate.const 1) (ConnectedActivityE6.loopBill_rate G L) (by norm_num))))
   exact (((((ht.pow 2).mul_left _).mul_right _).mul_left _)).weaken (by push_cast; norm_num)
lemma wings (t :ℝ) (V:BudgetPoint)(hp:Temper V E t G L) (hc:0≤ b)(hh:b≤ Y t)(hm:|d| ≤ A)(ha:|y| ≤ 4*betaF G t L) : tickets G V c σ X' b y d ≤ cost G L E A t:=by
   let X:= p; let K:= E.paths; have hx: cousin V X :=⟨hp.power,hp.order,hp.salary⟩ ; obtain ⟨hr,hL,hu,hH⟩:= Meadow.postage (G:=G) («σ»:=σ) V X hx
   have hZ: 0≤ K:= E.paths_pos.le; have hy : 0 ≤ lowerSize c K:= by unfold lowerSize; have := (c).quadratic_pos; positivity
   let R:=C₀ t; have ht:V.threshold≤R:=hp.pact
   have hv:=V.threshold_pos; have hr':= turnFee_pos X; have hA:= lowFee_nonneg G X E.width_pos
   have he: |-(y+d)| ≤ 4*betaF G t L+A:= by rw [abs_neg]; exact (abs_add_le ..).trans (add_le_add ha hm)
   unfold Hills.tickets Seasons.cost; refine add_le_add ?_ ?_
   · unfold host; rw [hr,hL,abs_mul,abs_neg]; gcongr
     all_goals first|exact ht|exact hm| positivity| exact mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans hm)
   have hk j (fP q t' v':ℝ) (hp : |t'|≤ v')(hv : 0≤fP)(he:fP≤q): Song.tenor G j V σ fP t' ≤ Seasons.conducts G E R j v' q:=by
       have hx: 0≤ v':= (abs_nonneg _).trans hp; have hs:= hp; have h:= highFee_pos G X j E.width_pos
       unfold Song.tenor Seasons.conducts; rw [hr,hH,abs_mul]; apply mul_le_mul (mul_le_mul_of_nonneg_left hp (abs_nonneg _)) _ _ _ <;> first | exact mul_nonneg (abs_nonneg _) hx| gcongr| positivity
       all_goals have hT:0 ≤ R:=V.threshold_pos.le.trans ht; positivity
   exact add_le_add (hk 3 _ _ _ _ he hZ le_rfl) (add_le_add (hk 4 _ _ _ _ he hZ le_rfl) (hk 2 _ _ _ _ (by norm_num) hc hh))
-- uniform weak fee conversion. REAL B incl halo and hard.
def stampede (B:ℕ)(A:ℝ):= Footprint.payment 1 B (E.power * E.order) (E.width/32) ((1+(B:ℝ))^(E.power*E.order)) (Fintype.card Signed * A) (E.supportExponent+3) Geo.lowCount
lemma blood (A:ℝ) : Rate G L (-(1/2)) (fun t=> stampede E (radiusB t) (cost G L E A t)):=by
    let f x:=Footprint.spread 1 (radiusB x)
    have he :Reserve G L fun t=> (f t:ℝ):= by unfold f Footprint.spread; simp only [one_mul]; exact Reserve.ball radiusB Reserve.field
    let Fp:= (fun t=> (1+(radiusB t:ℝ))^(E.power*E.order)); have ht : Reserve G L Fp:= (((Reserve.const (1:ℝ)).add Reserve.field).pow _)
    unfold stampede Footprint.payment Footprint.degreeIncome
    have hv:=(ht.rate); have hp:=sings G L E A
    let t : ℝ := (1-Real.exp (-(E.width/32)))⁻¹
    simpa only [add_zero] using! ((((((hp.mul_left (Fintype.card Signed:ℝ)).mul_left (Real.exp ((E.supportExponent+3)*Geo.lowCount))).mul ht.rate).mul he.rate).mul_right (((E.width/32)⁻¹^(4+E.power*E.order) * (4+E.power*E.order).factorial * Real.exp (E.width/32)))).mul_right t)

lemma spring (t:ℝ)(V:BudgetPoint)(hp:Temper V E t G L)(hc:0≤ b)(hh:b≤ Y t)(hm:|d| ≤ A)(ha:|y| ≤ 4*betaF G t L) : Hills.package V P σ (tickets G V c σ X' b y d) ≤ Seasons.stampede E (radiusB t) (cost G L E A t) :=by
    have hx:= wings G L E t V hp hc hh hm ha
    have hV: 0 ≤ (1-Real.exp (-(σ/32)))⁻¹:= inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith only [E.width_pos])))
    unfold Hills.package Footprint.payment Footprint.degreeIncome stampede
    rw [hp.pose,hp.power,hp.order]; unfold Footprint.payment Footprint.degreeIncome; have ht := E.width_pos; gcongr
local notation "Ao"=> ((Time.probe E))
lemma winter (t:ℝ)(V:BudgetPoint)(hp:Temper V E t G L)(hm:|d| ≤ A) : Hills.quoteA G V c σ X' d ≤ A*(2*C₀ t)*(lowHard Ao c σ X' * (1+(radiusB t:ℝ))^4):=by
   have hZ:Time.Same E V:=⟨hp.power,hp.order,hp.salary⟩
   have hh := V.threshold_pos; have hv:0≤ A:=(abs_nonneg _).trans hm
   have ht : hitPower V G d 0 ≤ A*(2*C₀ t):= by unfold hitPower; rw [add_zero,abs_zero,zero_mul,zero_mul,zero_mul,add_zero]; have he:= hp.pact; gcongr -- positivity hm V
   have hp' := Time.lowSoft_exp E hZ -- check
   unfold Hills.quoteA; exact mul_le_mul ht ((by have ht:=hp'; rw [hp.pose] at ht; exact ht)) ((budget_pos V G c E.width_pos E.paths_pos.le).2.2) ((hitPower_pos V G d 0).trans ht)
structure Thaw (A:ℝ)(t:ℝ)(q:ℝ):Prop where
   package (V:BudgetPoint) (H: Temper V E t G L): (P)/(V.B:ℝ) ≤ σ/4∧
              ∀ (b y a:ℝ),0≤ y→y≤ ConnectedActivityE6.loopBill G L t→ inBand (betaF G t L) b→|a|≤A → Hills.package V (E.supportExponent+3) E.width (tickets G V E.clip E.width E.paths y b a) ≤ q ∧ Hills.quoteA G V E.clip E.width E.paths a≤q
lemma arise (A:ℝ) : ∀ᶠ t in atTop, Thaw G L E A t ((betaF G t L)^(-(1/4:ℝ))):=by
   have hh:= ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Work.E01.radiusB_tendsto|>.const_mul_atTop E.width_pos).eventually_ge_atTop (4*(P))
   let f t:= A*(2*C₀ t)*(lowHard Ao c σ X' * (1+(radiusB t:ℝ))^4)
   have hp:Rate G L (-(1/2)) f:= by
       have hR: Reserve G L fun t=> lowHard Ao c σ X'*(1+(radiusB t:ℝ))^(4:ℕ) := ((Reserve.const _).mul (((Reserve.const _).add Reserve.field).pow _)); have hf:Rate G L (-(1/2)) C₀:= (Rate.flame.mul_left _)
       simpa only [add_zero] using! (((hf.mul_left 2).mul_left A).mul hR.rate) -- arg
   filter_upwards [hh,blood G L E A (-(1/4:ℝ)) (by norm_num), hp (-(1/4:ℝ)) (by norm_num), Delay.shift_pos G L] with t ht hV he hy
   constructor; intro V H; refine ⟨(div_le_iff₀ (show (0:ℝ)< (V.B:ℝ) from Nat.cast_pos.mpr V.B_pos)).2 ?_,fun b y p' hb hh h h'=> ⟨(spring G L E t V H hb hh h' ?_).trans ((le_abs_self _).trans hV),(winter G L E t V H h').trans ((le_abs_self _).trans he)⟩⟩
   · rw [H.pose]; change 4*_ ≤ σ*(radiusB t:ℝ) at ht; linarith only [ht]
   rw [abs_of_pos (Access.lane_pos hy h)]; exact h.2
end YM.RemainderComparison.Seasons
