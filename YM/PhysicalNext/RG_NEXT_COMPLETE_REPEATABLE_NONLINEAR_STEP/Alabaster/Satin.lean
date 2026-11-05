import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.HeadSwitch
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Even
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Bright
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Lookout
import YM.Further.THRESHOLD_SOURCE_RESTART.Intake
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Scarf
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Thatch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Whin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Jasper
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Income
import YM.Planned.ATOM_REGULAR_ESTIMATE.Scale
import YM.Primitives.SMALL_FIELD_EXTERIOR.HaarCoin
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Tariffs
/-!
# Pointed application certificate. Emits Ξ price on REAL varying V
 about every manifest-l sheet. Needs OBOE independently for fringe.
 Hold prices pointwise; to buy with Clutch schedules. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {p μ C v D' d r D K' : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} {η εK θ β a h g l b Y A q e r' u : ℝ}
local notation "F₀" => (facescale (univ:Finset (Bond f)))
local notation "L₁" => low R I
-- momentum issued after all; containing Oboe(v), portfolio A constant. -/
structure Loom (H : Cash W p μ L Q o C T R) (a b v : ℝ) (χ : Chi) (j : ℕ) where
  body : Canary G a b
  grants : 8*o.a*Pressure.fiery G p L ≤ a/2
  rays : ℝ
  seat : ℝ
  money : ℝ
  V : Utopia H j v rays seat money χ
  tariff : ℝ
  slots : 0 ≤ tariff
  prices : StampPrice T o p rays v χ j tariff
  jolt : ℝ
  jump : 0 ≤ jolt
  order : ℕ
  mask : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=p→ X.width=o.K → X.χ=χ→X.manifest→∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (U:E→ Config G c) (x:E), U x=X.V→ Mode U x j v→ Glass P X U x j W ∧ ∀ z:Air f G,
       Clutch X z o.a R.beta rays x j U (fun y=> steer X a (worldZ X R.beta z) (U y)) (fun y=> course X a R.beta z (U y)) ∧ ∀ I: Finset (Bond f), let p:=(facescale (univ : Finset (Bond f)) z)
       Brush j (jolt*p^order) 1 (fun y=>scalp I X (U y) R.beta a z) x ∧ Brush j (jolt*p^2) 1 (fun y=>draftI X I R.beta a (U y) z) x
section score
variable (V : Loom H a b v χ j)
include V
lemma flight : ∃ M: ℝ,0≤M ∧ ∀ (I : RG.Rep G f) (_P' : Facing R I) (d : ℝ), 0<d → d ≤ 1 → |(low R I)^2-1| ≤ d →
    ∀ (F:Forest S.ratio) (X:Coat T F), X.x=p→X.width=o.K→ X.χ=χ→X.manifest→∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (U:E→ Config G c) (x:E), U x=X.V→ Mode U x j v→ ∀ z:Air f G, ∀ i : Finset (Bond f), let c u:= scalp i X (U u) R.beta a z
       let p':=facescale (univ: Finset (Bond f)) z
       Brush j (d*M*p'^(V.order+2*j)) 1 (fun y=>scalp i X (U y) I.beta a (low R I • z) - c y) x:= by
  obtain ⟨M,hM,Hm⟩:=crystals j V.jolt V.jump; let t := V.jolt
  have ht:0 ≤ t:=V.jump; refine ⟨(t*M)*3^j,mul_nonneg (mul_nonneg ht hM) (by positivity),?_⟩
  intro I H d hd he hh F X hX hK hχ hU E _ _ _ U x hx hQ z i c p
  obtain ⟨hc,hF⟩:= ((V.mask F X hX hK hχ hU E U x hx hQ).2 z).2 i -- syntax
  have hg:= Hm _ _ _ hd.le he (show |1-(low R I)^2|≤d from (by rw [abs_sub_comm]; exact hh)) (show 1≤p from (Flux.expenses ..).1) _ _ _ hF
  refine (((hc.paints hg).trim).climb ?_ le_rfl).shimmy (Eventually.of_forall fun y=> ?_)
  · unfold t; rw [pow_add]; exact le_of_eq (by unfold p; ring)
  change _ = c y*_
  dsimp only; rw [show scalp i X _ _ _ _ = _ from sail H X i z (U y) a b V.body]; unfold c; rw [hx]; ring_nf -- maybe syntax

-- joint integral norm differences Jet, price via poll.
theorem spectra : ∃ K:ℝ,0 ≤ K ∧ ∃ s:ℝ,0<s∧ s≤1/4∧ ∀ {C':ℝ} (I:RG.Rep G f) (_ : Cash W p μ L Q o C' T I) (g f₀:ℕ→ℝ) (t:ℝ),Equalized Q.table R I g f₀ t→ t ≤ s→0<t →
    ∃ f': Molecule S→ℝ, SumBudget f' K ∧ ∃ n : ℕ, n = (V.order+2*j) ∧
    ∀ (F:Forest S.ratio) (X:Coat T F), X.x=p→ X.width=o.K→ X.χ=χ→X.manifest→ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E→ Config G c) (x:E), U x=X.V→ Mode U x j v → ∀ z:Air f G, ∀ (p:Molecule S) (I':Finset (Bond f)),
       Healthy (Pressure.temp X.x) (H.unionP p) X.V →
       let r':= low R I; let Tk (_w:ℝ) := walk X.relating r' z
       let U₀ y:= recoil I' X (U y) a Q.table p R W o.a Q.halo z
       let U' y:= recoil I' X (U y) a Q.table p I W o.a Q.halo (r' • z)
       let k:=(facescale (univ:Finset (Bond _)) z)^n
       Brush j ((Tk 1+|Tk 1-1|/t+1)*k*(t*f' p)) 1 (fun y=> Tk 1 * U' y-U₀ y) x:= by
  obtain ⟨C,hC,h⟩:=flight V; obtain ⟨A,hA,s,hs,Hs⟩:= warpPriced V.V _ V.slots V.prices
  let M:= C*3^j+V.jolt*3^j+1; have hh:= V.jump; have hM:0≤M:=by unfold M; positivity
  refine ⟨M*(M*(M*A)),by positivity,min s (1/4),lt_min hs (by norm_num),min_le_right ..,?_⟩; intro C' I H' g f' t hp ht' hT
  obtain ⟨f,hF,hP⟩:= Hs I H' g f' t hp (ht'.trans (min_le_left ..)) hT
  refine ⟨fun i=> M*(M*(M*f i)),budget_scale hM (budget_scale hM (budget_scale hM hF)),V.order+2*j,rfl,?_⟩
  intro F X hX hK hχ h₀ E _ _ _ U x hU hv z q I' hQ L' k R₀ R' w
  have ht : t ≤ 1:= ht'.trans ((min_le_right ..).trans (by norm_num : (1:ℝ)/4≤1))
  let v:= facescale univ z; have hh':1≤v:=(Flux.expenses ..).1
  obtain ⟨hc,Hc⟩:= (V.mask F X hX hK hχ h₀ E U x hU hv).2 z
  have hv' :=(Hc I').1; let K y:= scalp I' X (U y) R.beta a z; let K' y:= scalp I' X (U y) I.beta a (L' • z)
  have hQ' := h I hp.toFacing t hT ht hp.heat F X hX hK hχ h₀ E U x hU hv z I'
  obtain ⟨ha,hI⟩:=hP F X hK hX h₀ hχ E z U _ _ x hv hc q hQ
  let f' y:= floating (vary X (U y)) o.a R W Q.table (course X a R.beta z (U y)) (own q) Q.halo q; let g' y:= floating (vary X (U y)) o.a I W Q.table (course X a I.beta (L' • z) (U y)) (own q) Q.halo q
  have hg:g'=(fun y=> floating (vary X (U y)) o.a I W Q.table ((low R I) • course X a R.beta z (U y)) (own q) Q.halo q):= funext fun i=> congr_arg (fun x=>floating _ _ _ _ _ x _ _ _) (coursing hp.toFacing X a _ _)
  have hx₁: Brush j (f q) 1 g' x := ha.shimmy (Eventually.of_forall fun i=> congr_fun hg i)
  have hx₂: Brush j (t * f q) 1 (g'-f') x := hg.symm ▸ hI
  have hv'': Brush j (V.jolt*w) 1 K x:= hv'.climb (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh' (Nat.le_add_right ..)) hh) le_rfl
  let c:= k 1; have hcc : 0≤c:= (bristle _ _ (uplift hp.toFacing|>.2.2.1) _).le
  have hf₀:= ((hQ'.paints hx₁).smul c).trim; rw [Real.norm_of_nonneg hcc] at hf₀
  have Z:= (((hv''.paints hx₁).smul (c-1)).gathering (hv''.paints hx₂)).trim
  refine ((hf₀.gathering Z).climb ?_ le_rfl).shimmy (Eventually.of_forall fun y=>?_)
  · have hm : 1≤M:=by unfold M; apply le_add_of_nonneg_left; positivity
    have hp : 0≤w:= pow_nonneg (zero_le_one.trans hh') _; have hv := hF.1 q
    change (c* ((t*C*w)*(f q)))*(1+(1+1))^j+ (|c-1| *(V.jolt*w*f q)+(V.jolt*w)*(t*f q))*(1+(1+1))^j≤ (c + |c-1|/t+1)*w*(t*(M*(M*(M*f q))))
    have h₁: V.jolt*3^j ≤ M:=by unfold M; have hD:= mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ) ≤3) j); linarith only [hD]
    have h₂: C*3^j ≤ M:= by unfold M; have hD:= mul_nonneg hh (pow_nonneg (by norm_num : (0:ℝ) ≤3) j); linarith only [hD]
    calc
      _ ≤ c*M*w*t*f q+|c-1| *M*w*f q+M*w*t*f q := by norm_num; nlinarith only [mul_le_mul_of_nonneg_left h₁ (show 0≤ |c-1| *w*f q by positivity),mul_le_mul_of_nonneg_right h₁ (show 0≤ w*t*f q by positivity),mul_le_mul_of_nonneg_left h₂ (show 0≤c*w*t*f q by positivity)]
      _ = (c+|c-1|/t+1)*w*(t*(M*f q)):= by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left (mul_nonneg hM hv) hm).trans (le_mul_of_one_le_left (by positivity) hm)) hT.le) (by positivity)
  · change c * (K' y*g' y) - K y*f' y= c*((K' y-K y)* g' y)+ ((c-1)*(K y*g' y)+ (K y*(g' y-f' y))); ring
end score
end YM.PhysicalNext.Repeat.Alabaster
