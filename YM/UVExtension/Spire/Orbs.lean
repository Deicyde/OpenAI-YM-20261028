import YM.UVExtension.Spire.Alpine
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
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
open Guild Tabernacle
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
open Cart
namespace Fitted
variable {R hG t hk hp N n} (H:Fitted R hG t hk hp N n)
    (V:Cart A.B.a N H.Hut)(he:H.Took V) {z:PlotN N}(hv:z∈Harbor N)(hZ: Cart.Light N z)
    {b:ℝ}
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
local notation "W#"=> H.W N

/-! # meshwise reports. Later packet and Start choices fixed at these pin,
    can preselect cart, sequence witnesses. Starter shelf held. -/
variable (hf: Fees A.B.a)

def sonnet (b:ℂ): PlotN N:= V.picked hG a! N H.Hut hf (b:=b)
def Third (b:ℝ):= faceV (R:=R) (H.sonnet V hf (b:ℂ))
def Rest (b:ℝ):= H.graceT (H.sonnet V hf (b:ℂ))
def Sail (b:ℝ):= H.cash (H.sonnet V hf (b:ℂ))
variable (hh : (↑b:ℂ)∈ Camp.Broad A.B.a)
include hh he
lemma acts : Shot H (H.Rest V hf b) (H.Third V hf b) (H.Sail V hf b) ∧ (H.Third V hf b 0)=A.B.a.clock.bar+b:=by
    have hx:= H.blessed V he hf hh; have hp:= V.laced hG a! N H.Hut hf hh; exact H.stock V he hp.1 hx hp.2

def prays (v:ℂ)(i:ℕ)(hi:i≤N):ℂ:= ↑(Camp.slope a! cN i)+(Camp.pulse a! i:ℂ)*Camp.Cart.node N (sonnet H V hf v) i hi
def veins (v:ℂ)(i:ℕ)(hi:i≤N): Hold A.B.a i n (H.W i):= Camp.Cart.play a! N H.Hut V (sonnet H V hf v) i hi

def gates (v:ℂ)(i:ℕ)(hi:i≤N): Tabernacle.Readings G (A.B.a.budget i) (A.B.a.S.side i n):= (H.veins V hf v i hi).val
omit hh he
open Complex
lemma emits : DifferentiableOn ℂ (sonnet H V hf) (Camp.Broad a!):= Cart.canon hG a! N H.Hut V hf
lemma glint (b:ℂ)(hh:b∈Camp.Broad a!): H.sonnet V hf b∈ Harbor N := (V.laced hG a! N H.Hut hf hh).1

lemma nowBeta (m:ℕ)(hm:m≤N): DifferentiableOn ℂ (fun v=>prays H V hf v m hm) (Camp.Broad a!)∧∀ v∈ Camp.Broad a!, ‖prays H V hf v m hm‖ ≤3*A.B.a.clock.hatBeta m:= by
    constructor
    · let u(z:ℂ):= node N (sonnet H V hf z) m hm; have he:DifferentiableOn ℂ u (Camp.Broad a!) :=fun i hi=> differentiableWithinAt_pi.mp (H.emits V hf _ hi) _
      exact differentiableOn_const _ |>.add (he.const_mul (_:ℂ)) -- parse
    intro v hz; let w:= H.sonnet V hf v; apply le_trans (norm_add_le ..); rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (pulse_pos ..|>.le)]
    have h0:0<A.B.a.clock.hatBeta m:= zero_lt_one.trans (A.B.a.fits.delayed _)
    obtain ⟨hA,hB⟩:= land (A:=A) hG N m hm
    rw [Real.norm_of_nonneg (show 0≤Camp.slope _ _ _ from by linarith only [h0,hA])]; have ht: ‖w‖ ≤ rad:= mem_closedBall_zero_iff.mp (H.glint V hf v hz)
    have hv : ‖node N (sonnet H V hf v) m hm‖≤ 1:= ((norm_le_pi_norm w _).trans ht).trans (by norm_num [rad,rim]); have hp:= (mul_le_of_le_one_right (pulse_pos a! m).le hv).trans (pulse_falls a! m)
    linarith only [hB,hp,h0]
lemma riversV (m:ℕ)(hm:m≤N): DifferentiableOn ℂ (fun v=>H.veins V hf v m hm) (Camp.Broad a!)∧∀ v∈ Camp.Broad a!, ‖(H.veins V hf v m hm)‖ ≤ Camp.soft:= by
    exact ⟨V.music a! N H.Hut m hm _ _ isOpen_ball (fun z hz=> H.glint V hf z hz) (H.emits V hf),fun z hz=> (V.seats a! N H.Hut (H.glint V hf z hz) m hm).1⟩
lemma lamps (m:ℕ)(hm:m≤N): DifferentiableOn ℂ (fun v=>H.gates V hf v m hm) (Camp.Broad a!) ∧ ∀ v∈ Camp.Broad a!, ‖H.gates V hf v m hm‖ ≤ Camp.soft:= by
    have hh:= H.riversV V hf m hm; constructor; · exact ((Tabernacle.Box _).subtypeL).differentiable.comp_differentiableOn hh.1
    exact hh.2
include he hh
lemma really (i:ℕ)(hi:i≤N): H.prays V hf b i hi=↑(H.Third V hf b i)∧ H.veins V hf b i hi=place A.B.a i n (H.W i) (H.Rest V hf b i):=by
   let z:= H.sonnet V hf (b:ℂ); have hz:= H.blessed V he hf hh; let v:= node N z i hi
   constructor
   · have he1:=Complex.re_add_im v; rw [show v.im=0 from (hz _),ofReal_zero,zero_mul,add_zero] at he1
     unfold Third faceV; rw [dif_pos hi]; unfold lock art; push_cast; unfold prays; rw [show Complex.ofReal (node N (H.sonnet V hf (b:ℂ)) i hi).re=v from he1]; rfl
   unfold Rest graceT; rw [dif_pos hi]; exact (H.officious _ he (H.glint V hf _ hh) hz i hi).2 -- Here V infer
lemma realX (i:ℕ)(hi:i≤N): H.gates V hf b i hi= Tabernacle.tuning (A.B.a.budget i) (A.B.a.clock.allowance i) (A.B.a.clock.forcedAllowance i) (H.Rest V hf b i).val:=congr_arg Subtype.val (H.really V he hf hh i hi).2 -- congr_arg
end Fitted
end YM.UVExtension.Spire
#print axioms YM.UVExtension.Spire.Fitted.lamps
#print axioms YM.UVExtension.Spire.Fitted.acts
