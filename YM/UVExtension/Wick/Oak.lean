import YM.UVExtension.Wick.Bower

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' t n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}

section fuel
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {y:E} {f g:E→ℝ}
lemma conical {B : ℝ→ℝ} (hB : Rate G L 1 B) (j : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ m : ℕ,1 ≤ m → ((|B x| *m:ℝ))^j ≤ Real.exp ((C*Delay.bill G L x^5) * m) := by
  refine ⟨3*(j:ℝ),by positivity,?_⟩
  filter_upwards [hB 2 (by norm_num), (Work.E09.betaF_growth G L).eventually_ge_atTop 2] with x hx ht m hm
  let M : ℝ:=m; have hM:1≤ M := by unfold M; exact_mod_cast hm
  let g:=Delay.bill G L x; let t:= betaF G x L; have ht : 2≤ t := ht
  have he : 1≤ g:= Delay.bill_ge ..; have ht':0 < t:= by linarith
  have hh : Real.log t ≤ g := by unfold g Delay.bill t; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
  have hp : |B x| ≤ Real.exp (2*g^5*M) := by
    apply hx.trans; rw [Real.rpow_two,show betaF G x L=t from rfl,← Real.exp_log ht', ← Real.exp_nat_mul]
    apply Real.exp_monotone; push_cast; nlinarith [le_self_pow₀ (n:=5) he (by decide)]
  apply (pow_le_pow_left₀ (show 0≤ |B x| *M from by positivity) (mul_le_mul hp (show M ≤ Real.exp (g^5*M) by
    have he := one_le_pow₀ (n:=5) he; linarith [Real.add_one_le_exp (g^5*M), le_mul_of_one_le_left (zero_le_one.trans hM) he]) (zero_le_one.trans hM) (Real.exp_pos _).le) j).trans_eq
  rw [← Real.exp_add,← Real.exp_nat_mul]; congr 1; unfold g M; ring

end fuel

namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
variable (z : Vines ι) (hv:z∈parade (ι:=ι) (betaF G x L) g)
set_option quotPrecheck false
local notation "β" => z none
local notation "θ" => (z none).re
local notation "Ψ" => z ∘ some
variable (hq : ‖z none‖/ (z none).re≤2)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E}
    (ht:V' τ=X.V) (hM:Mode V' τ j u)
local notation "S₁"=> steer X A
local notation "P₁"=> warmth X
abbrev oneV (z : Vines ι) (hz:z∈parade (betaF G x L) g) : Cash W x μ L Q o a T (flight R (z none).re) := (hF.known _ (marching _|>.1 hz|>.1)).some
include hF hv
lemma drift : ∃ (p : ℝ), 0 < p ∧ p ∈ Set.Ioo (betaF G x L / 2) (2*betaF G x L) ∧ (z none).re/8≤|p-(z none).re| ∧ Nonempty (Cash W x μ L Q o a T (flight R p)) := by
  have he:= (marching z).1 hv; have hx: 0<betaF G x L := Festa.altitude (H:=H)
  obtain ⟨p,hP,H⟩:= bogey hx ⟨he.1.1,he.1.2.1⟩
  refine ⟨p,(by have hh:=hP.1; linarith),hP,H,hF.known (p:ℂ) (show (p:ℂ)∈ aisle _ from ⟨hP.1,hP.2,?_⟩)⟩
  rw [Complex.ofReal_im,abs_zero]; positivity

include N hS hX hm hc hr ht hM hq
lemma scallop (I : Finset (Bond f)) (z' : Air f G) (p q : ℝ) (hy:Brush j p 1 Real.log 1) (hQ:Brush j q 1 Complex.exp 0) :
    Brush j 1 ((1+(1+j.factorial*q)*(1+24*(j.factorial*p+j.factorial*p))*2)*(B*2^K) * facescale I (scaled θ z')^K) (fun t=> scorched X A I (V' t) β z') τ:= by
  have hW := drift hF z hv
  have hh:= marching z|>.1 hv; have hL:= Festa.altitude (H:=H)
  let d':= θ; have ht': 0<d' := breath hL hh.1; let f s:= facescale I (scaled s z'); have hf := (Flux.expenses I (scaled θ z')).1
  obtain ⟨p',hp,hH,hj,⟨W'⟩⟩:= hW
  have hx :=flicker I z' hL hh.1.1.le hp hH.2.le
  have h R (i:Cash W x μ L Q o a T R) (v):= ((N.granted _ _ S T R a i hS rfl).2 E V' F X τ hX hc hr hm ht hM).2 v|>.2.1 I -- `let` tactic cannot infer R? test
  let y:= B*(2*f d')^K
  have hm : Brush j 1 y (fun t=> scalp I X (V' t) d' A (scaled d' z')) τ:=by
    have hb:1 ≤ f d':=hf; apply (h _ (oneV hF z hv) (scaled d' z')).climb le_rfl; unfold y; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by exact zero_le_one.trans hb) (show f d'≤2*f d' from (by linarith)) _) N.roof
  have hg := (h _ W' (scaled p' z')).climb le_rfl (show B*facescale I (scaled p' z')^K≤y from
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (Flux.expenses ..).1) hx _) N.roof)
  apply (tow X I p' d' V' ht N.bay z' hp ht' hj hm hg β rfl hq hy hQ).climb le_rfl
  unfold y f d'; ring_nf; rfl

end Bower
end YM.UVExtension.Wick
