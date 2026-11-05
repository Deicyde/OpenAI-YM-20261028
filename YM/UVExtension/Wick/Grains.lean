import YM.UVExtension.Wick.Tolls

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
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)

variable {z : Vines ι} {hv:z∈parade (betaF G x L) g}
namespace Lush
variable {J : Mixed.Costs} {v₀ : ℝ} (hK:Lush N hF z hv v₀ J) (hp:0≤v₀)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E} (he:V' τ=X.V) (hc': X.χ=χ)
    (hV:Mode V' τ j u)
local notation "κ"=> H.unionP
set_option quotPrecheck false
local notation "φ"=> cockpit X A o.a W
local notation "ψ'"=> hK.peeled
local notation "μ'"=> (F.order G).prod X.dice
local notation "θ"=> (z none).re
variable (x' : Molecule S)
-- Brush on normalized real at ζ. use each label tested by many z's BUT one tag sample. partition q* bound.
include he hm hS hc' hr hp hV hX hK
lemma shawl (p:Molecule S) (hq:Healthy (temp X.x) (H.unionP p) X.V) (hs:troupe T R Q.halo (radiusB x) p) (I:Finset (Bond f)) (Z:F.Slice G × Air f G) :
    Brush j (((X.catastrophe (o.ξ/2) (z none).re (blaze p)).indicator (fun y:Air f G=>
      (∏ i∈p, tabs S J (radiusB x) Q.halo hK.peeled i)*(1+v₀+2*r)^j*(1+H.shapeW p)^j*facescale I Z.2^(K*j))) Z.2) 1
      (fun i=> cockpit X A o.a W p R Q.table Q.halo V z I (V' i) (Z.1,gStep ((z none).re) • Z.2)) τ:= by
  rcases Z with ⟨y,w'⟩; let P':= X.wrapY y; let q:Air f G:= gStep θ • w'; let p'(i:E):= steer P' A (loom P' q) (V' i)
  let S':= X.catastrophe (o.ξ/2) (z none).re (blaze p); let T':=θ; let v:=tabs S J (radiusB x) Q.halo hK.peeled
  let l':= Matter.own p; let f(k)(i:E):=amberP (vary P' (V' i)) R Q.table W o.a l' Q.halo V (z none) (z∘some) (sailplane P' A q (V' i)) (p' i) (P'.input (loom P' q)) k
  let g':= fun i=>held X A o.a W p R Q.table Q.halo V z I (V' i) (y,q)
  have hh:= hF.hovers hX hr hm hV he p N.bay N.foot hv I (y,q); apply Brush.shimmy (f:=g') _ hh.symm
  have hu : 0<θ:= hK.link.laws.intake.positive; have ht' :(gStep (z none).re)≠0:=(inv_pos.mpr (Real.sqrt_pos.mpr hu)).ne'; have hk' : scaled θ q = w':= inv_smul_smul₀ ht' _
  by_cases hz:w'∈S'
  · rw [Set.indicator_of_mem hz]
    obtain ⟨hL,hQ⟩:= hK.breathes E V' F P' hX hc' hr hm τ q hV he; specialize hL I; rw [hk'] at hL
    have he i (hi:i∈p) : Brush j (v i) (r*spanW T R (radiusB x) Q.halo i) (f i) τ := hQ _ i
      (Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.supportP) hi) hq)
    have hhV :(∑ i∈p,r*spanW T R (radiusB x) Q.halo i)≤r*(2*H.shapeW p):= by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Utopia.worthy _ hs) (zero_le_one.trans hK.conduit.active)
    have H' := (all_thread p f v _ he).climb le_rfl hhV
    have hp' := (hL.paints H').trim
    apply hp'.climb _ le_rfl; let x:= facescale I w'; let W:=1+H.shapeW p
    have hr:=hK.conduit.active; have he : 1 ≤ x^K:= one_le_pow₀ (Flux.expenses I w').1; have hr':1 ≤ W := le_add_of_nonneg_right (H.positive_volume p); rw [one_mul]
    have hf : 1+(v₀*x^K+r*(2*H.shapeW p)) ≤ (1+v₀+2*r)*W*x^K := by
      have hv' : x^K≤ W*x^K:= le_mul_of_one_le_left (by linarith only [he]) hr'; have H: H.shapeW p ≤ W*x^K:= le_trans (le_add_of_nonneg_left zero_le_one) (le_mul_of_one_le_right (zero_le_one.trans hr') he); nlinarith only [H,hv',hp,he,hr,mul_le_mul_of_nonneg_left H (zero_le_one.trans hr)]
    change (∏ i∈p,v i)*(1+(v₀*x^K+r*(2*H.shapeW p)))^j ≤ (∏ i∈p,v i)*_ * W^j * x^(K*j)
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have he: 0≤H.shapeW p := H.positive_volume _; exact add_nonneg zero_le_one (add_nonneg hL.pos (mul_nonneg (zero_le_one.trans hr) (mul_nonneg (by norm_num) he)))) hf j) H'.nonneg).trans_eq
    rw [mul_pow,mul_pow,pow_mul]; ring
  rw [Set.indicator_of_notMem hz]; refine Brush.zi ?_ le_rfl zero_le_one
  let Z:= hK.link
  have hv := (N.granted c _ S T _ _ Z hS rfl).2 E V' F P' τ hX hc' hr hm he hV
  unfold S' catastrophe Poll.Crash at hz; change ¬(∀ i∈_,∃ j, _≤_ ∧ _≤_) at hz; push Not at hz; obtain ⟨i,hi,hp⟩:= hz
  let S_: Cash W P'.x μ L Q o a T (flight R (z none).re) := hX.symm ▸ Z
  have H':worldZ P' (flight R (z none).re).beta w'=loom P' q:= by rw [← hk']; exact fanned _ _ hu -- hk rewrite q? test
  have he:= (hv.2 w').1.sleek S_ hV hS hm hr i (fun i hi=> (hp i hi).le) l'
  filter_upwards [he] with y0 hy; change _ * (∏ i∈p,f i y0)=0
  refine mul_eq_zero.mpr (Or.inr (Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi))) ?_))
  rw [H'] at hy; exact (congr_arg Complex.ofReal hy).trans Complex.ofReal_zero
end Lush
end Bower
end YM.UVExtension.Wick
