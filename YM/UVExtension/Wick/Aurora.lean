import YM.UVExtension.Wick.Classy

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
variable {x y γ W μ δ e b B C d D : ℝ}
lemma bogey (h:0<x) (hz:u∈Set.Ioo (x/2) (2*x)):∃ v:ℝ, v ∈ Set.Ioo (x/2) (2*x) ∧ u/8 ≤ |v-u|:= by
  obtain ⟨hL,hU⟩:=hz; by_cases hu:u ≥ x; refine ⟨5*x/8,⟨by linarith,by linarith⟩,?_⟩
  · rw [abs_of_nonpos (by linarith : 5*x/8-u≤0)]; linarith
  refine ⟨3*x/2,⟨by linarith,by linarith⟩,?_⟩; rw [abs_of_nonneg (by linarith : 0≤3*x/2-u)]; linarith
lemma two_pay {r : ℂ} (_h : u=r.re) (hp: ‖r‖/u ≤ 2) (hq:0<u) (hv:u/8≤|v-u|) :
    v-u ≠ 0 ∧ ‖(r-(u:ℂ))/((v-u:ℝ):ℂ)‖≤24 := by
  have hb:0< |v-u| := by linarith
  refine ⟨abs_pos.mp hb,?_⟩; rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
  apply (div_le_iff₀ hb).2; have hp:‖r‖≤2*u:= (div_le_iff₀ hq).1 hp
  have hf:= norm_sub_le r (u:ℂ); rw [Complex.norm_real,Real.norm_of_nonneg hq.le] at hf; linarith
lemma flicker (t : Finset (Bond f)) (w : Air f G) (hx:0<x) (hp:x/2≤u) (hv:0<v) (hu:v≤2*x) :
    facescale t (scaled v w) ≤2 * facescale t (scaled u w) := by
  have hb:0<u:= by linarith
  have h:(gStep v)⁻¹≤2*(gStep u)⁻¹ := by unfold gStep; rw [inv_inv,inv_inv]; nlinarith [Real.sq_sqrt hb.le,Real.sq_sqrt hv.le,Real.sqrt_nonneg v,Real.sqrt_nonneg u]
  have he : ∑ i∈lensS t G,|scaled v w i|≤2*∑ i∈lensS t G,|scaled u w i| := by
    rw [Finset.mul_sum]; apply sum_le_sum; intro i _; rw [scaled_tip,scaled_tip, abs_mul, abs_mul, abs_of_nonneg (a:=(gStep v)⁻¹), abs_of_nonneg (a:=(gStep u)⁻¹)]
    · rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    all_goals unfold gStep; positivity
  unfold facescale; linarith only [he,Nat.cast_nonneg (α:=ℝ) (lensS t G).card,Nat.cast_nonneg (α:=ℝ) t.card]
lemma scaleV_one (I : Finset (Bond f)) (h:Canary G D C) (z:Air f G) (hv:0<u) : scalp I X X.V u D z=1 := by
  have hh i : steerJ X D (worldZ X u z) X.V i=1 := by unfold steerJ Silica.action; rw [mul_inv_cancel,G.mat_one]; exact Eider.leaves h ..
  unfold Flux.scalp Flux.jacL; dsimp only; rw [prod_eq_one (fun i _=> hh i), Silica.home X h z hv,one_mul]; apply div_self (fullFuel _ _|>.ne')

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z':E} {U:E→Config G c} {j : ℕ}
lemma beads {g f : E→ℝ} (hg : Brush j 1 d g z') (hb:Brush j 1 d f z') -- d declare
    (h : Brush j a 1 Real.log 1) (hp : g z'=1) (hk:f z'=1) (y:E →ℝ)
    (he: ∀ i:E, g i= f i* Real.exp (y i)) : Brush j (j.factorial*a+j.factorial*a) (2*d) y z' := by
  have heq:y=ᶠ[𝓝 z'] fun i=> Real.log (g i)- Real.log (f i):= by
    filter_upwards [hb.smooth.continuousAt.eventually (lt_mem_nhds (show 0<f z' from hk.symm ▸ zero_lt_one))] with i hi
    have hf : 0< f i:=hi; rw [he,Real.log_mul hf.ne' (Real.exp_pos _).ne',Real.log_exp]; ring
  apply Brush.shimmy _ heq; rw [show (2:ℝ)=1+1 by norm_num]; exact (hg.pine (show Brush j a 1 Real.log (g z') by rwa [hp])).separating (hb.pine (show Brush j a 1 Real.log (f z') by rwa [hk]))
lemma tow (I:Finset (Bond f)) (y t:ℝ) (V:E→Config G c) (hp:V z'= X.V) (h:Canary G D C) (w: Air f G) (hy:0<y) (ht:0<t) (hc:t/8≤|y-t|)
    (hv:Brush j 1 b (fun i=> scalp I X (V i) t D (scaled t w)) z') (hV:Brush j 1 b (fun i=> scalp I X (V i) y D (scaled y w)) z')
    (z : ℂ) (hZ : z.re=t) (hx : ‖z‖/t ≤2) (hq:Brush j a 1 Real.log 1) (hr:Brush j e 1 Complex.exp 0) :
    Brush j 1 (b+(1+j.factorial*e)*(1+24*(j.factorial*a+j.factorial*a))*(2*b)) (fun i=> scorched X D I (V i) z w) z':= by
  let f s i:= scalp I X (V i) s D (scaled s w); let P i:= rosined X D I (V i) w; let g v:ℝ:= v
  have hf s (hs:0<s): f s z'=1:= by unfold f; rw [hp]; exact scaleV_one X _ h _ hs -- w scaled
  have he i:f y i=f t i * Real.exp ((y-t)*P i):= by unfold f P; rw [real_ears X D I hy,real_ears X D I ht,mul_assoc, ← Real.exp_add]; congr 2; ring
  have hp:=beads hV hv hq (hf y hy) (hf t ht) (fun i=> (y-t)*P i) he; obtain ⟨hN,hQ⟩:= two_pay hZ.symm hx ht hc
  let fZ i:= (z-(t:ℂ))*(P i:ℂ)
  have ht0:(y-t)* P z'=0:= (Real.exp_eq_one_iff _).mp ((by have hh:= he z'; rw [hf t ht, hf y hy,one_mul] at hh; exact hh.symm))
  have h0 : fZ z'=0:= by unfold fZ; rw [show P z'=0 from (mul_eq_zero.mp ht0).resolve_left hN,Complex.ofReal_zero,mul_zero]
  have hχ : (fun i=> fZ i-fZ z')=fun i=> ((z-t)/((y-t:ℝ):ℂ))*(((y-t)*P i:ℝ):ℂ) := by
    rw [h0]; ext1 i; rw [Complex.ofReal_mul,sub_zero, ← mul_assoc, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hN)]
  have hh:= shimmers (x:=z') (f:=fZ) (v:=24*(j.factorial*a+j.factorial*a)) (d:=2*b) ?_ hr; swap
  · rw [hχ]; exact (scales (rises hp) _).climb (mul_le_mul_of_nonneg_right hQ hp.nonneg) le_rfl
  rw [h0,Complex.exp_zero,norm_one] at hh
  have hT := (rises hv).paints hh; apply (hT.climb (one_mul 1|>.le) (le_of_eq ?_)).shimmy (Eventually.of_forall fun i=> coal X D I ht (V i) w z)
  ring
end YM.UVExtension.Wick
