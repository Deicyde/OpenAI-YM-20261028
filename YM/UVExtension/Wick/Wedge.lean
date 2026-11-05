import YM.UVExtension.Wick.Beryl

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

set_option quotPrecheck false
variable (p:Molecule S) {i:ℕ} (hi:i≤j) (Z:Fin i→ E)
local notation "Φ"=>cockpit X A o.a W p R Q.table Q.halo V
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
local notation "S'"=>parade (ι:=ι) (betaF G x L) g
local notation "Γ'"=> (F.order G).prod X.dice
set_option quotPrecheck false
local notation "p'"=> plated (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z z
local notation "φ"=> blade (τ:=τ) (X:=X) (H:=H) (A:=A) (V:=V) (V':=V') p Z z
include hS N hK he hm hc hr hX hF hV hi
lemma plies (k:ℕ) (U:ℝ) (hh:1≤U) (hx:Bower.Lush.Shirts o L (radiusB x) U (K*j*2) k) (hp:0≤v₀) (hq:Healthy (temp X.x) (H.unionP p) X.V) (hs:troupe T R Q.halo (radiusB x) p) :
    let Y:=(F.order G).prod (volume : Measure (Body (↥ X'))); let d:=∏ i, ‖Z i‖
    Integrable (p') Y ∧ (∫ y, ‖(p') y‖ ∂Y) ≤ permag (z none) (X').card * ((U*(1+v₀+2*r)^j*(1+H.shapeW p)^(k+j)*(∏ i∈p,tabs S J (radiusB x) Q.halo hK.toll i))*d) := by
  intro Y d'; let μ:= (F.order G).prod X.dice; let d:= gStep (z none).re; let P:= X'; let M:=circuit P X.relating
  let F' i:= ‖φ (Prod.fst i, d • Prod.snd i)‖; let g (i:F.Slice G × Body (↥P)):= F' (i.1,spill P i.2)
  have hc' : Measurable (φ):= (shiner N hS hF hX hm hc hr hK he hV p hi Z hq _ hv).measurable
  have hf:Measurable F':= hc'.norm.comp (show Measurable (fun i:F.Slice G × Air f G=> (i.1,d • i.2)) by fun_prop)
  have hg:Measurable g:= hf.comp (measurable_fst.prodMk ((spill_m P).comp measurable_snd))
  have hY : Measurable (p'):= (bulbs_meas _ _|>.comp measurable_snd).mul (hc'.comp (measurable_fst.prodMk ((spill_m P).comp measurable_snd)))
  have ht:= (H.laws.data.localP _ X hX hr hm).sails.fullC; have hm':M.PosDef:= ht.submatrix Subtype.val_injective
  have ht' : 0 < (z none).re:= hK.link.laws.intake.positive; have hd : 0< d:= inv_pos.mpr (Real.sqrt_pos.mpr ht')
  let A':= permag (z none) P.card; let v:= Prod.map (id:F.Slice G→F.Slice G) (Pond.swim P)
  have hy : MeasurePreserving v μ ((F.order G).prod (Poll.sweep M)) := sweeping X P ht
  obtain ⟨w',hw,h,hβ⟩:= Lush.booths N hS hF hX hm hr hK hp he hc hV p hq hs k U hh hx
  have hD' x' : F' x'≤ w' x'*d' := by
    have hr:= (Brush.offer.mp (hβ x')).inside i hi; unfold F'
    unfold blade; exact (ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right hr (prod_nonneg fun i _=> norm_nonneg _))
  have hR : Integrable F' μ := (hw.mul_const d').mono' hf.aestronglyMeasurable (Eventually.of_forall (fun i=> by rw [Real.norm_of_nonneg (show 0 ≤ F' i from norm_nonneg _)]; exact hD' i))
  have hθ:g∘ v= F':= by
    funext x; apply congr_arg norm
    apply congr_arg (fun k:E [×i]→L[ℝ] ℂ=> k Z) (congr_arg (fun f=> iteratedFDeriv ℝ i f τ) (funext (fun t=> hF.confinement hX p hv (V' t) x.1 (d • spill P (Pond.swim P x.2)) (d • x.2) ?_)))
    change d • Pond.swim P (spill P (Pond.swim P x.2))= d • Pond.swim P x.2; rw [Pond.settled]

  have hr' := (hy.integrable_comp hg.aestronglyMeasurable).1 (hθ.symm ▸ hR)
  have hp (x:F.Slice G × Body (↥P)) : ‖p' x‖= A'*tether M (z none).re g x:= by
    unfold plated tether; rw [norm_mul,bulbs M x.2 ht']; change _*(permag (z none) (Fintype.card (↥P)))*_= A'*(_ * g (x.1, d⁻¹ • x.2)); unfold g F'; dsimp only; rw [Festa.spilling,smul_inv_smul₀ hd.ne']; simp only [Fintype.card_coe]; unfold A' P; ring
  have hh': Integrable (fun x=> ‖p' x‖) Y:= by simp_rw [hp]; exact ((gear _ M hm' ht' _).1 hr').const_mul _
  refine ⟨(integrable_norm_iff hY.aestronglyMeasurable).1 hh',?_⟩; simp_rw [hp]; rw [integral_const_mul,← axle _ M hm' ht',← hy.map_eq, integral_map hy.measurable.aemeasurable hg.aestronglyMeasurable]; change A'*(∫ x, g.comp v x ∂μ)≤ _; rw [hθ]; refine mul_le_mul_of_nonneg_left ((integral_mono hR (hw.mul_const _) hD').trans ?_) (Real.exp_pos _).le
  rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right h (prod_nonneg fun i _ => norm_nonneg _)
end Lush
end Bower
end YM.UVExtension.Wick
