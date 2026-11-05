import YM.UVExtension.Linden.Petal
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Linden
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat Daisy Willow Wick Wick.Bower
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable {v₁ v₀ b₀ K' w g θ A r B' D d n' n : ℝ} {k j K : ℕ} {χ:Chi}
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
    (M: PhysicalNext.Repeat.Lotus.Leaf R) (hl:Lines R V w (betaF G x L) M)
set_option quotPrecheck false
variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
local notation "bX"=> M.turn.badge S
local notation "Σ"=> parade (ι:=ι) (betaF G x L) g
variable (p:Molecule S) (hp: Healthy (temp X.x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V':E → Config G c} {τ:E}
    (ht: V' τ=X.V)(hV:Mode V' τ j u) (t:F.Slice G × Air f G) (q:Vines ι) -- S α
local notation "cA"=> (pilot M p X A Q.table (W:=W) o.a Q.halo V)
local notation "bA"=> (buffer M p X A Q.table (W:=W) o.a Q.halo V)
local notation "Λ"=> grown (ι:=ι) (betaF G x L) w
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
variable (Y: Mojo Q o L μ A x d v₁ j χ)
variable {m:Molecule S}
variable {U:Mixed.Costs} {z : Vines ι} {hz:z∈parade (betaF G x L) g} (B₀:Lush N hF z hz v₀ U) (h₀:0≤v₀)
local notation "Θ"=> (z none).re
variable {i:ℕ} (hi:i≤j) (Z:Fin i→ E)
local notation "Γ'"=> (F.order G).prod X.dice
local notation "Λx"=> flax (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z
local notation "P'"=> (F.order G).prod (volume : Measure (Body (↥ X')))
local notation "p'"=> foamF (V:=V) (M:=M) (A:=A) (H:=H) (X:=X) (V':=V') (τ:=τ) p Z z
local notation "φ"=> Λx z
include Y N hS hF B₀ h₀ hp hV hX hc hr hm ht hi hl
lemma blastP (k:ℕ) (D0:ℝ) (hh:1≤D0) (hx:Bower.Lush.Shirts o L (radiusB x) D0 (K*j*2) k) (hW:bX∈p) (hs:troupe T R Q.halo (radiusB x) p) :
    let ξo:=(F.order G).prod (volume : Measure (Body (↥ X'))); let d:=∏ i, ‖Z i‖
    Integrable (p') ξo ∧ (∫ y, ‖(p') y‖ ∂ξo) ≤ permag (z none) (X').card * ((D0*(1+v₀+2*(v₁+r))^j*(1+H.shapeW p)^(k+j)*(M.weight*∏ i∈p.erase bX,tabs S U (radiusB x) Q.halo B₀.toll i))*d) := by
  intro ξo d'; let μ:= (F.order G).prod X.dice; let d:= gStep (z none).re; let P:= X'; let M0:=circuit P X.relating
  let F' i:= ‖φ (Prod.fst i, d • Prod.snd i)‖; let g (i:F.Slice G × Body (↥P)):= F' (i.1,spill P i.2)
  have hc' : Measurable (φ):= (glam N hS hF M hl hX hm hc hr p hp ht hV Y B₀ hi Z _ hz).measurable
  have hf:Measurable F':= hc'.norm.comp (show Measurable (fun i:F.Slice G × Air f G=> (i.1,d • i.2)) by fun_prop)
  have hg:Measurable g:= hf.comp (measurable_fst.prodMk ((spill_m P).comp measurable_snd))
  have hY : Measurable (p'):= (bulbs_meas _ _|>.comp measurable_snd).mul (hc'.comp (measurable_fst.prodMk ((spill_m P).comp measurable_snd)))
  have hc0:= (H.laws.data.localP _ X hX hr hm).sails.fullC; have hm':M0.PosDef:= hc0.submatrix Subtype.val_injective
  have ht' : 0 < (z none).re:= B₀.link.laws.intake.positive; have hd : 0< d:= inv_pos.mpr (Real.sqrt_pos.mpr ht')
  let A':= permag (z none) P.card; let v:= Prod.map (id:F.Slice G→F.Slice G) (Pond.swim P)
  have hy : MeasurePreserving v μ ((F.order G).prod (Poll.sweep M0)) := sweeping X P hc0
  obtain ⟨w',hw,h,hβ⟩:= nestling N hS hF M hX hm hc hr p hp ht hV Y B₀ h₀ hW hs k D0 hh hx
  have hD' x' : F' x'≤ w' x'*d' := by
    have hr:= (Brush.offer.mp (hβ x')).inside i hi; unfold F'
    unfold flax; exact (ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right hr (prod_nonneg fun i _=> norm_nonneg _))
  have hR : Integrable F' μ := (hw.mul_const d').mono' hf.aestronglyMeasurable (Eventually.of_forall (fun i=> by rw [Real.norm_of_nonneg (show 0 ≤ F' i from norm_nonneg _)]; exact hD' i))
  have hθ:g∘ v= F':= by
    funext x; apply congr_arg norm
    apply congr_arg (fun k:E [×i]→L[ℝ] ℂ=> k Z) (congr_arg (fun f=> iteratedFDeriv ℝ i f τ) (funext (fun t=> surround (A:=A) hF M hl p z (V' t) hz x.1 (d • spill P (Pond.swim P x.2)) (d • x.2) hX ?_)))
    change d • Pond.swim P (spill P (Pond.swim P x.2))= d • Pond.swim P x.2; rw [Pond.settled]

  have hr' := (hy.integrable_comp hg.aestronglyMeasurable).1 (hθ.symm ▸ hR)
  have hp (x:F.Slice G × Body (↥P)) : ‖p' x‖= A'*tether M0 (z none).re g x:= by
    unfold foamF tether; rw [norm_mul,bulbs M0 x.2 ht']; change _*(permag (z none) (Fintype.card (↥P)))*_= A'*(_ * g (x.1, d⁻¹ • x.2)); unfold g F'; dsimp only; rw [Festa.spilling,smul_inv_smul₀ hd.ne']; simp only [Fintype.card_coe]; unfold A' P; ring
  have hh': Integrable (fun x=> ‖p' x‖) ξo:= by simp_rw [hp]; exact ((gear _ M0 hm' ht' _).1 hr').const_mul _
  refine ⟨(integrable_norm_iff hY.aestronglyMeasurable).1 hh',?_⟩; simp_rw [hp]; rw [integral_const_mul,← axle _ M0 hm' ht',← hy.map_eq, integral_map hy.measurable.aemeasurable hg.aestronglyMeasurable]; change A'*(∫ x, g.comp v x ∂μ)≤ _; rw [hθ]; refine mul_le_mul_of_nonneg_left ((integral_mono hR (hw.mul_const _) hD').trans ?_) (Real.exp_pos _).le
  rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right h (prod_nonneg fun i _ => norm_nonneg _)

end YM.UVExtension.Linden
