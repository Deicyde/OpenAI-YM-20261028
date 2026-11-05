import YM.RemainderComparison.Auxiliary.Park

/-!
 # Raw AUX law(Pane). Conditional real denominator path & exact rescaling.

 Handles polynomials/test coefficients via strongly measurable Banach
 integral on the actual slice. Global support factor checked in weighted
 marker use; here per-supplier, homogeneous estimates. No coefficient
 outside park discarded. No positivity needed for numerator. `actual_l` and
 `nearby_l` retain all normalization costs in same physical β.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aux
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {q : Teller G} {c f : Side} {x W y u D d a A t v : ℝ} {n : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : StepData c f} (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G)
    (k : S.Choices) (ρ : Bid.Dir G c → AxisChart G F) (B : BudgetPoint) (β : ℝ)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun i:Xs=> represent (tint G _ i))
local notation "p" => Lapis.orbit F ρ
local notation "g" => gStep β
local notation "ϕ" => Lapis.table F k T.up T.high
local notation "ψ" => Lapis.mist F Θ T.up
local notation "₥" => Lapis.gram F T.up T.high ρ k
local notation "R₀" => Pane.virgin T B β

-- vector version of compact change, with all choices tracked
omit [CompleteSpace E] in
lemma residence (u : F.Slice G→ E) (hm : LocalRatio Θ)
    (a : Config G c) (y : Y) (hv : 0<v) (h : ∀ z:Y, ‖z‖≤D → windmill F (y+v • z)∈ mouth Θ) (hp : StronglyMeasurable u) :
    ∫ i in staying F y v D a, u i ∂F.order G =v^ Fintype.card (Precision.Key F G) • ∫ z:Y in closedBall 0 D, pay Θ (windmill F (y+v•z)) • u (draw F a (y+v•z)) := by
  let K:=Precision.Key F G; let W:= floorG F a; let Z:=staying F y v D a; let Ω:=Z.indicator u; let Y₀:=closedBall (0:Y) D
  let Qq: LogArray G F.Free → E := (mouth Θ).indicator (fun x=> pay Θ x • Ω (release W x)); have hz x (hx:x∈Z):x∈covered Θ W:= by -- edit ambiguities
    obtain ⟨r,⟨z,hp,rfl⟩,rfl⟩:=hx; rw [← release_image]; exact ⟨_,h z (mem_closedBall_zero_iff.mp hp),rfl⟩
  obtain ⟨-,hx⟩:= release_integral hm W Ω (hp.indicator (staying_meas ..)) (fun y hy=> Set.indicator_of_notMem (mt (hz y) hy) _)
  have hf (f : Y → E) : ∫ z,f z= v^Fintype.card K • ∫ z, f (y+ v • z):= by
    rw [Measure.integral_comp_smul_of_nonneg (hR:=hv.le) volume (fun z=> f (y+z)) v,integral_add_left_eq_self, finrank_euclideanSpace,smul_smul]
    rw [show v ^ Fintype.card K * _=1 from mul_inv_cancel₀ (pow_pos hv _).ne',one_smul]
  rw [← integral_indicator (staying_meas ..),← integral_indicator measurableSet_closedBall]; obtain ⟨e,hK,hζ⟩:=Fare.spinning F (G:=G)
  change (∫ x,Ω x ∂piHaar G _)=_
  rw [show (∫ x,Ω x ∂piHaar G _)=∫ z,Qq z from hx]
  rw [← hK.integral_comp' Qq,hζ,hf (fun y=>Qq (windmill F y))]; apply congr_arg (fun x:E=>v^Fintype.card K • x); apply integral_congr_ae; filter_upwards with z
  by_cases hp:z∈Y₀
  · have hP : draw F a (y+v•z)∈Z:= ⟨_,⟨z,hp,rfl⟩,rfl⟩
    change Qq _=_; unfold Qq; rw [indicator_of_mem (h z (mem_closedBall_zero_iff.mp hp)),indicator_of_mem hp]
    exact congr_arg (pay _ _ • ·) (indicator_of_mem hP _)
  rw [indicator_of_notMem hp]; by_cases he: windmill F (y+v•z)∈mouth Θ
  · have hv' : draw F a (y+v•z)∉Z:= by
      rintro ⟨b,⟨c,hc,rfl⟩,hy⟩; apply hp
      have hR:= release_injOn hm W (h c (mem_closedBall_zero_iff.mp hc)) he hy
      rw [← hζ] at hR; exact (smul_right_injective Y hv.ne' (add_left_cancel (e.injective hR))) ▸ hc
    unfold Qq; rw [indicator_of_mem he]; change _ • Z.indicator u (draw F a (y+v•z))=_; rw [indicator_of_notMem hv',smul_zero]
  exact indicator_of_notMem he _
omit [CompleteSpace E] in
lemma gauze {ι : Type} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) (h:Q.PosDef) (f:Body ι → E) :
    (∫ z, f z ∂sweep Q) = ∫ z, Shield.lens₀ Q z • f z := by
  rw [Shield.magnifies Q h]; have ht : Measurable (fun x=> Shield.lens₀ Q x) := Shield.bulbB (S:=fun _ : Poll.Body ι=>Q) (fun i j=> measurable_const) (z:=id) measurable_id
  rw [integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x=> ENNReal.ofReal (Shield.lens₀ Q x)) from ENNReal.measurable_ofReal.comp ht) (ae_of_all _ (fun x=> ENNReal.ofReal_lt_top))]
  exact integral_congr_ae (ae_of_all _ (fun y=> by dsimp only; rw [ENNReal.toReal_ofReal (Shield.fullFuel Q y).le]))

-- arbitrary multiplier after masking: assumed finite sup on physical group.
structure Actual (H : Config G f→E) (C : ℝ) : Prop where
  bore : StronglyMeasurable H
  gauge : GaugeInvariant H
  rich : ∀ i, ‖H i‖≤C

def inputC (H:Config G f→E) (U:Config G f) := (Pane.virgin T B β).eval U • H U

def alive (V₁:Config G c) (H:Config G f→E) (U:F.Slice G) := Fare.overall F T B β V₁ U • H (F.drape U)
def powder (V₁:Config G c) (H:Config G f→E) := S.push β (inputC T B β H) V₁
def scaled_l (H:Config G f→E) (x:Xs) := (weight T F Θ k ρ β (g•x))⁻¹ • powder T B β (V (g•x)) H

def synced (H:Config G f→E) (U:ℝ × Xs→Y→E) (D:ℝ) (x:Xs) := ∀ z:Y, ‖z‖≤ D → U (g,x) z=H (F.drape (piece F ρ β (g•x) z))
-- always fixed model for Gaussian indication

def combo (U:ℝ×Xs→Y→E) (x:ℝ×Xs) (z:Y) := Germ.primary ϕ ψ p ₥ x z • U x z

section ink
variable (hO:LocalRatio Θ) {H:Config G f→E} {U:ℝ×Positions (Uniform.Primary c G)→Poll.Body (Precision.Key F G)→E} (hf : Intake q T t (Pane.virgin T B β)) {C:ℝ}
variable (hp: Actual H C)
include hf hp
omit [CompleteSpace E] in
lemma inkIn : Integrable (inputC T B β H) (prior G f) ∧ GaugeInvariant (inputC T B β H):= by
  obtain ⟨hx,hh,hq⟩:=hp; have ht:= (R₀).envelope hf.cap; obtain ⟨A,hA⟩:=ht.cost
  refine ⟨Integrable.of_bound ((ht.meas.stronglyMeasurable.smul hx).aestronglyMeasurable) (A*C) ?_,fun s U=>?_⟩ -- edit
  · exact (ae_of_all _ fun i=> by unfold inputC; rw [norm_smul]; exact mul_le_mul (hA _) (hq i) (norm_nonneg _) ((norm_nonneg _).trans (hA i)))
  unfold inputC; rw [hh,lawful_gi hf.cap]
lemma wrote (V₀:Config G c) : StronglyMeasurable (alive T F B β V₀ H) ∧ Integrable (alive T F B β V₀ H) (F.order G) ∧
    powder T B β V₀ H=∫ z, alive T F B β V₀ H z ∂F.order G := by
  have hx:= inkIn T B β hf hp
  have hh:= Fare.amt F T B β t _ hf V₀; have hg:=hh.1.meas
  have hp' : StronglyMeasurable (alive T F B β V₀ H):= hg.stronglyMeasurable.smul (hp.bore.comp_measurable F.continuous_drape.measurable)
  obtain ⟨A,hA⟩:= hh.1.cost
  refine ⟨hp', Integrable.of_bound hp'.aestronglyMeasurable (A*C) (ae_of_all _ fun i=>?_), ?_⟩
  · unfold alive; rw [norm_smul]; exact mul_le_mul (hA _) (hp.rich _) (norm_nonneg _) ((norm_nonneg _).trans (hA i))
  unfold powder; rw [F.pushing (S.isKernel (G:=G) (hf.ready.knobs.symm ▸ hf.ready.kernel) β) _ _ hx.2 hx.1 (fun k U' => S.covary (hf.ready.knobs.symm ▸ hf.ready.kernel) k β U' V₀)]
  apply integral_congr_ae; filter_upwards with z; unfold alive inputC; rw [Fare.total,smul_smul]
include hO
variable {y x:Positions (Uniform.Primary c G)} (ha : Pilot T F Θ k ρ B β D d u a A n (gStep β•x)) (hy:‖gStep β•y‖<d) (hh:‖(gStep β•y)-gStep β•x‖≤u)
    (hJ:synced F ρ β H U D y)
include ha hy hh hJ
lemma integral_stamp : ∫ z in park F ρ β D (g•y), alive T F B β (V (g•y)) H z ∂F.order G = weight T F Θ k ρ β (g•y) • coupon ((₥) 0)⁻¹ (combo T F Θ k ρ U) D (g,y) := by
  let x' := g•y; let V':=V x'; let W:=₥; let L:= ((₥) 0)⁻¹; let σ:=weight T F Θ k ρ β x'; let X' :=closedBall (0:Y) D
  have ht : 0<β := hf.positive
  have hβ := (Fare.gS β ht).1
  have he := ha.signed _ hy hh; have h := ha.core.gram 0 (show ‖(0:Xs)‖<d from norm_zero.trans_lt ha.core.pos)
  have hX z (hx:z ∈X'):= Fare.reserves F T Θ k ρ B β D ha.core ht ha.distance (hf.ready.knobs.symm ▸ hf.ready.kernel) hy (fun i hi l=> he.basis l i hi) hO he.inside he.healthy z hx
  rw [park,residence F Θ _ hO (V (g•y)) ((p) (g•y)) hβ he.inside (wrote T F B β hf hp _).1,← integral_smul,coupon,gauze _ h.1.inv,← integral_smul,← integral_indicator measurableSet_closedBall]; apply integral_congr_ae; filter_upwards with z
  by_cases ht:z∈X'
  · rw [indicator_of_mem ht,velvet,indicator_of_mem ht]
    unfold alive; rw [smul_smul,smul_smul,mul_assoc,hX z ht]; unfold combo; rw [hJ z (mem_closedBall_zero_iff.mp ht),smul_smul,smul_smul,mul_assoc (weight T F Θ k ρ β (g•y))]; rfl
  rw [indicator_of_notMem ht,velvet,indicator_of_notMem ht,smul_zero,smul_zero]

lemma logarithmic_purse :
    ‖scaled_l T F Θ k ρ B β H y - coupon ((₥) 0)⁻¹ (combo T F Θ k ρ U) D (g,y)‖ ≤ remain a D * C := by
  let x':=g • y; let z:=weight T F Θ k ρ β x'; let Y':= park F ρ β D x'; let U':=alive T F B β (V x') H; let X':=coupon ((₥) 0)⁻¹ (combo T F Θ k ρ U) D (g,y)
  let g':= Fare.overall F T B β (V x'); have hβ: 0<β := hf.positive; have hW := wrote T F B β hf hp (V x')
  have hr :0 ≤ C:= (norm_nonneg _).trans (hp.rich 1)
  have hz : 0 < z:= wear_pos T F Θ k ρ β hβ hO x'; have hv:MeasurableSet Y':= staying_meas ..
  have h : scaled_l T F Θ k ρ B β H y=z⁻¹ • (z • X'+∫ i in Y'ᶜ,U' i ∂F.order G):= by
    unfold scaled_l; rw [show powder _ _ _ _ _=_ from hW.2.2,← integral_add_compl hv hW.2.1, integral_stamp T F Θ k ρ B β hO hf hp ha hy hh hJ]
  let f:=∫ i in Y'ᶜ, U' i ∂F.order G
  change ‖_ - X'‖≤_
  rw [h, smul_add, inv_smul_smul₀ hz.ne', add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hz).le]
  have he i : ‖U' i‖ ≤ g' i * C:= by
    have hp' : 0 ≤ g' i := Fare.rays F T B β i (g•y)
    change ‖g' i • H _‖ ≤ _; rw [norm_smul, Real.norm_of_nonneg hp']; exact mul_le_mul_of_nonneg_left (hp.rich _) hp'
  have hy := norm_integral_le_of_norm_le ((Fare.amt F T B β t _ hf (V x')).1.integrable (F.order G) |>.mul_const C|>.restrict (s:=Y'ᶜ)) (ae_of_all _ he)
  apply (inv_mul_le_iff₀ hz).mpr
  rw [integral_mul_const] at hy; apply hy.trans
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (ha.signed x' (by assumption) hh).exterior hr
end ink
end YM.RemainderComparison.Aux
