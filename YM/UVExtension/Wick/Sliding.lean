import YM.UVExtension.Wick.Amber

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

section volume
variable {ι A : Type} [Fintype ι] [DecidableEq ι]
def cloud (M : Matrix ι ι ℝ) (d : ℝ) (x : Body ι) := dotProduct (WithLp.ofLp x) (M⁻¹ *ᵥ WithLp.ofLp x)/2*d
lemma fresh (M : Matrix ι ι ℝ) (x : Body ι) (y : ℝ) : cloud M 1 (y • x) = cloud M (y^2) x := by
  unfold cloud; simp only [WithLp.ofLp_smul,mulVec_smul,dotProduct_smul,smul_dotProduct,smul_eq_mul]; ring
lemma crispyV (M : Matrix ι ι ℝ) (hu:0<u) (x : Body ι) :
    lens₀ M ((gStep u)⁻¹ • x)=lens₀ M x*Real.exp (-(u-1)*cloud M 1 x) := by
  let s:= (gStep u)⁻¹
  let q := -Real.log M.det/2
  let c:= ((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹
  have he x : lens₀ M x=c*Real.exp (q-cloud M 1 x):=by unfold lens₀ cloud c q; simp only [mul_one]
  simp_rw [he, fresh M, pow_two (gStep u)⁻¹,qratio hu]; rw [mul_assoc,← Real.exp_add]; apply congr_arg; apply congr_arg Real.exp; unfold cloud; ring

def lint (u : ℝ) (n : ℕ) := (gStep u)⁻¹^n
lemma lint_real {u : ℝ} (hu:0<u) (n : ℕ) : lint u n=Real.exp (n/2* Real.log u) := by
  unfold lint; unfold gStep; rw [inv_inv]
  calc
    _ = (Real.exp (Real.log u/2))^n := by rw [← Real.log_sqrt hu.le, Real.exp_log (by positivity)]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
lemma lint_pos {u : ℝ} (hu:0<u) (n:ℕ) : 0<lint u n:= by rw [lint_real hu]; positivity

def bulb (M : Matrix ι ι ℝ) (x : Body ι) (y : ℂ) : ℂ :=
    (lens₀ M x:ℂ)* Complex.exp ((Fintype.card ι:ℂ)/2*Complex.log y- (y-1)* (cloud M 1 x:ℂ))
lemma voiced (M : Matrix ι ι ℝ) (x : Body ι) (h:0<u) :
    bulb M x u = (lint u (Fintype.card ι)*lens₀ M ((gStep u)⁻¹ • x):ℝ):= by
  unfold bulb; rw [crispyV _ h, lint_real h]; push_cast; rw [Complex.exp_sub,div_eq_mul_inv]; rw [← Complex.ofReal_log h.le]; simp only [neg_mul, Complex.exp_neg]; ring

def permag (r : ℂ) (n : ℕ) := Real.exp ((n:ℝ)/2 * Real.log (‖r‖/r.re))
lemma bulbs (M : Matrix ι ι ℝ) (x : Body ι) {r : ℂ} (h:0<r.re) : ‖bulb M x r‖=
    lint r.re (Fintype.card ι)*lens₀ M ((gStep r.re)⁻¹ • x) * permag r (Fintype.card ι) := by
  unfold bulb permag
  have hh:0<‖r‖:= h.trans_le (Complex.re_le_norm _); rw [Real.log_div hh.ne' h.ne']
  rw [lint_real h, crispyV _ h]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fullFuel _ _).le,Complex.norm_exp]; norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.mul_im,Complex.log_re]
  rw [mul_left_comm _ (lens₀ M x),mul_assoc,mul_assoc,← Real.exp_add,← Real.exp_add]; congr 2; ring
lemma bulbs_meas (M : Matrix ι ι ℝ) (r : ℂ) : Measurable fun x=>bulb M x r:= by
  apply Measurable.mul (Complex.measurable_ofReal.comp (bulbB (S:=fun _:Body ι=>M) (z:=id) (fun i j=>measurable_const) measurable_id)); refine Complex.continuous_exp.measurable.comp (measurable_const.sub (measurable_const.mul (Complex.measurable_ofReal.comp ?_)))
  unfold cloud Matrix.mulVec dotProduct; fun_prop
lemma bulbs_hol {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] {S:Set A} {r:A→ℂ} (M : Matrix ι ι ℝ) (x : Body ι) (hf : DifferentiableOn ℂ r S) (h:∀ z∈S,0<(r z).re) :
    DifferentiableOn ℂ (fun z=> bulb M x (r z)) S:= ((((hf.clog (fun z hz=> Or.inl (h z hz))).const_mul _).sub ((hf.sub_const _).mul_const _)).cexp).const_mul _

variable [MeasurableSpace A] (μ : Measure A) [SFinite μ] (M : Matrix ι ι ℝ)
    (hp : M.PosDef) (h : 0 < u)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tether (M : Matrix ι ι ℝ) (t : ℝ) (W : A × Body ι → E) (x : A × Body ι) :=
    (lint t (Fintype.card ι) *lens₀ M ((gStep t)⁻¹ • x.2)) • W (x.1,(gStep t)⁻¹ • x.2)
-- real frame on body. 
include hp h
lemma gear (W : A × Body ι → E) : Integrable W (μ.prod (Poll.sweep M)) ↔ Integrable (tether M u W) (μ.prod volume) := by
  let Y:=(volume : Measure (Body ι)); let e:Body ι→ℝ≥0∞:= fun x=>ENNReal.ofReal (lens₀ M x); let f x:=lens₀ M x
  have he : Measurable e := ENNReal.measurable_ofReal.comp (bulbB (S:=fun _:Body ι=>M) (z:=id) (fun i j=>measurable_const) measurable_id)
  let s:=(gStep u)⁻¹; have hs : 0<s:=by unfold s gStep; rw [inv_inv]; positivity
  let T' : Body ι≃ₜ Body ι:= Homeomorph.smul (isUnit_iff_ne_zero.2 hs.ne').unit
  let T : A × Body ι≃ᵐ A × Body ι:= (MeasurableEquiv.refl _).prodCongr T'.toMeasurableEquiv
  let r:=lint u (Fintype.card ι); have hr:0<r:= lint_pos h _
  let Z x:=(fun x : A × Body ι=> f x.2 • W x) x
  have hm : μ.prod (Poll.sweep M) = (μ.prod Y).withDensity (fun x:A×Body ι=>e x.2):= by rw [magnifies _ hp,prod_withDensity_right he]
  have hb : (μ.prod Y).map T= ENNReal.ofReal r⁻¹ • μ.prod Y := by
    rw [show (⇑T)=Prod.map id ((s • ·):Body ι→Body ι) from rfl, ← Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id,Measure.map_addHaar_smul _ hs.ne', Measure.prod_smul_right]
    simp [finrank_euclideanSpace,abs_of_pos (show 0 < (s^ Fintype.card ι)⁻¹ by positivity), Poll.Body]; rfl
  rw [hm, integrable_withDensity_iff_integrable_smul' (show Measurable (fun x:A×Body ι=>e x.2) from he.comp measurable_snd) (Eventually.of_forall fun x=> ENNReal.ofReal_lt_top)]
  have hh : (fun x:A × Body ι=> (e x.2).toReal • W x)=Z:= funext fun i=> by unfold e; rw [ENNReal.toReal_ofReal (fullFuel _ _).le]
  change Integrable (fun x:A×Body ι=> (e x.2).toReal • W x) _ ↔ _; rw [hh]
  have hg : Integrable Z (μ.prod Y) ↔ Integrable (Z ∘ T) (μ.prod Y) := by
    rw [← T.measurableEmbedding.integrable_map_iff, hb]; exact (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).symm
  rw [hg]; have hz : tether M u W = fun x=> r • (Z ∘ T) x:= funext fun x=> mul_smul ..
  rw [hz]; exact (integrable_smul_iff hr.ne' (Z ∘ T)).symm

lemma axle (W : A × Body ι → E) : (∫ x,W x ∂(μ.prod (sweep M)))=∫ x,tether M u W x ∂(μ.prod volume) := by
  let Y:=(volume : Measure (Body ι)); let e:Body ι→ℝ≥0∞:= fun x=>ENNReal.ofReal (lens₀ M x); let f x:=lens₀ M x
  have he : Measurable e := ENNReal.measurable_ofReal.comp (bulbB (S:=fun _:Body ι=>M) (z:=id) (fun i j=>measurable_const) measurable_id)
  let s:=(gStep u)⁻¹; have hs : 0<s:=by unfold s gStep; rw [inv_inv]; positivity
  let T' : Body ι≃ₜ Body ι:= Homeomorph.smul (isUnit_iff_ne_zero.2 hs.ne').unit; let T : A×Body ι ≃ᵐ A×Body ι := (MeasurableEquiv.refl _).prodCongr T'.toMeasurableEquiv
  let r:=lint u (Fintype.card ι); have hr:0<r:=lint_pos h _; let Z x:=(fun x:A×Body ι=> f x.2 • W x) x
  have hm : μ.prod (Poll.sweep M)=(μ.prod Y).withDensity (fun x:A×Body ι=> e x.2):= by rw [magnifies _ hp,prod_withDensity_right he]
  have hb : (μ.prod Y).map T=ENNReal.ofReal r⁻¹ • μ.prod Y:= by
    rw [show (⇑T)=Prod.map id ((s • ·):Body ι → Body ι) from rfl, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, Measure.map_addHaar_smul _ hs.ne', Measure.prod_smul_right]
    simp [finrank_euclideanSpace,abs_of_pos (show 0 < (s^ Fintype.card ι)⁻¹ by positivity), Poll.Body]; rfl
  have he' (x:A×Body ι) : (e x.2).toReal • W x=Z x:= by unfold e; rw [ENNReal.toReal_ofReal (fullFuel _ _).le]
  rw [hm,integral_withDensity_eq_integral_toReal_smul (show Measurable (fun x:A×Body ι=>e x.2) from he.comp measurable_snd) (Eventually.of_forall fun x=> ENNReal.ofReal_lt_top)]
  simp_rw [he']; have hf x : tether M u W x=r • Z (T x):= mul_smul ..
  simp_rw [hf]; change _= ∫ x, r • Z (T x) ∂(μ.prod Y)
  rw [integral_smul,← integral_map_equiv,hb,integral_smul_measure,ENNReal.toReal_ofReal (inv_pos.mpr hr).le, smul_inv_smul₀ hr.ne']
end volume
end YM.UVExtension.Wick
