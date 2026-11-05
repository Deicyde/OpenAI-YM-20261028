import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Jasper
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Slate
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Verm
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Melange
/-!
# Consume post-L voucher on real physical auxiliary chart. Separate slack and final go, so cost shared
 All on same V. `ruling` exact closure (no log yet) GO2. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {P : Teller G} {c f : Side} {S : StepData c f} {x W K' y σ C σ' C' Λ' e m t v q w : ℝ} {n : ℕ}
variable (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W) (F : Forest S.ratio) (T : Tube G S) (k : S.Choices)
    (A : Before G σ C S.patch.J S.kernel (n+3)) (ρ : Bid.Dir G c→AxisChart G F) (B B' : BudgetPoint) (β : ℝ)
    {D : ℝ}
local notation "M" => A.tables T.high S.patch
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Θ" => Q.table
local notation "G₀" => gStep β
local notation "U" => eaves G L x
local notation "D₀" => furl G L x
local notation "f₁" => Lapis.table F k T.up T.high
local notation "μ" => (Lapis.orbit F ρ)
local notation "g" => Lapis.mist F Q.table T.up
local notation "K" => Lapis.gram F T.up T.high ρ k
local notation "R₀" => Pane.virgin T B β
local notation "V" => (fun x: Xs=> represent (tint G _ x))
variable (E : FiberFee Q.table ((n+3)+1)) (J : BareRates.pre G σ' C' (n+3))
    (he : A.Service F T.high T.up ρ) (hh : Larger (G:=G) S)
    (hr : T.up.Bounds T.high σ C (ConnectedActivityE6.loopBill G L x)) (hz : T.down.Bounds T.low σ' C' Λ')
variable {vC xX:ℝ} (hb : 1 ≤ vC) (hk : (Fintype.card (Joint F G):ℝ) ≤ vC) (hF : (Fintype.card F.Free:ℝ) ≤ vC) (hs : (Fintype.card (Site f):ℝ) ≤ vC)
    (hp : Pigment n (A.tables T.high S.patch) Q.table D (gStep β) xX (eaves G L x) x B.threshold (furl G L x))
    (hL : S.patch.L=L) (hm : 0 < m) (hβ : 0<β) (hB : B.threshold ≤ m)
local notation "K₀" => pam n Q.table T.high S.patch A vC vC E (ConnectedActivityE6.loopBill G L x)
include k E he hh hr hb hk hs hF hp
lemma courtyard : Golf f₁ g μ K n D U U K₀ := by
  have hT : Before.Service.trailCost M (n+3)*U + U*D ≤ (1+ Before.Service.trailCost M (n+3))*U+U*D:= add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hp.top.le) le_rfl
  have hu : eaves G L x ≤ (A.tables T.high S.patch).horizon:=Pigment.horizon hp
  exact illuminates F T.up _ k ρ A E hh hr he Q.table_exists D hp.positive hp.top hp.top hp.small hp.small hu hb hk hs hF (hT.trans_lt hp.initial) (hT.trans_lt hp.one) hp.count

variable (H : ∀ i:S.Choices, ∀ V':Config G c, ∀ z:F.Slice G, Alive S (F.drape z) i → (∀ j: Cell f,toll (F.drape z) j ≤ m) → (∀ b, wire (S.prediction (F.drape z) i) V' b ≤ m) →∃ w : Poll.Body (Precision.Key F G), ‖weld (Precision.Key F G) w‖≤(A.tables T.high S.patch).safety ∧ z=draw F V' w)
    (hV : ∀ z:ℝ, 0≤ z → z ≤ eaves G L x → β*meterQ (A.tables T.high S.patch) n vC*z+(A.tables T.high S.patch).gap/4*D^2 ≤ β*(S.kernel.penalty*m^2/2))
local notation "R" => (ChartPrices.gap (A.tables T.high S.patch) * D^2/4)
include E hm hB H hV hβ
lemma bulks {y:Xs} (hy:‖y‖<U) (U': F.Slice G) (hu: U'∉ staying F (μ y) (G₀) D (V y)) :
    overall F T B β (V y) U' ≤ solar F Q.table β*Real.exp (-coverLog F T Θ k ρ β y+
      (-(Fintype.card F.Free:ℝ)*Real.log (measure_g Q.table β) -R + vC*PathData.loopsPrice B β C (ConnectedActivityE6.loopBill G L x)+ K₀+tapir M vC)) := by
  have he := Fare.overest F T k A ρ Θ B β he hh hr vC hb hk hs D (courtyard Q F T k A ρ B β E he hh hr hb hk hF hs hp) (Pigment.horizon hp) hy hβ m hm hB (fun i => H i (V y)) (hV ‖y‖ (norm_nonneg _) hy.le) _ hu
  apply he.trans_eq; rw [market F]
  let w:= measure_g Q.table β; have hw : 0 < w:=by unfold w measure_g; have ht:= Q.table_exists.scale; have h:= hp.booth; positivity
  rw [show measure_g Q.table β^_=Real.exp ( Fintype.card F.Free* Real.log (measure_g Q.table β)) from (by rw [Real.exp_nat_mul,Real.exp_log hw]), mul_assoc, ← Real.exp_add]
  apply congr_arg; apply congr_arg; ring

include hz J
lemma cooler (X : Coat T F) (HR : Cash W X.x e L Q o t T R₀) (hW:X.x=x) (hw:X.width=o.K) (hM:X.manifest) (hf: B'.threshold=Pressure.temp x) (hh' : (Fintype.card (Site c):ℝ) ≤ vC) (ht' : (Fintype.card (Tubular f G):ℝ) ≤ vC)
    (hy: flags B'.threshold X.V=∅) {y : Xs} (hkY : X.V=V y) (hy' : ‖y‖<U) (ha : ClassicalMatch F T.high T.low T.up T.down ρ) (hμ : 5 ≤ n+3)
    (hX : Real.exp ((↑(c.val^4):ℝ)*Q.overture L e x 0) ≤ (3:ℝ)/2)
    (hc : let C₀:=stocksK G n σ' C' J T.low M; let e:=β*(vC*C₀*‖y‖^5+vC*(C'*B'.threshold^3+C'*B'.threshold^4))+(K₀+tapir M vC+vC*o.ample/2)
          let Yp:= -(Fintype.card F.Free:ℝ)*Real.log (measure_g Q.table β) -R + vC*PathData.loopsPrice B β C (ConnectedActivityE6.loopBill G L x)+ K₀+tapir M vC
          Yp+e+2 ≤ -R/2) : ∃ z:F.Slice G, z ∈ staying F (μ y) G₀ D (V y) ∧∀ i:Cell f,toll (F.drape z) i≤ B.threshold/2:= by
  let i:=HR.laws.intake; let h':= HR.laws.data
  let Yp:=X.χ.profiles G S X.x W h'.W_pos h'.room.fiery
  have hn : 0 < Matter.overhead X R₀ Θ:=Matter.overhead_pos X HR
  have hu : 0 < solar F Q.table β := sun F Θ β hβ Q.table_exists
  let w:= K₀; let u' := -(Fintype.card F.Free:ℝ)*Real.log (measure_g Θ β)-R+vC*PathData.loopsPrice B β C (ConnectedActivityE6.loopBill G L x)+w+tapir M vC; let v:= -coverLog F T Θ k ρ β y
  have hb : ∀ Up, Up∉ staying F (μ y) (G₀) D (V y) → overall F T B β (V y) Up≤ solar F Θ β*Real.exp (v+u'):= fun Up hu=> bulks Q F T k A ρ B β E he hh hr hb hk hF hs hp hm hβ hB H hV hy' Up hu
  apply coolant F T B β Yp (V y) (μ y) P i i.received.temp (mul_pos hu (Real.exp_pos _)).le hb
  have he' :=Pane.lower X HR hw (show flags (Pressure.temp X.x) X.V=∅ from ((by rwa [hW,← hf])))
  rw [show V y=X.V from hkY.symm] -- edit
  apply lt_of_lt_of_le _ he'
  refine lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_left (b:=1/2) ?_ hn.le) -- order
  · have h:=courtyard Q F T k A ρ B β E he hh hr (by assumption) hk hF hs hp
    have H:= bench F T k A ρ X β B B' he hh hr ha hz J hμ hβ HR hM hw _ hkY (hW.symm ▸ hf) (hkY ▸ hy) ((mul_le_mul_of_nonneg_left hy'.le (Uniform.shade_pos G).le).trans_lt hp.shade) hh' ht' hk h hy' (Pigment.horizon hp)
    refine lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_right H (by norm_num))
    rw [mul_assoc]; apply mul_lt_mul_of_pos_left _ hu
    let C₀:= stocksK G n σ' C' J T.low M
    let u:=β*(vC*C₀*‖y‖^5+vC*(C'*B'.threshold^3+C'*B'.threshold^4))+(w+tapir M vC+vC*o.ample/2)
    have hr' : 0<(M).gap:= (A.receipt F k hr hh rfl rfl).1.pos_m
    have hv : 0 ≤ R:=by positivity
    have he : u'+u+2 ≤ -(R)/2 := hc
    change _ < Real.exp (v-u)* (1/2)
    apply lt_of_le_of_lt (Real.exp_monotone (show v+u' ≤ v-u+(-2) by linarith only [he,hv])); rw [Real.exp_add]; apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
    rw [Real.exp_neg,show (1:ℝ)/2=(2:ℝ)⁻¹ by simp] -- edit
    apply inv_lt_inv₀ (Real.exp_pos _) (by norm_num)|>.2; linarith only [Real.add_one_le_exp 2]
  · rw [hW]; linarith only [hX]
end YM.PhysicalNext.Repeat.Sienna
