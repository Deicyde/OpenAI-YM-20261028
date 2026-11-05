import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Lush
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Crone
/-!
# Use real vouchers: on x0 radius all(s).
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
variable (H : ∀ i:S.Choices, ∀ V':Config G c, ∀ z:F.Slice G, Alive S (F.drape z) i → (∀ j: Cell f,toll (F.drape z) j ≤ m) → (∀ b, wire (S.prediction (F.drape z) i) V' b ≤ m) →∃ w : Poll.Body (Precision.Key F G), ‖weld (Precision.Key F G) w‖≤(A.tables T.high S.patch).safety ∧ z=draw F V' w)
    (hV : ∀ z:ℝ, 0≤ z → z ≤ eaves G L x → β*meterQ (A.tables T.high S.patch) n vC*z+(A.tables T.high S.patch).gap/4*D^2 ≤ β*(S.kernel.penalty*m^2/2))
local notation "R" => (ChartPrices.gap (A.tables T.high S.patch) * D^2/4)
include E hm hB H hV hβ
lemma rule_it (ZH : Intake P T x R₀) {z:Xs} (ht : ‖z‖<U)
    (hy : ∀ i:Y,‖i‖≤D → flags B.threshold (F.drape (draw F (V z) (μ z+G₀ • i)))=∅)
    (hc : -(Fintype.card F.Free:ℝ)*Real.log (measure_g Q.table β)-R+vC*PathData.loopsPrice B β C (ConnectedActivityE6.loopBill G L x)+ K₀+tapir M vC ≤ -R / 2) :
    let v:=ratify f₁ g μ K D (G₀,z)
    let t:=solar F Θ β* Real.exp (-coverLog F T Θ k ρ β z)
    S.push β (R₀).eval (V z)-t*v∈ Set.Icc 0 (t*Real.exp (-R / 2)) := by
  intro v' t'; let Y':= staying F (μ z) G₀ D (V z); let G':= overall F T B β (V z)
  have hp' := courtyard Q F T k A ρ B β E he hh hr hb hk hF hs hp; have h' := amt F T B β x P ZH (V z)
  have hc' : (1+Before.Service.trailCost M (n+3))*U + G₀*D < (M).initial:= lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_of_nonneg_right hp.lease.le hp.positive)) hp.initial
  have hY: Uniform.shade G*(Before.Service.trailCost M (n+3)*U + G₀ *D) < Q.table.radius := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hp.lease.le hp.positive)) (Uniform.shade_pos G).le) (hp.count.trans_lt (half_lt_self Q.table_exists.patch))
  have hv: ∫ i in Y', G' i ∂F.order G=t'*v':= pricing F T Θ k ρ B β D hp' hβ hp.lease hh.1 ht (Fare.gamma F T k A ρ he hh hr hp.horizon hp.booth ht hc') Q.table_exists (mouthF F T k A ρ he hh hr hp.horizon Θ hY hp.booth ht) hy (h'.1.meas.stronglyMeasurable)
  have hX:0< solar F Q.table β:= sun F Q.table β hβ Q.table_exists; have hz :0<t':= mul_pos hX (Real.exp_pos _)
  have hx : S.push β (R₀).eval (V z)=t'*v'+ ∫ i in Y'ᶜ,G' i ∂F.order G:= by rw [h'.2, ←hv]; exact (integral_add_compl (staying_meas ..) (h'.1.integrable _)).symm
  rw [hx,add_sub_cancel_left]; refine ⟨setIntegral_nonneg (staying_meas ..|>.compl) (fun i _=> rays F T B β i z),outside_est F T B β _ _ P ZH (by positivity) (fun i hi=> ?_)⟩
  apply (bulks Q F T k A ρ B β E he hh hr hb hk hF hs hp hm hβ hB H hV ht i hi).trans
  unfold t'; rw [mul_assoc,← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (add_le_add le_rfl hc)) hX.le
end YM.PhysicalNext.Repeat.Sienna
