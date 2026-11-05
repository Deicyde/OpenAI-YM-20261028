import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Vetting
import YM.RemainderComparison.Auxiliary.Purse

/-!
 # Coarse-data derivatives without transporting the exterior domain

 O(β^C) estimates normalized by Solar, *same* denominator density
 (not global partition). Permits interpolation on moving mask splice.
 Actual fine field H evaluated AS IS, no derivative. Value-small germ
 estimates apply separately. Used also on scalar/log ratio ancestors
 after registration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aux
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {q : Teller G} {c f : Side} {x u s D d a A t v β : ℝ} {n j m : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : StepData c f} (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G)
    (k : S.Choices) (ρ : Bid.Dir G c → AxisChart G F) (B : BudgetPoint) (β : ℝ)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun i:Xs=> represent (tint G _ i))
local notation "g" => gStep β
local notation "R₀" => Pane.virgin T B β
local notation "Ω" => Fare.solar F Θ β
local notation "₾" => Aux.weight T F Θ k ρ β
local notation "θ" => coverLog F T Θ k ρ β
local notation "Ξ" => Germ.primary (Lapis.table F k T.up T.high) (Lapis.mist F Θ T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k)
variable {H:Config G f→E} (hf : Intake q T t (Pane.virgin T B β))
variable {C:ℝ} (hp: Actual H C)

omit [NormedSpace ℝ E] in
lemma Actual.price (hp : Actual H C) : 0 ≤ C := (norm_nonneg _).trans (hp.rich 1)
omit [NormedSpace ℝ E] in
lemma Actual.unit (v : E) : Actual (f:=f) (G:=G) (fun _=> v) ‖v‖:= ⟨stronglyMeasurable_const,fun _ _=>rfl,fun _=>le_rfl⟩
lemma trunk [CompleteSpace E] (h: E) (w:Config G c) : powder T B β w (fun _=> h)=(S.push β (R₀).eval w) • h := by
  unfold powder inputC StepData.push; simp_rw [smul_smul,smul_eq_mul]; rw [integral_smul_const]

include hf hp
variable [CompleteSpace E]
variable {N R C' : ℝ} (he : PaintSupply G j C')
    (hi : (Fintype.card (Bond c) : ℝ) ≤ N) (hr : Brush j R 1 Real.exp 0)
local notation "ℓ" => prime G S.kernel j C' R β N
include he hi hr

include F
lemma sprays (x:Xs) (hx : ‖x‖<1) : Brush j ((C*3^j*ℓ)*tramp T B β x) 1 (fun y=> powder T B β (V y) H) x:= by
  let A y:= alive T F B β (V y) H
  have hf' y:= Fare.amt F T B β t q hf (V y); let W (x:Xs) := overall F T B β (V x)
  have hh i := wrote T F B β hf hp (V i)
  have hβ : 0<β := hf.positive
  let f z:= C*3^j*ℓ*W x z
  have hC:= hp.price; have ht : 0≤ℓ:= (primeN S.kernel hβ (le_refl _) hr.nonneg he.1.le ((Nat.cast_nonneg _).trans hi)).1
  have hv z y (hy:‖y‖<1) : Brush j (C*3^j*ℓ*W y z) 1 (fun y=> A y z) y:= by
    have ha:Brush j C 1 (fun _ : Xs=> H (F.drape z)) y := (Brush.certified zero_le_one _).climb (hp.rich _) le_rfl
    have hh: (ℓ*W y z)*C*3^j=C*3^j*ℓ*W y z:= by ring
    exact (Trace.paint (volumeQ F T B β z he hi _ hy.le hr) ha).climb hh.le le_rfl
  have hz : Integrable f (F.order G) := ((hf' x).1.integrable _).const_mul _
  have hQ' : ∃ T:ℝ, ∀ y z, W y z≤T:= by
    obtain ⟨d,hd⟩:= S.density_bound (hf.ready.knobs.symm ▸ hf.ready.kernel) β
    obtain ⟨v,hv⟩:= ((Pane.virgin T B β).envelope hf.cap).cost
    refine ⟨|d| *|v|,fun y z=>?_⟩; unfold W; rw [Fare.total]; apply mul_le_mul ((hd ..).trans (le_abs_self _)) ((le_abs_self _).trans ((hv _).trans (le_abs_self _))) _ (abs_nonneg _); rw [Pane.sparkling]; split <;> positivity
  obtain ⟨q,hq⟩:=hQ'
  have hδ : Meristem A x (F.order G) j:= by
    refine Relative.test_domination (M:=fun _=> (C*3^j*ℓ)*q) (integrable_const _) ?_ (Eventually.of_forall fun y=> (hh y).1)
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy z
    exact (hv z y hy).climb (mul_le_mul_of_nonneg_left (hq y z) (by positivity)) le_rfl
  exact (hδ.buds f hz zero_le_one (by rw [show tramp T B β x=∫ i,W x i ∂F.order G from (hf' x).2,← integral_const_mul]) (ae_of_all _ fun z=> hv z x hx)).shimmy (Eventually.of_forall fun y=> (hh y).2.2)

variable (hO : LocalRatio Θ) {y x:Positions (Uniform.Primary c G)} (hP : Pilot T F Θ k ρ B β D d u a A n (gStep β • x)) (hx: ‖gStep β • y‖ < d) (hh: ‖gStep β • y-gStep β • x‖ ≤ u)
omit hp he hi hr
include hO hP hx hh
lemma temper (hU : Brush n v 1 (Germ.coupon ((Lapis.gram F T.up T.high ρ k 0)⁻¹) Ξ D) (g,y)) :
    (₾ (g • y))⁻¹*tramp T B β (g•y) ≤ v+1 := by
  have hs : Actual (G:=G) (f:=f) (fun _=> (1:ℝ)) 1:= by simpa only [norm_one] using Actual.unit (E:=ℝ) 1
  let K:= (fun (_:ℝ×Xs) (_:Y) => (1:ℝ)); let V':= coupon ((Lapis.gram F T.up T.high ρ k 0)⁻¹) (Ξ) D; let z:=₾ (g•y)
  have hf := logarithmic_purse T F Θ k ρ B β hO hf hs hP hx hh (show synced F ρ β _ K D y from fun _ _=> rfl)
  have h : remain a D*1 ≤ 1 := by unfold remain; rw [mul_one]; exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by have ha:= hP.gap; positivity)) (by norm_num))
  have ht : combo T F Θ k ρ K=(Ξ) := funext fun i=> funext fun r=> by unfold combo; simp only [K,smul_eq_mul,mul_one]
  rw [ht, Aux.scaled_l, trunk T B, smul_eq_mul, smul_eq_mul,mul_one] at hf
  change z⁻¹ * tramp T B β (g•y) ≤ _; have hg: z⁻¹ * tramp T B β (g•y)-V' (g,y)≤1:= (le_abs_self _).trans (hf.trans h)
  linarith only [hg,(le_abs_self (V' (g,y))).trans hU.bound]
include hp he hi hr
omit hh
lemma drenched (hm : j≤n) {u':ℝ} (hv : (₾ (g • y))⁻¹*tramp T B β (g•y) ≤ u') : Brush j
    (clump j (oat j A β + oat j A β) R * ((C*3^j*ℓ)*u')*3^j)
    1 (scaled_l T F Θ k ρ B β H) y := by
  let V' := (fun y=>powder T B β (V y) H); let φ x:= ₾ (g • x); let φ' x:= φ y*(φ x)⁻¹; let f' x:= (φ y)⁻¹ • V' (g • x)
  have hβ:0<β := hf.positive; let X:=g• y
  let L:= g • ContinuousLinearMap.id ℝ Xs
  have hv' : ‖L‖≤1:= by
    unfold L; rw [norm_smul,Real.norm_of_nonneg (Fare.gS β hβ).1.le]
    exact (mul_le_of_le_one_right (Fare.gS β hβ).1.le ContinuousLinearMap.norm_id_le).trans (hP.distance.le.trans hP.core.small)
  have ht : 0<φ y := wear_pos T F Θ k ρ β hβ hO _
  have he' (u':Xs): φ' u'=Real.exp (θ (L u')-θ (g•y)) := by
    have hh:0<Ω:= Fare.sun F Θ β hβ hO
    unfold φ' φ Aux.weight; rw [_root_.mul_inv_rev]; simp only [Real.exp_neg,inv_inv]; change _=Real.exp (θ (g•u')- _); rw [Real.exp_sub]; field_simp
  have hk := octane F T Θ ρ β k hm hx hP.core hβ
  have hb := Brush.reading L (x:=y) hk hv'; rw [one_mul] at hb
  have hφ : Brush j (clump j (oat j A β + oat j A β) R) 1 φ' y:= by
    rw [funext he']; exact Lantern.composite («g»:=Real.exp) hb (show Brush j R 1 Real.exp (θ (L y)-θ (g•y)) from (by change Brush j _ _ _ (_-θ X); rw [show θ (L y)=θ X from rfl, sub_self]; exact hr))
  have ht' :0≤ℓ:= (primeN S.kernel hβ (le_refl _) hr.nonneg he.1.le ((Nat.cast_nonneg _).trans hi)).1
  have hU : 0 ≤ C:= hp.price; let k:= C*3^j*ℓ
  have hs := Brush.reading L (x:=y) (sprays T F B β hf hp he hi hr (L y) (hx.trans_le hP.core.small)) hv'; rw [one_mul] at hs
  have hF := hs.smul (φ y)⁻¹; rw [Real.norm_of_nonneg (inv_pos.mpr ht).le,mul_left_comm] at hF
  have hh := (Trace.paint hφ (show Brush j (k*u') 1 f' y from hF.climb (mul_le_mul_of_nonneg_left hv (by positivity)) le_rfl))
  refine hh.shimmy ?_; filter_upwards with i
  unfold scaled_l; change (φ i)⁻¹ • V' _=φ' i • f' i; unfold φ' f'
  rw [smul_smul,mul_comm (φ y),mul_assoc,mul_inv_cancel₀ ht.ne',mul_one]
end YM.RemainderComparison.Aux
