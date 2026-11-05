import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Musical
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Pastoral
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pool

/-! Quantitative test integral at exact prices, no law migration. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Puff Push.SectorMeasure Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
namespace Lute
lemma decay_pos {L : Side} : 0 < decay B L X := by unfold decay; split <;> positivity
private lemma raisePrice (n : ℕ) {a b s : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) : (a+b*s^2)^(n+n) ≤ (a+a)^(n+n)*(1+b^(n+n)*s^(2*(n+n))) := by
  let d := n+n
  have hp : 0≤b*s^2 := mul_nonneg hb (sq_nonneg _)
  rw [pow_mul, ← mul_pow]; rcases le_or_gt (b*s^2) 1 with h|h
  · exact (pow_le_pow_left₀ (by positivity) (add_le_add_right (h.trans ha) a) d).trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg hp _)))
  rw [mul_add,mul_one,← mul_pow]; apply le_add_of_nonneg_left' (pow_le_pow_left₀ (by positivity) _ _) (by positivity : 0 ≤ (a+a)^d)
  rw [add_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) h.le) (le_mul_of_one_le_left hp ha)
where le_add_of_nonneg_left' {u v w : ℝ} (h : u≤v) (he : 0≤w) : u≤w+v := h.trans (le_add_of_nonneg_left he)

variable {Γ : Prices G ι → ℝ} (hG : G.Simple) (a : Museum F x A X Y ι) (he : Plays C D P B Pt T x) (hf : Seed B o X f') (hτ : B.supBounds o X f' τ)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ)
include hG he hf hτ hY hu hΓ
lemma vested (U : Config G f) (hV : Healthy P.threshold Y V) (l : List (Directions G c)) (hl : l.length ≤ n) (ha : ∀ A∈l, P.dirBound (S.ratio.parent o) A) (z : Prices G ι) :
    let ρ := rust C D P B S.patch.L X r x u
    ‖leftDerivs (a.concert T u q d k f' Γ U V z) l V‖ ≤ (beat C*τ*decay B S.patch.L X) * (1+ρ^(n+n)*powers z^(2*(n+n))) := by
  intro ρ; have ht := hτ.1
  obtain h := a.choir_band (k:=k) (q:=q) (d:=d) U hG he hf hτ hY hu hΓ hV z
  have hw : 0 ≤ ρ := rust_nn hu; have hc := leading_one C
  let t := leading C+ρ*powers z^2; let p := phrase C; let D' := decay B S.patch.L X
  have h1 : 1 ≤ t := hc.trans (le_add_of_nonneg_right (mul_nonneg hw (sq_nonneg _))); have hp : 0 ≤ p := phrase_nn C; have hd : 0 ≤ D' := decay_pos.le
  calc
    _ ≤ p * D' * t^n * τ * t^n := (h.caps l hl ha).trans (mul_le_mul (mul_le_mul_of_nonneg_right (pay_le hu z) ht)
      ((pow_le_pow_left₀ h.sane (speed_le a hY hf.site hu z) _).trans (pow_le_pow_right₀ h1 hl)) (pow_nonneg h.sane _) (by positivity))
    _ = (p*D'*τ)*t^(n+n) := by rw [pow_add]; ring
    _ ≤ (p*D'*τ)*((leading C+leading C)^(n+n)*(1+ρ^(n+n)*powers z^(2*(n+n)))) := mul_le_mul_of_nonneg_left (raisePrice n hc hw) (by positivity)
    _ = _ := by unfold D' beat p; ring

-- Meter dimension still explicitly attached to conductor and score.
def returnFee (C : Libretto G n) (D : Record) (P B : BudgetPoint) (L : Side) (X : Support f) (r : ℕ) (x u : ℝ) :=
    beat C * decay B L X * (1+(rust C D P B L X r x u)^(n+n) * AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)))

omit hG he hf hτ hY hu hΓ
private lemma meter_nn {Q : ℝ} (hq : 0≤Q) (d k : ℕ) : 0 ≤ AnalyticBridge.LocalGaussian.Moments.meter d 0 Q k := by
  unfold AnalyticBridge.LocalGaussian.Moments.meter; positivity [inflate_ge k (show 0 ≤ Q⁻¹ / 8 by positivity)]
private lemma meter_mono {Q : ℝ} (hq : 0≤Q) {D H : ℕ} (k : ℕ) (h : D ≤ H) :
    AnalyticBridge.LocalGaussian.Moments.meter D 0 Q k ≤ AnalyticBridge.LocalGaussian.Moments.meter H 0 Q k := by
  have hi := inflate_ge k (show 0≤Q⁻¹/8 by positivity)
  unfold AnalyticBridge.LocalGaussian.Moments.meter; gcongr

include he hY hu
lemma hall_general (hw : 0 ≤ τ) (ho : o∈X) {p : Config G c → ℝ} {F : Config G c → Prices G ι → Config G c → ℂ}
    (h' : ∀ V : Config G c, Healthy P.threshold Y V → ∀ l : List (Directions G c), l.length ≤ n → (∀ A∈l,P.dirBound (S.ratio.parent o) A) →
      let g := fun z => leftDerivs (F V z) l V; let μ := Gaussian.cloud (a.twilight k T V)
      Integrable g μ ∧ ((leftDerivs p l V:ℝ):ℂ)=∫ z,g z ∂μ) (hv : ∀ V : Config G c, Healthy P.threshold Y V → ∀ l : List (Directions G c), l.length ≤ n → (∀ A∈l,P.dirBound (S.ratio.parent o) A) →
      ∀ z, let ρ:=rust C D P B S.patch.L X r x u
           ‖leftDerivs (F V z) l V‖ ≤ (beat C*τ*decay B S.patch.L X)*(1+ρ^(n+n)*powers z^(2*(n+n)))) : P.supBounds (S.ratio.parent o) Y p (τ*returnFee C D P B S.patch.L X r x u) := by
  let ρ:=rust C D P B S.patch.L X r x u; let j:=2*(n+n); let b:=beat C*τ*decay B S.patch.L X
  let d':=AnalyticBridge.LocalGaussian.Moments.meter (heads G B S.patch.L X r x) 0 D.K j
  have hρ : 0≤ρ := rust_nn hu
  have hd := decay_pos (L:=S.patch.L) (B:=B) (X:=X); have hbC := beat_nn C; have hb : 0≤b := by unfold b; positivity
  have hQ := D.peak; have h₀ : 0≤d' := meter_nn (by positivity) _ _
  have htrans : τ*returnFee C D P B S.patch.L X r x u = b*(1+ρ^(n+n)*d') := by unfold b returnFee ρ d' j; ring
  rw [htrans]; refine ⟨by positivity,fun V hV l hl hA => ?_⟩
  rw [he.rehearsed.test] at hl
  obtain ⟨hI,hL⟩ := h' V hV l hl hA
  let Q := a.twilight k T V
  have ha := he.cantos (k:=k) a hV hY ho
  rw [← Complex.norm_real,show ((leftDerivs _ _ _:ℝ):ℂ)=_ from hL]; apply (norm_integral_le_integral_norm ..).trans
  obtain ⟨hM,hh⟩ := purchased ∅ (zero_lt_one.trans_le hQ) ha.pos ha.peak j
  change Integrable (fun z => slopeEnvelope ∅ D.K j z) _ at hM
  simp only [slopeEnvelope,load,Finset.sum_empty,mul_zero, Real.exp_zero, mul_one, Finset.card_empty] at hM hh
  have hT := ((integrable_const (1:ℝ)).add (hM.const_mul (ρ^(n+n)))).const_mul b
  calc
    _ ≤ ∫ z, b*(1+ρ^(n+n)*powers z^j) ∂(Gaussian.cloud Q) := integral_mono hI.norm hT (hv V hV l hl hA)
    _ ≤ _ := by
      rw [integral_const_mul,integral_add (integrable_const _) (hM.const_mul _), integral_const, integral_const_mul, probReal_univ,one_smul]
      apply mul_le_mul_of_nonneg_left _ hb; gcongr; exact hh.trans (meter_mono (by positivity) _ (a.viewed hY B ho _))

include hG hf hτ hΓ
lemma hall : P.supBounds (S.ratio.parent o) Y (a.principal T u q d k f' Γ) (τ*returnFee C D P B S.patch.L X r x u) :=
    hall_general a he hY hu hτ.1 hf.site (fun _ hV l hl _ => a.priced_principal hG he hf hτ hY hu hΓ 1 hV l hl) (fun _ hV l hl hA z => vested hG a he hf hτ hY hu hΓ 1 hV l hl hA z)
end Lute
end YM.PhysicalNext.JointLoad.Heir
