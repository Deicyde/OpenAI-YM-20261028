import YM.Bid.Fetch
import YM.Further.DENSE_MIXED_KERNELS.Portions
import YM.Further.DENSE_MIXED_KERNELS.Score
import YM.Work.A05.Window
import YM.Work.B09.Shell


/-!
# First-system integral with ANY sized word of sources held

Vacuum/protector assumptions here are on **individual factors**, before
expectations, under the precise law, with fourth-budget growth/trigger
control allowed. No condition on independence of any events. Apply even
when same physical argument or marker/control budget is reused, by proving
these hypotheses on the SAME word; the fourth budgets must count it.
Proof also for empty alphabets in service of variants with separate exterior
offsets; use nonempty for the connected estimates. This is the V-jet part.

Held arguments in `z` include *all* predicate calls on incoming H/K marked
coefficients. No derivatives of those. Later files get actual z,M.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module Port Gaussian Surface
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {U : Config G n} {M t : ℝ} {k : ℕ}
section generic
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Hard amplitude can be arbitrary bounded measurable. Not even assuming
measurable as fn of hypothetical plateaus absent in this component. -/
lemma Varies.insulate {f : X → Config G n → ℂ} {g : X → ℂ} (h : Varies μ k U f) (hf : Measurable g)
    (hp : 0≤M) (he : ∀ i,‖g i‖≤ M) : Varies μ k U (fun i v => g i * f i v) := by
  obtain ⟨s,hs,h⟩ := h
  obtain ⟨b,hb,hb'⟩ := h.holds
  let L (i : X) := ContinuousLinearMap.mul ℝ ℂ (g i)
  refine ⟨s,hs,h.territory,fun i => (L i).contDiff.comp_contDiffOn (h.smooth i),
    fun _ hy => hf.aestronglyMeasurable.mul (h.meas _ hy),fun i => M*b i, hb.const_mul _,
    fun i v hv j hj => ?_⟩
  have hL : ‖L i‖ ≤ M := by
    apply (L i).opNorm_le_bound hp
    intro z
    change ‖g i*z‖≤_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (he i) (norm_nonneg _)
  exact ((L i).norm_iteratedFDeriv_comp_left (h.territory.contDiffOn_iff.mp (h.smooth i) hv) (Nat.cast_le.mpr hj)).trans
    (mul_le_mul hL (hb' i v hv j hj) (norm_nonneg _) hp)

lemma complexCost {f : Config G n → ℝ} {P : Directions G n → Prop} (h : Pitch f U P k M t) :
    Pitch (fun x => (f x:ℂ)) U P k M t := by
  rw [show M= (1:ℝ)*M by rw [one_mul]]; exact h.linear Complex.ofRealCLM (fun x => by simp) zero_le_one
end generic

variable {ι κ Ω α : Type} [Fintype ι] [Fintype κ] [Fintype α] [MeasurableSpace Ω]
    {A : ChartRatio G} {H : Port A} {μ : Measure Ω} {W : Config G n→Surface H ι κ Ω}
    {P : Directions G n → Prop} {c C g : ℝ}
local notation "X" => H.front ι (H.Room κ)
local notation "Y" => Ω × H.back ι (H.Room κ)

/-- Kernel-only tests from the unmarked integrals, but required even
for the word sizes/read sets of this marked situation. At evaluation. -/
structure Glides (W : Config G n→Surface H ι κ Ω) (U : Config G n) (g t : ℝ) (k : ℕ) (P : Directions G n→Prop)
    (c C : ℝ) : Prop where
  legal : (W U).Valid
  firm : ∀ i x, c * ‖x‖^2 ≤ (W U).B i x x
  smooth : Shifts W U P k g t
  matrix : ∀ i, Pitch (fun v=> (W v).B i) U P k C t

variable {f : α → Config G n → Ω × H.back ι (H.Room κ) → ℂ} {b : α→ℝ}

def whole (W : Config G n→Surface H ι κ Ω) (f : α → Config G n → Ω × H.back ι (H.Room κ) → ℂ) (g : ℝ) (y : Ω × H.back ι (H.Room κ))
    (u : Config G n) : ℂ := (W u).confirm g y • (∏ i,f i u y)

/-- `blank` is the end-protector of the held chart. Doesn't assert an
analytic derivative computation through an output switch.
`controls` product budgets include ratios and trigger shares (see Portions)
when needed, or can prove directly with one (Fourths.empty).
`pulses`: through *output* tested directions and at common anchor.
Amount depends on the spell of the word via independent cost b; can
use scales with q fixed before stage to allow unbounded velocities in z.
`charter`: neighborhood control; no arithmetic bound but still needs
real proof for the kernel and these factors. Includes extensions of the
sector calculations for an unforced term. -/
structure Arc (W : Config G n→Surface H ι κ Ω) (μ : Measure Ω) (f : α → Config G n → Ω × H.back ι (H.Room κ) → ℂ) (U : Config G n)
    (P : Directions G n → Prop) (b : α→ℝ) (k q : ℕ) (g t : ℝ) : Prop where
  blank : ∀ y∉ (W U).Perch, ∀ᶠ v in 𝓝 0, whole W f g y (increment U v)=0
  controls : ∃ R L : α → Ω × H.back ι (H.Room κ)→ℝ, Fourth ((W U).aboard μ g) R ∧ Fourth ((W U).aboard μ g) L ∧
    ∀ i p, p ∈ (W U).Perch → Pitch (fun v=> f i v p) U P k (b i*R i p*L i p) (t * (W U).tower g p ^ q)
  charter : Varies (ambient H ι κ μ) k U (whole W f g)

def flight (H : Port A) (s z d k : ℕ) (t c C : ℝ) := 1+s*t+tally H z d k t c C

def billed (H : Port A) (s z d k q : ℕ) (t c C : ℝ) := (flight H s z d k t c C)^k * (2+expense d ((q+2)*k*2) c)


/-- Absolute integrals and genuine derivatives. `k` arbitrary output
order, `M` still uncolored (no duties). -/
theorem Arc.evaluate [IsProbabilityMeasure μ] {q : ℕ} (hw : Glides W U g t k P c C) (h : Arc W μ f U P b k q g t)
    (hc : 0<c) (hC : 1≤C) (hg : 0<g) (hv : g≤1) (ht : 0≤t) (hb : ∀ i,0≤b i)
    (z : Y → ℂ) (he : Measurable z) (hm : 0≤M) (hM : ∀ y, ‖z y‖≤M) :
    Pitch (fun v => ∫ y,z y * whole W f g y v ∂ambient H ι κ μ) U P k
      (M*(∏ i,b i)*billed H (Fintype.card α) (Fintype.card ι) (finrank ℝ X) k q t c C) 1 := by
  have ha := hw.legal
  obtain ⟨R,L,hR,hL,Hl⟩ := h.controls
  let d := finrank ℝ X; let l₀ := tally H (Fintype.card ι) d k t c C
  let D := flight H (Fintype.card α) (Fintype.card ι) d k t c C
  have hu : 0 ≤ l₀ := tally_pos _ _ _ _ hc (zero_le_one.trans hC) ht
  have hfix : 0 ≤ (Fintype.card α:ℝ)*t := mul_nonneg (Nat.cast_nonneg _) ht
  have hD : 1≤D := by change 1≤1+_+l₀; linarith
  let Xr y := (∏ i,R i y); let Xt y := (∏ i,L i y)
  let Q y := (W U).confirm g y; let K := M*∏ i,b i
  have hK : 0≤K := mul_nonneg hm (Finset.prod_nonneg fun i _ => hb i)
  let m y := (W U).tower g y
  let F y v := z y * whole W f g y v
  have hQ y : 0 ≤ Q y := ha.confirm_nonneg g hg y
  let weight y := Q y * (Xr y * Xt y * m y ^ ((q+2)*k))
  have hF := h.charter.insulate he hm hM
  obtain ⟨hI,(hh : (∫ y,weight y ∂ambient H ι κ μ) ≤ 2+_)⟩ := hR.allow hL ha hg hc hw.firm ((q+2)*k)
  refine ⟨hF.integrate, fun l hl hD' => ?_⟩
  rw [Varies.turns hF l hl]; apply (norm_integral_le_integral_norm _).trans
  change (∫ i,‖leftDerivs (F i) l U‖ ∂ambient H ι κ μ) ≤ K * _ * _
  have hx (y) : ‖leftDerivs (F y) l U‖ ≤ K * D^k * weight y := by
    by_cases hp : y ∈ (W U).Perch
    ·
      let s := Fintype.card α
      have hm' : 1≤m y := le_add_of_nonneg_right (norm_nonneg _)
      have he : Pitch (fun V => ∏ i,f i V y) U P k ((∏ i,b i)*Xr y*Xt y) (s*(t*m y^q)) := by
        have he := Pitch.joint Finset.univ (fun i (_:i∈(Finset.univ:Finset α)) => Hl i y hp)
        simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, ← Finset.prod_mul_distrib,Xr,Xt] using! he
      have hc' : Pitch (fun v => ((W v).confirm g y:ℂ)) U P k (Q y) (l₀*m y^2) := complexCost
        (chart_pitch hw.smooth hg (by assumption : g≤1) ht hc hC hw.firm hw.matrix hp)
      have hG := Pitch.complex_mul ( (Pitch.fixed (U:=U) (P:=P) (k:=k) (z y) (le_refl 0)).mono (hM y) (le_refl 0) (le_refl 0) ) (Pitch.complex_mul hc' he)
      have h : Pitch (F y) U P k (Q y * (K*Xr y*Xt y)) (D * m y^(q+2)) := by
        unfold F whole; simp_rw [Complex.real_smul]
        apply hG.mono
        · apply le_of_eq; unfold K; ring
        · rw [zero_add]; positivity
        rw [zero_add]
        calc
          _ ≤ l₀*m y^(q+2) + s*(t*(m y)^(q+2)) := by gcongr <;> omega
          _ = (l₀+s*t)*(m y)^(q+2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (by change l₀+ (s:ℝ)*_≤1+(s:ℝ)*_+l₀; linarith) (by positivity)
      apply (h.bounds l hl hD').trans; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le
        hD (one_le_pow₀ hm')) hl) h.pos)
      unfold weight; apply le_of_eq; rw [mul_pow (n:=k),pow_mul]; ring
    have hz : (F y)∘increment U =ᶠ[𝓝 0] (fun _ => (0:ℂ)) ∘ increment U := by
      filter_upwards [h.blank y hp] with v hv; dsimp only [Function.comp_apply,F]; rw [hv,mul_zero]
    have h0 := left_eq l hz
    have hg := (Pitch.fixed (U:=U) (P:=P) (k:=k) (0:ℂ) (le_refl 0)).bounds l hl hD'
    rw [h0]; simp only [norm_zero,zero_mul] at hg
    apply hg.trans
    unfold weight
    have hp' : Q y=0 := if_neg hp
    rw [hp',zero_mul,mul_zero]
  refine le_trans (integral_mono (hF.post l (show 0+l.length ≤ k by omega)).reads.norm
    ((show Integrable weight _ from hI).const_mul (K * D^k)) hx) ?_
  rw [one_pow,mul_one,integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans (le_of_eq (by unfold billed; change K * D^k * _= K*(D^k *_); ring))
end YM.Further.DenseMixedKernels
