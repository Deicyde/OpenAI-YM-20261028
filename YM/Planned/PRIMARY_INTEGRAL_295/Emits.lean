import YM.Planned.PRIMARY_INTEGRAL_295.Purse
import YM.Planned.PRIMARY_INTEGRAL_295.Ripple

/-!
# Normalized J-pr term. Marginal ledger up to common unconfirmed rates

Full quantitative comparison in analytic coordinates of actual inputs
(only usable *if* these costs earned), separated tests working against one
joint tag/noise receipt. `Clock` lower-level receipt on all needed actual
W,ρ variations. As phrased consumed along a path of query calls; cannot
replace the kernel/history. Math propagates normalized bounded stencil
jets. Doesn't certify/emulate the sector/local producer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Emits
open Function Filter Set Metric MeasureTheory Oval Purse Ripple Tones Place
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {E F G Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [MeasurableSpace Ω] {M : Measure Ω} {W : Ω→E→F} {ρ : Ω→E→ℝ} {t : ℝ}
variable {q : E→F} {l k n : ℕ} {x : E} {δ : ℝ}

/-- INDEPENDENT of H; native error variable ε is the x-jet cost on
normalized log links to order k, not the requested Final estimate. `R`
ball hypothesis imposed on contributing z, includes derivatives of the
weight, not a V-mask. -/
structure Clock (M : Measure Ω) (k l : ℕ) (q : E→F) (W : Ω→E→F) (ρ : Ω→E→ℝ) (x : E) (t R : ℝ) (ε : Ω→ℝ) (δ : ℝ) : Prop where
  cores : ∀ᵐ z ∂M, ContDiffAt ℝ k (W z) x ∧ ContDiffAt ℝ k (ρ z) x
  carries : ∀ᵐ z ∂M, 0≤ε z ∧ (Present (ρ z) x k → ‖t • W z x‖≤R ∧ Fuzz x k (W z) q (ε z))
  rates : 0 ≤ δ
  charge : Integrable (fun z=> Purse.due (ρ z) x k (l+k) (ε z)) M ∧ (∫ z,Purse.due (ρ z) x k (l+k) (ε z) ∂M) ≤ δ
  pay : Integrable (fun z=>ρ z x) M ∧ ‖(∫ z,ρ z x ∂M)-1‖≤δ

-- if receipts supply one common higher degree k*, can apply all lower slot
-- orders (does not remove mb_meas).
lemma Clock.radius {ε : Ω→ℝ} {R R' : ℝ} (h : Clock M k l q W ρ x t R ε δ) (hR : R ≤ R') :
    Clock M k l q W ρ x t R' ε δ := by
  refine {h with carries:=?_}
  exact h.carries.mono fun i h=> ⟨h.1,fun h' => ⟨(h.2 h').1.trans hR,(h.2 h').2⟩⟩

def atom (W : Ω→E→F) (ρ : Ω→E→ℝ) (f : F→G) (l : ℕ) (t : ℝ) (z : Ω) (x : E) : G :=
    ρ z x • coat f l t (W z x)

variable [CompleteSpace G]
variable {f : F→G} {u R C : ℝ}

/-- JM moment comparison, pricing receives already normalized f/score jets.
Consequence below of genuine lower-level stationary path data, not of a
history operator with leading action. `δ` includes charge and pay
normalization failures chosen at fixed L, all other constants independent
of t/ L. Does need real derivatives at equality as at all x. -/
lemma forceClock (hq : ContDiffAt ℝ k q x) (hf : ContDiff ℝ ω f) (hu : Envelope x k q u)
    {ε : Ω → ℝ} (hc : Clock M k l q W ρ x t R ε δ) (hS : Regales (atom W ρ f l t) M k x)
    (hb : Width f (k+1) l R C) (ht : t∈Ioc 0 1) (hQ : ‖t • q x‖≤R) :
    Fuzz x k (value (atom W ρ f l t) M) (coat f l t ∘ q) ((2^k+1)*league k l u C*δ) := by
  let H:=coat f l t; let V:=H∘q; let X:=atom W ρ f l t; let L:=league k l u C; let D:=2^k*L
  have hL : 0≤L := prize hu.1 hb.1 ..
  have hD : 0≤D := mul_nonneg (by positivity) hL
  have hA := hc.rates
  have hv : Envelope x k V L := (Oval.sticker hq hq (show Fuzz x k q q 0 from ⟨le_rfl,fun _ _=>by simp⟩) hu hf ht hb hQ hQ).1
  obtain ⟨S,hx,hX⟩:=hS
  refine ⟨by change 0≤(2^k+1)*L*δ; positivity,fun n hn=>?_⟩
  let w := iteratedFDeriv ℝ n V x; let b (z:Ω) := ρ z x; let y := ∫ z,b z ∂M
  let A (z:Ω) := iteratedFDeriv ℝ n (X z) x
  let m:=l+k; let c (z:Ω) := Purse.due (ρ z) x k m (ε z)
  have hF : ∀ᵐ z ∂M, ‖A z-b z • w‖≤D*c z := by
    filter_upwards [hc.carries,hc.cores] with z hz he
    exact coated_badge hq he.1 he.2 hu hf ht hb hn hQ hz.1 hz.2
  have he : ‖(∫ z,A z ∂M)-y • w‖ ≤ D*δ := by
    have hh : y • w =∫ z,b z • w ∂M := (integral_smul_const b w).symm
    have hi : Integrable A M := hX.serves hx hn
    have hz : Integrable b M := hc.pay.1
    rw [hh, ← integral_sub hi (hz.smul_const w)]
    refine (norm_integral_le_of_norm_le (hc.charge.1.const_mul D) hF).trans ?_; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hc.charge.2 hD
  have he' : ‖y • w-w‖ ≤ δ*L := by
    have hh : y • w-w=(y-1) • w := by rw [sub_smul,one_smul]
    rw [hh,norm_smul]; exact mul_le_mul hc.pay.2 (hv.2 n hn) (norm_nonneg _) hA
  change ‖iteratedFDeriv ℝ n (value X M) x - w‖ ≤ (2^k+1)*L*δ
  rw [hX.stirring hx hn]; apply (norm_sub_le_norm_sub_add_norm_sub _ (y • w) _).trans
  exact (add_le_add he he').trans_eq (by unfold D; ring)
end YM.Planned.PrimaryIntegral295.Emits
