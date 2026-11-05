import YM.Further.DENSE_MIXED_KERNELS.Moments
import YM.Further.DENSE_MIXED_KERNELS.Tracks


/-!
# FKer's relative jet budget through a complete mixed occurrence

Use on the reindexed kernel with patches throughout a single physical
sector component. **Not** on Healthy varying across a boundary but with a
formula turning off when Healthy fails there! Larger integrable dominations
in open neighborhoods needed too. See Window, Arc (later file).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels.Surface
open Filter Function Set MeasureTheory Lattice RG Wilson Precision Module Port Gaussian
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {ι κ Ω : Type} [Fintype ι] [Fintype κ]
    {A : ChartRatio G} {H : Port A} {S : Surface H ι κ Ω} {n : Side}
    {W : Config G n → Surface H ι κ Ω} {U : Config G n} {P : Directions G n → Prop}
    {g T c C : ℝ} {k : ℕ} {p : Ω × H.back ι (H.Room κ)}

local notation "Y" => H.back ι (H.Room κ)
local notation "X" => H.front ι (H.Room κ)

def pen (H : Port A) (k : ℕ) (t : ℝ) := 2^k*(curve H k (curve H k t))

lemma pen_pos (H : Port A) (k : ℕ) {t : ℝ} (ht : 0≤t) : 0 ≤ pen H k t := by unfold pen curve; have he := H.cash k; positivity

/-- Once per link of the held table. Log of actual normalized Haar ratio. -/
lemma oneCoin (h : Shifts W U P k g T) (hp : p∈ (W U).Perch) (hg : 0<g) (hy : g≤1) (ht : 0≤T) (i : ι) :
    let f := fun v => (A.scale*A.J ((W v).arc p i))⁻¹
    Pitch f U P k (f U) (pen H k T) := by
  intro f
  let a (x) := (W x).arc p i
  have he (v) (hp : p∈(W v).Perch) : a v∈H.accepts := H.heard_mem hp i (Set.mem_univ i)
  have hx (v) (hp : p∈(W v).Perch) : 0 < A.scale*A.J (a v) := mul_pos H.legal.scale (H.positive_accept (he v hp))
  let y (p : G.Color) := Real.log (A.scale*A.J p)
  obtain ⟨hY,hY'⟩ := (H.price_chart k).choose_spec.2.2 _ (he U hp)
  let C := H.coins k
  have hz : 0 ≤ curve H k T := mul_nonneg (zero_le_one.trans (H.cash k)) (by positivity)
  have hr : Ripple (y∘a) U P k (C*g) (2^k*curve H k T) :=
    (motion hg hy ht h p hp i).comp hy hz (zero_le_one.trans (H.cash k)) hY (fun j _ hj => hY' _ hj) hg.le
  have hl := hr.save (by positivity) (H.cash k) hg.le
  let r := curve H k (curve H k T)
  have hm : 0 ≤ r := mul_nonneg (zero_le_one.trans (H.cash k)) (by positivity)
  have hw : Pulse (fun v => -y (a v)) U P k r := (hl.neg.mono hm le_rfl zero_le_one hy).unit
  have hf (v) (hp : p∈(W v).Perch) : Real.exp (-y (a v))=f v := by unfold y; rw [Real.exp_neg,Real.exp_log (hx v hp)]
  rw [← hf U hp]; exact (hw.flare hm).congr' ((h.perching hp).mono fun v hv => (hf _ hv).symm)

lemma product_real {ι : Type*} (s : Finset ι) {f : ι → Config G n → ℝ} {b t : ι → ℝ}
    (hf : ∀ i∈s, Pitch (f i) U P k (b i) (t i)) : Pitch (fun x => ∏ i∈s,f i x) U P k (∏ i∈s,b i) (∑ i∈s,t i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty,norm_one] using! Pitch.fixed (k:=k) (U:=U) (P:=P) (1:ℝ) (le_refl 0)
  | insert i s hi ih =>
    simpa only [Finset.prod_insert hi,Finset.sum_insert hi] using! Pitch.real_mul (hf i (Finset.mem_insert_self ..))
      (ih fun _ h => hf _ (Finset.mem_insert_of_mem h))

def tally (H : Port A) (z d k : ℕ) (t c C : ℝ) :=
    z*pen H k t + 3^k*stall d k c C t + 2^k*C*(t+4*curve H k t)
lemma tally_pos (H : Port A) (z d k : ℕ) {c C t : ℝ} (hc : 0<c) (hC : 0≤C) (ht : 0≤t) :
    0≤ tally H z d k t c C := by
  have hx : 0 ≤ curve H k t := mul_nonneg (zero_le_one.trans (H.cash k)) (by positivity)
  have he := pen_pos H k ht
  unfold tally stall
  have hv := expense_ge hc d (2*k); positivity

/-- Score homothety cost for any j, measured under the actual kernel
law (the complementary patch carries zero kernel; agreed smooth test
there needs zero support appropriately). tower^2 is spent per derivative
order. We keep the full factor including the value piece. -/
theorem chart_pitch (h : Shifts W U P k g T) (hg : 0<g) (hy : g≤1) (ht : 0≤T)
    (hc : 0<c) (hC : 1≤C) (hb : ∀ i x,c*‖x‖^2 ≤ (W U).B i x x)
    (hP : ∀ i,Pitch (fun v => (W v).B i) U P k C T)
    (hp : p∈ (W U).Perch) :
    Pitch (fun v => (W v).confirm g p) U P k ((W U).confirm g p)
      (tally H (Fintype.card ι) (finrank ℝ X) k T c C * tower (W U) g p ^ 2) := by
  let f (v : Config G n) := (H.stamp ((W v).arc p))⁻¹
  let u (v : Config G n) := ((W v).mapUp g p).2
  have hv : Pitch f U P k (f U) (Fintype.card ι*pen H k T) := by
    unfold f stamp
    simp_rw [← Finset.prod_inv_distrib]
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using! product_real Finset.univ
      (fun i (_:i∈(Finset.univ:Finset ι)) => oneCoin h hp hg hy ht i)
  let a := (g^H.dimension ι)⁻¹; have ha : 0<a := by unfold a; positivity
  have hw' : Pitch (fun _=>a) U P k a 0 := by simpa only [Real.norm_of_nonneg ha.le] using Pitch.fixed (U:=U) (P:=P) (k:=k) a (le_refl 0)
  have hw := Pitch.real_mul hw' hv
  let s := curve H k T
  have hs : 0 ≤ s := mul_nonneg (zero_le_one.trans (H.cash k)) (by positivity)
  let t := tower (W U) g p
  have ht' : 1 ≤ t := le_add_of_nonneg_right (norm_nonneg _)
  have hV : Pitch u U P k (1+‖u U‖) (2*s) := (drift hg hy ht h p hp).wrap (by positivity)
    (by linarith [norm_nonneg (u U)] : 1≤1+‖u U‖) (le_add_of_nonneg_left zero_le_one)
  let B v := (W v).B p.1
  let d := finrank ℝ X
  let b := 3^k*stall d k c C T
  let L : ℝ := Fintype.card ι * pen H k T
  have hts : 0 ≤ b := by unfold b stall; have he := expense_ge hc d (2*k); positivity
  have hl : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) (pen_pos H k ht)
  have := Surface.add_haar H ι κ
  have hh := Gaussian.dynamic volume hc (hb p.1) (hP p.1) ht hC hV (by positivity)
  let y v := a*f v * pdf volume (B v) (u v)
  have he : Pitch y U P k (y U) (L+( (2:ℝ)^k*C*t^2*(T+2*(2*s))+b)) := by
    simpa only [zero_add] using! Pitch.real_mul hw hh
  have hx : (fun v => (W v).confirm g p) ∘ increment U =ᶠ[𝓝 0] y ∘ increment U := by
    filter_upwards [h.perching hp] with v hb; dsimp only [comp_apply,confirm, Port.route]
    rw [if_pos (show _∈H.touch _ from hb)]; rfl
  rw [show (W U).confirm g p = y U by simpa only [comp_apply,increment_zero] using hx.self_of_nhds]
  refine he.congr' hx |>.mono le_rfl (by positivity) ?_
  change L+(_+b) ≤ ((L+b)+2^k*C*(T+4*s))*t^2
  have hu : L+b ≤ (L+b)*t^2 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ ht')
  linarith only [hu]
end YM.Further.DenseMixedKernels.Surface
