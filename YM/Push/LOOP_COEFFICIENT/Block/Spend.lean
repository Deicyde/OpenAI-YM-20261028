import YM.Push.LOOP_COEFFICIENT.Block.Fibers
import YM.Push.LOOP_COEFFICIENT.Block.Glow
import YM.Push.LOOP_COEFFICIENT.Block.Magnitude
import YM.Push.LOOP_COEFFICIENT.Block.Masses
import YM.Push.LOOP_COEFFICIENT.Block.Tests



/-!
# Tilted alias H² to Young counting prices, at arbitrary total frequencies
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Filter Lattice Laurent RG Wilson Bloch Precision Exterior Kernel Complex Portal
open scoped Topology Matrix.Norms.L2Operator ContDiff BigOperators
variable {G : Gauge} {L : Side} {η C : ℝ} {q : Momentum} {a b d : Type} [Fintype a] [Fintype b] [Fintype d] [DecidableEq b] {Y : Profiles L a b}

def heft (L : Side) (q : Momentum) (i : Site L) := (L.val:ℝ) * energy L q i
lemma heft_ge_one (q : Momentum) (i : Site L) : 1 ≤ heft L q i := by unfold heft; simpa [side_ne,ne_of_gt (side_pos L)] using! mul_le_mul_of_nonneg_left (energy_lo L q i) (side_pos L).le
lemma heft_pos (q : Momentum) (i : Site L) : 0 < heft L q i := zero_lt_one.trans_le (heft_ge_one ..)
lemma heft_bill (hη : 0<η) : ∃ K>0,∀ {L : Side} {q}, q∈Center η → ∀ i : Site L, heft L q i ≤ K * mass i := by
  refine ⟨2 + 2*(3*Real.pi+η),by positivity,fun {L q} hq i => ?_⟩
  have he (z : Momentum) : ‖Fine.shade z‖ ≤ ‖z‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun i => by simpa [Fine.shade] using! (Complex.abs_re_le_norm (z i)).trans (norm_le_pi_norm z i)
  have h := energy_ruler q i
  have hi := (he _).trans (alias_norm hq i); unfold Fine.ruler at h
  field_simp at hi h; unfold heft; nlinarith [side_pos L,mass_one i]
omit [DecidableEq b] in
lemma alias_sup (Y : Matrix a b ℂ) {A : ℝ} (h : Entries Y A) {x : CSpace b} (hx : ‖x‖≤1) : ‖Y *ᵥ x‖ ≤ Fintype.card b*A := by
  have hA := h.nonneg; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => (norm_sum_le ..).trans ?_; exact (Finset.sum_le_sum (g:=fun _ => A) (fun j _ => by rw [norm_mul]; exact (mul_le_mul (h.entry i j) ((norm_le_pi_norm ..).trans hx) (norm_nonneg _) hA).trans (by simp))).trans_eq (by simp)

/-- Cost of any external columns in the distributed-alias prescription.
Unlike Spread, valid without choosing real representatives beforehand. -/
def Provision (Y : Profiles L a b) (η C : ℝ) := ∀ q∈Tube η,∀ v : CSpace b, ‖v‖≤1 → ∑ i,(heft L q i ^2 * ((L.val:ℝ)*‖Y q i *ᵥ v‖))^2 ≤ C
variable (a b) in
lemma provision_price (hη : 0<η) (M : ℝ) : ∃ C>0,∀ {L : Side} {Y : Profiles L a b}, Spread Y η M → Flow Y η → Provision Y η C := by
  obtain ⟨K,hK,H⟩ := heft_bill hη
  let B : ℝ := Fintype.card b
  refine ⟨1+(K^2*B*M)^2,by positivity,fun {L Y} h he z hz v hv => ?_⟩
  obtain ⟨q,hq,x,rfl⟩ := center_adjust hz
  obtain ⟨w,hw,h'⟩ := h q hq
  simp_rw [heft,energy_shift,he.align _ q hq.1]
  erw [Equiv.sum_comp (Equiv.addRight (wrap L x)) (fun i => (heft L q i ^2 * (L.val*‖Y q i *ᵥ v‖))^2)]
  have hS i : heft L q i^2 * (L.val*‖Y q i *ᵥ v‖) ≤ K^2 * (L.val*B) * (mass i^2 * w i) := by
    have := heft_ge_one q i; convert! mul_le_mul (pow_le_pow_left₀ (heft_pos ..).le (H hq i) 2) (mul_le_mul_of_nonneg_left (alias_sup _ (hw i) hv) (side_pos L).le) (by positivity) (by positivity) using 1; dsimp [B]; ring
  refine (Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (by positivity)) (hS i) 2)).trans ?_
  simp only [mul_pow (K^2 * _) (mass _ ^2 * _), ← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left h' (sq_nonneg _)).trans ((le_of_eq (b:=(K^2*B*M)^2) (by field_simp)).trans (le_add_of_nonneg_left zero_le_one))

lemma beam_first {x : CSpace (Co L d)} (hx : mag x ≤ 1) : ∑ i, mag (beam i x)^2 ≤ 1 := (mag_prod x).trans_le ((pow_le_pow_left₀ (mag_nonneg _) hx 2).trans (by simp))
lemma beam_second {x : CSpace (Co L d)} (hx : mag x ≤ 1) (hq : ∑ i, (heft L q i)⁻¹^6 ≤ C) : ∑ i, ((heft L q i)⁻¹ * mag (beam i x))^(3/2:ℝ) ≤ C+1 := mix_one (fun i => (inv_pos.mpr (heft_pos q i)).le) (fun _ => mag_nonneg _) hq (beam_first hx)
variable (h : Provision Y η C) (hq : q∈Tube η) {v : CSpace b} (hv : ‖v‖≤1) {K : ℝ} (hm : ∑ i, (heft L q i)⁻¹^6 ≤ K)
include h hq hv hm
omit [DecidableEq b] in
lemma Provision.first : ∑ i, ((L.val:ℝ)*‖Y q i *ᵥ v‖)^(6/5:ℝ) ≤ K+C := by
  have H := mix_two (fun i : Site L => (inv_pos.mpr (heft_pos q i)).le) (fun i : Site L => show 0≤ heft L q i ^2 * ((L.val:ℝ)*‖Y q i *ᵥ v‖) by positivity) hm (h q hq v hv)
  simpa only [inv_pow,inv_mul_cancel_left₀ (pow_ne_zero _ (heft_pos ..).ne')] using! H
omit [DecidableEq b] in
lemma Provision.second : ∑ i, (heft L q i * ((L.val:ℝ)*‖Y q i *ᵥ v‖))^(3/2:ℝ) ≤ K+C := by
  have H := mix_one (fun i : Site L => (inv_pos.mpr (heft_pos q i)).le) (fun i : Site L => show 0≤ heft L q i ^2 * ((L.val:ℝ)*‖Y q i *ᵥ v‖) by positivity) hm (h q hq v hv)
  simpa only [pow_two,mul_assoc, fun i => inv_mul_cancel_left₀ (heft_pos q i).ne'] using! H
end YM.Push.Loops.Block
