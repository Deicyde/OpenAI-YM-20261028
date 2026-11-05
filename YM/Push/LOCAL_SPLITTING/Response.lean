import YM.Push.LOCAL_SPLITTING.CovariantKernel
import YM.Push.LOCAL_SPLITTING.NoiseJet


/-!
# Nonperturbative smooth local probes of the actual one-step push

An auxiliary ratio of entire observed-edge integrals including vacuum,
not a Pi/terminal fit to a conditional expectation. It gives intermediate
cylindrical functions without any fitted coordinates and without sectorwise
division. No claim of localization of the conditioning or small tails.
Explicit prices grow with the observation support and are not the PSREC
step estimate. Every derivative bound is for a representative (pointwise).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Filter Lattice Wilson RG Source Labels MeasureTheory Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side}

structure Good (S : StepData c f) (D : Config G f → ℝ) (F : Config G f → ℂ) : Prop where
  branches : S.patch.Branches S.kernel G
  denom : Integrable D (prior G f)
  input : Integrable F (prior G f)
  positive : ∀ U, 0 < D U
  gauge : GaugeInvariant D
  sym : GaugeInvariant F

section Ratio
variable (S : StepData c f) (β : ℝ) {D : Config G f → ℝ} {F : Config G f → ℂ}

variable (D F) in
def response (J : Edges c) (V : Config G c) := pass S β J F V / ((pass S β J D V : ℝ) : ℂ)

variable {S}

theorem response_local (X : Support c) (D : Config G f → ℝ) (F : Config G f → ℂ) : LocalOn X (response S β D F (edges X)) := fun _ _ h => congr_arg₂ (· / ·) (pass_local S β X F _ _ h) (congr_arg Complex.ofReal (pass_local S β X D _ _ h))

theorem response_gauge (J : Edges c) (h : Good S D F) : GaugeInvariant (response S β D F J) := fun g V => by rw [response,response,pass_gauge S β J h.branches h.gauge, pass_gauge S β J h.branches h.sym]



private def vacuum (J : Edges c) (D : Config G f → ℝ) := Complex.ofRealCLM ∘ pass S β J D

private theorem vacuum_ne (J : Edges c) {V : Config G c} (h : Good S D F) : vacuum (S:=S) β J D V ≠ 0 := Complex.ofReal_ne_zero.mpr (pass_pos S β J h.branches _ h.denom h.positive).ne'

private theorem vacuum_chart (J : Edges c) {V : Config G c} (k : ℕ) (h : Good S D F) : Chart k (vacuum (S:=S) β J D) V := Complex.ofRealCLM.contDiff.contDiffAt.comp _ (smooth_pass S β J h.branches h.denom _ _)

theorem response_chart (J : Edges c) (V : Config G c) (k : ℕ) (h : Good S D F) : Chart k (response S β D F J) V := by
  have he : (vacuum (S:=S) β J D ∘ increment V) 0 ≠ 0 := by rw [comp_apply,Work.G07.at_zero_increment]; exact vacuum_ne β J h
  rw [show response S β D F J = pass S β J F * (vacuum (S:=S) β J D)⁻¹ from funext fun W => div_eq_mul_inv ..]
  exact (smooth_pass S β J h.branches h.input V k).mul ((vacuum_chart β J k h).inv he)

theorem response_regular (X : Support c) (B : BudgetPoint) (h : Good S D F) : B.Regular X (response S β D F (edges X)) :=
  ⟨response_local β X D F, ((pass_continuous S β (edges X) h.branches h.input).div
    (Complex.continuous_ofReal.comp (pass_continuous S β (edges X) h.branches h.denom)) (fun _ => vacuum_ne β _ h)).measurable,
    response_gauge β _ h, fun V _ => response_chart β _ V _ h, fun V _ A _ hl => left_has A hl (response_chart β _ V _ h)⟩
end Ratio

section Derivs
private theorem chart_inv {Z : Config G c → ℂ} {V : Config G c} {k : ℕ} (h : Chart k Z V) (hp : Z V ≠ 0) : Chart k (fun W => (Z W)⁻¹) V := h.inv (by simpa [Work.G07.at_zero_increment] using hp)

private theorem inv_first {Z : Config G c → ℂ} {V : Config G c} (A : Directions G c) (hf : Chart 1 Z V) (hp : Z V ≠ 0) :
    leftDerivs (fun W => (Z W)⁻¹) [A] V = (Z V)⁻¹ * (Z V)⁻¹ * leftDerivs Z [-A] V := by
  have hx := ((left_has A (l:=[]) (by simp) hf).inv (by simpa [leftDerivs,Work.G07.at_zero_increment] using hp)).deriv
  change leftDerivs (fun W => (Z W)⁻¹) [A] V = _ at hx
  rw [hx,left_cons (-A) [] hf (by simp),map_neg, ← left_cons A [] hf (by simp)]
  simp [leftDerivs,Work.G07.at_zero_increment,div_eq_mul_inv,pow_two]; ring

def invRate (k : ℕ) (C : ℝ) : ℕ → ℝ
  | 0 => 1
  | m+1 => 2^k*(2^k*(invRate k C m * invRate k C m)*C)

private theorem invRate_pos (k : ℕ) {C : ℝ} (hC : 1 ≤ C) (m : ℕ) : 1 ≤ invRate k C m := by
  induction m with
  | zero => rfl
  | succ m ih => exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_mul_of_one_le_of_one_le ih ih)) hC)

/-- A coarse reciprocal jet estimate, homogeneous in the denominating vacuum
value. Costs depend on the order. Positivity is at the actual conditioning
input where read (and here we require nonzero and C^k at every input).
No upper/lower bound constant depending on a partition function. -/
theorem inv_bound {Z : Config G c → ℂ} {D : Directions G c → Prop} {V : Config G c} {k m : ℕ} {C : ℝ} (hC : 1 ≤ C) (hm : m ≤ k)
    (he : ∀ V, Chart k Z V) (hp : ∀ V, Z V ≠ 0) (hs : ∀ v, D v → D (-v))
    (h : ∀ l : List (Directions G c), l.length ≤ k → (∀ v∈l,D v) → ‖leftDerivs Z l V‖ ≤ C * ‖Z V‖) :
    ∀ l : List (Directions G c), l.length ≤ m → (∀ v∈l,D v) → ‖leftDerivs (fun W => (Z W)⁻¹) l V‖ ≤ invRate k C m * ‖Z V‖⁻¹ := by
  intro l hl hD
  have hZ := norm_pos_iff.mpr (hp V)
  induction m generalizing l with
  | zero => cases l with
    | nil => simp [leftDerivs,invRate]
    | cons v l => simp at hl
  | succ m ih =>
    let Q := invRate k C m * ‖Z V‖⁻¹
    have hQ : 0 ≤ Q := mul_nonneg (zero_le_one.trans (invRate_pos k hC m)) (inv_pos.mpr hZ).le
    have h' : Chart m (fun W => (Z W)⁻¹) V := chart_inv ((he V).of_le (Nat.cast_le.mpr (m.le_succ.trans hm))) (hp _)
    have ih' := ih (m.le_succ.trans hm)
    have hh (l : List (Directions G c)) (hl : l.length ≤ m) (hd : ∀ v∈l,D v) : ‖leftDerivs ((fun W => (Z W)⁻¹) * (fun W => (Z W)⁻¹)) l V‖ ≤ 2^k*(Q*Q) := (left_mul_bound h' h' ih' ih' l hl hd).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (mul_nonneg hQ hQ))
    induction l using List.reverseRecOn with
    | nil => rw [leftDerivs, norm_inv]; exact le_mul_of_one_le_left (inv_pos.mpr hZ).le (invRate_pos k hC _)
    | append_singleton l A _ =>
      have hl' : l.length ≤ m := by simpa using hl
      have H (l' : List (Directions G c)) (hl' : l'.length ≤ m) (hd' : ∀ v∈l',D v) : ‖leftDerivs (leftDerivs Z [-A]) l' V‖ ≤ C*‖Z V‖ := by
        rw [← Work.G07.left_append]; exact h _ (by simp; omega) (fun v hv => by rcases List.mem_append.mp hv with hi|hi; exact hd' v hi; simpa [List.mem_singleton.mp hi] using hs A (hD A (by simp)))
      rw [Work.G07.left_append, show leftDerivs (fun W => (Z W)⁻¹) [A] = ((fun W => (Z W)⁻¹) * (fun W => (Z W)⁻¹)) * leftDerivs Z [-A] from funext fun V => inv_first A ((he V).of_le (Nat.cast_le.mpr (by omega : 1≤k))) (hp V)]
      refine (left_mul_bound (h'.mul h') (leftDerivs_chart _ m ((he V).of_le (Nat.cast_le.mpr (by simp; omega)))) hh H l hl' (fun v hv => hD v (by simp [hv]))).trans ?_
      refine (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hl'.trans (m.le_succ.trans hm))) (by positivity : 0 ≤ 2^k * (Q*Q) * (C * ‖Z V‖))).trans_eq ?_
      rw [invRate]; unfold Q; field_simp

def responsePrice (G : Gauge) (β : ℝ) (k j : ℕ) (r : ℝ) := 2^k * ((noiseFactor G β k j r)^k * invRate k ((noiseFactor G β k j r)^k) k)

variable {S : StepData c f} (β : ℝ) (J : Edges c) {D : Config G f → ℝ} {F : Config G f → ℂ}

theorem bound_response (V : Config G c) (h : Good S D F) {r a : ℝ} (hr : 0 ≤ r) (ha : ∀ U, ‖F U‖ ≤ a*D U)
    (k : ℕ) (l : List (Directions G c)) (hl : l.length ≤ k) (H : ∀ v∈l, ∀ i∈J, ‖v i‖ ≤ r) :
    ‖leftDerivs (response S β D F J) l V‖ ≤ responsePrice G (β*S.kernel.penalty) k J.card r * a := by
  let C := (noiseFactor G (β*S.kernel.penalty) k J.card r)^k
  have hC : 1 ≤ C := one_le_pow₀ (noiseFactor_ge _ _ _ _ hr)
  let q (A : Directions G c) := ∀ i∈J, ‖A i‖ ≤ r
  let Z := vacuum (S:=S) β J D
  have hZ : ‖Z V‖ = pass S β J D V := (Complex.norm_real _).trans (Real.norm_of_nonneg (pass_pos S β J h.branches _ h.denom h.positive).le)
  have hv : Chart k (pass S β J D) V := smooth_pass S β J h.branches h.denom V k
  have hd := inv_bound (Z:=Z) (D:=q) (V:=V) hC (le_refl k) (fun V => vacuum_chart β J _ h) (fun _ => vacuum_ne β J h) (fun _ => by simp [q]) (fun l hl hl' => by
    rw [hZ,show leftDerivs Z l V = _ from left_linear Complex.ofRealCLM l hv hl]; simpa using! bound_pass S β J h.branches V hr h.denom h.denom (a:=1) (fun U => by rw [Real.norm_of_nonneg (h.positive _).le,one_mul]) l hl hl')
  have hn := bound_pass (k:=k) S β J h.branches V hr h.input h.denom ha
  have hp := pass_pos S β J h.branches V h.denom h.positive
  have h₀ : 0 ≤ a := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (ha 1)) (h.positive _)
  rw [show response S β D F J = pass S β J F * (fun W => (Z W)⁻¹) from funext fun W => div_eq_mul_inv ..]
  apply (left_mul_bound (smooth_pass S β J h.branches h.input V k) (chart_inv (vacuum_chart β J k h) (vacuum_ne β J h)) (fun l hl => hn l hl) hd l hl H).trans
  rw [hZ]; unfold responsePrice
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) ?_)
  · field_simp; dsimp [C]; exact le_of_eq (by ring)
  change 0 ≤ C*a*pass S β J D V * (invRate k C k * (pass S β J D V)⁻¹); positivity [invRate_pos k hC k]

/-- Sup cost at an arbitrary anchor for a local region. Powers paid on
initial edge vertices in the given support only. -/
theorem budget_response (o : Site c) (X : Support c) {R : ℝ} (hr : 0 ≤ R) (hR : ∀ x ∈ X,(separation x o:ℝ) ≤ R) (B : BudgetPoint) (h : Good S D F) {a : ℝ} (ha : ∀ U, ‖F U‖ ≤ a*D U) :
    B.supBounds o X (response S β D F (edges X)) (responsePrice G (β*S.kernel.penalty) B.order (edges X).card (B.threshold*(1+R)^B.power) * a) := by
  let p := B.threshold*(1+R)^B.power
  have hp : 0 ≤ p := by positivity [B.threshold_pos]
  have ht := noiseFactor_ge G (β*S.kernel.penalty) B.order (edges X).card hp
  have h₀ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (ha 1)) (h.positive _)
  refine ⟨by unfold responsePrice; change 0 ≤ 2^B.order*(((noiseFactor G _ B.order (edges X).card p)^B.order)*invRate B.order ((noiseFactor G _ B.order (edges X).card p)^B.order) B.order)*a; positivity [invRate_pos B.order (one_le_pow₀ (n:=B.order) ht) B.order],fun U _ l hl hd => bound_response β (edges X) U h hp ha B.order l hl ?_⟩
  intro v hv i hi; apply (hd v hv i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith [hR _ (Finset.mem_filter.mp hi).2.1] : _ ≤ 1+R) _) B.threshold_pos.le)
end Derivs
end YM.Push.Local.Kernel
