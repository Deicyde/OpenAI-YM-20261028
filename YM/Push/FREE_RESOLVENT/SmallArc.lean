import YM.Push.FREE_RESOLVENT.FixedBox
import YM.Push.FREE_RESOLVENT.TrackBill

/-!
# Polarized row & column budgets for D, Q jets

Counting periods, parent distance. Reserve extra positions before shrinking
in the products. Pay work entirely on patch offsets *in the actual V field*.
Rotated indices on their named site; one-unit orientation shift paid in reach.
These are real Taylor-derivative caps; use with any k (including zero).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.F08 Lifted Mark
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c : Side} {s : Signed} {S : StepData c f}

-- one constant preserving both cost and inverse semantics
def altitude (V : ℝ) (γ : ℝ) (k : ℕ) (R : ℕ) (A : ℝ) := V*(Real.exp (k*γ*(2*R))* (Real.exp (2*γ*R)*A))
lemma altitude_nn {V γ A : ℝ} {k R} (hv : 0 ≤ V) (ha : 0 ≤ A) : 0 ≤ altitude V γ k R A :=
  mul_nonneg hv (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le ha))

section estimate
variable {ι : Type*} [Fintype ι] {F : pair G c f → ι → ℝ} (x : ι → Site c)

theorem local_prices (S : StepData c f) (hf : ContDiffAt ℝ ω F 0) (k : ℕ) (R : ℕ) {A γ d V : ℝ}
    (hm : 0 ≤ A) (hg : 0 < γ) (hd : 0 ≤ d) (hc : d ≤ γ)
    (hV : (native c).Volume (home (G:=G) (r:=1) S) γ V) (hv : (native c).Volume x γ V)
    (hy : ∀ i : ι, (fun z => F (stopAt S (x i) R z) i)=ᶠ[𝓝 0] (fun z => F z i))
    (he : ∀ i n, n ≤ k → ‖iteratedFDeriv ℝ (n+1) (fun z => F z i) 0‖ ≤ A) :
    Bundle (ray G c) (marks G c d) (native c) x (home S) (matrix F) 0 k γ (altitude V γ k R A) := by
  constructor
  · exact grad_smooth hf k
  intro l hl
  let D := native c; let Y := jet (ray G c) (matrix F) l 0
  let C := marks G c d
  let H := Real.exp (k*γ*(2*R))* (Real.exp (2*γ*R)*A)
  have hN : 0 ≤ H := by unfold H; positivity
  have hh (i j) : C.pay l (x i)*(D.weight (2*γ) (x i) (home S j) * |Y i j|) ≤ H ∧
      C.pay l (home S j)*(D.weight (2*γ) (home S j) (x i) * |Y i j|) ≤ H := by
    by_cases hj : Y i j = 0
    · simp only [hj,abs_zero,mul_zero]; exact ⟨hN,hN⟩
    obtain ⟨hs,hw⟩ := coal S _ _ j l hf (hy i) hj
    have hL : D.d (x i) (home S j) ≤ R := by change ((separation _ _):ℝ) ≤ (R:ℝ); exact_mod_cast hs
    have hp (u : Site c) (hh : separation u (x i) ≤ R) :
        C.pay l u * (D.weight (2*γ) (x i) (home S j) * |Y i j|) ≤ H := by
      have ht (v) (h : v∈l) : D.d u (hearth v) ≤ 2*R := by
        have hz : separation u (hearth v) ≤ 2*R := by
          have hp := hw v h; have he := separation_triangle u (x i) (hearth v); omega
        change ↑(separation u (hearth v)) ≤ 2*(R:ℝ); exact_mod_cast hz
      have he : ‖Y i j‖ ≤ A := polar_focus hf j l hm (he i _ hl)
      apply mul_le_mul _ _ (mul_nonneg (D.weight_nn ..) (abs_nonneg _)) (Real.exp_pos _).le
      · apply (plumb D u _ l hd _ ht).trans
        apply Real.exp_monotone; gcongr
      exact mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left hL (by positivity))) he (abs_nonneg _) (Real.exp_pos _).le
    rw [D.weight_symm _ (home S j)]
    exact ⟨hp _ (by simp), hp _ ((separation_comm ..).trans_le hs)⟩
  exact Bill.of_entry (volume_down hV (by linarith)) (volume_down hv (by linarith)) hN (fun i j => (hh i j).1) fun i j => (hh i j).2
end estimate

def lowBudget (G : Gauge) (P : Patch) (K : KernelChoices) (γ : ℝ) (k : ℕ) := altitude
  (max (torusPay (Co P.L (PAC G 1)) γ) (torusPay (Co P.L (PAC G 2)) γ)) γ k 4 (View.faceBill G P K k)
lemma low_nn (k : ℕ) (P : Patch) (K : KernelChoices) {γ : ℝ} (hp : 0 < γ) : 0 ≤ lowBudget G P K γ k :=
  altitude_nn (le_max_of_le_left (torusPay_nn _ γ hp)) (View.bills_nonneg G P K k).1

def highBudget (G : Gauge) (P : Patch) (K : KernelChoices) (γ : ℝ) (k : ℕ) := altitude
  (max (torusPay (Co P.L (PAC G 1)) γ) (torusPay (PAC G 1) γ)) γ k (View.reach P+2) (View.ductBill G P K k)
lemma high_nn (k : ℕ) (P : Patch) (K : KernelChoices) {γ : ℝ} (hp : 0 < γ) : 0 ≤ highBudget G P K γ k :=
  altitude_nn (le_max_of_le_left (torusPay_nn _ γ hp)) (View.bills_nonneg G P K k).2

lemma price_D (S : StepData c f) (s : Signed) (h : 1<c.val) (k : ℕ) {γ d : ℝ} (hg : 0 < γ) (hd : 0 ≤ d) (hh : d ≤ γ) :
    Bundle (ray G c) (marks G c d) (native c) (named S s) (home S) (response S s) 0 k γ (lowBudget G S.patch S.kernel γ k) :=
  local_prices (named S s) S (face_smooth s).contDiffAt k _ (View.bills_nonneg G S.patch S.kernel k).1 hg hd hh
    ((home_volume S 1 γ hg).le (le_max_left ..)) ((named_volume S s 2 γ hg).le (le_max_right ..))
    (fun i => EventuallyEq.of_eq (View.monotile S s i h)) fun i => View.face_tariff S s i h

lemma price_Q (S : StepData c f) (s : Signed) (t : S.Choices) (h : 1<c.val) (k : ℕ) {γ d : ℝ}
    (hb : S.patch.Branches S.kernel G) (hg : 0 < γ) (hd : 0 ≤ d) (hh : d ≤ γ) :
    Bundle (ray G c) (marks G c d) (native c) (namedCo s) (home S) (duct S s t) 0 k γ (highBudget G S.patch S.kernel γ k) :=
  local_prices (namedCo s) S (duct_smooth hb s t) k _ (View.bills_nonneg G S.patch S.kernel k).2 hg hd hh
    ((home_volume S 1 γ hg).le (le_max_left ..)) ((co_volume G c s 1 γ hg).le (le_max_right ..))
    (fun i => View.monopole S s i t h hb) fun i => View.duct_tariff S s t i h hb
end YM.FreeResolvent.Affine
