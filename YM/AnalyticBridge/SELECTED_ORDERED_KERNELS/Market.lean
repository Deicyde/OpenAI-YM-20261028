import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.TrueNoise
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.TrueTransport

/-!
# Forward ordinary `market` with all coarse slots before active restriction

Same common-background budget for either of two neighbouring tags. THIS
matrix needn't itself be gapped. `shared` mask on the noise rows, absolute
both-orientation prices. Faces over all rows with the ACTUAL transport by
the moved replica composed AFTER the fine-slot derivative. No differentiating
that transport in computing the face response tangent; do differentiate it
w.r.t. every external background slot. After L, same delay as Q row supply.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Bloch Next.SectorChange Next.Fluctuations
  YM.Pressure FreeResolvent Affine Mark TestD Push.Uniform Matrix
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Patch} {n : ℕ} {d σ C M : ℝ}
  {x : ℝ} {A : Stores S} {T U : Forest S.ratio} {k : S.Choices} {V : Config G c}
  {W : PathData G}

def outlet (x : ℝ) (A : Stores S) (T U : Forest S.ratio) (k : S.Choices) (V : Config G c) (s : Signed) (p : Clip) (W : PathData G) (r : Admit)
    (B : Vec G c 1) :=
  let H := matrix (petals S V s) B
  let N := matrix (contacts x A T U k V s) B
  p.direct • squareQ H + squareQ (over (NoHole.pathRows S s W r) V B * H) + S.kernel.penalty • squareQ N

def market (x : ℝ) (A : Stores S) (T U : Forest S.ratio) (k : S.Choices) (V : Config G c) (p : Clip) (W : PathData G) (r : Admit)
    (B : Vec G c 1) := (Fintype.card Signed:ℝ)⁻¹ • ∑ s, outlet x A T U k V s p W r B



def receive (P : Patch) (G : Gauge) (σ : ℝ) (n : ℕ) (C : ℝ) := let γ := staging σ n
  altitude (max (torusPay (Co P.L (PAC G 1)) γ) (torusPay (PAC G 1) γ)) γ n (predReach P+1) C

def marketFee (P : Patch) (G : Gauge) (K : KernelChoices) (p : Clip) (σ : ℝ) (n : ℕ) (C M : ℝ) :=
  let x := Small.low P G σ n C; let y := Small.transportPrice P G σ n C M; let z := receive P G σ n C
  p.direct * tagPrice 1 n x x + tagPrice 1 n y y + K.penalty * tagPrice 1 n z z
lemma receive_nn (P : Patch) (G : Gauge) (hσ : 0 < σ) (n : ℕ) (hC : 0 ≤ C) : 0 ≤ receive P G σ n C :=
  altitude_nn (le_max_of_le_left (torusPay_nn _ _ (staging_pos hσ n))) hC
lemma market_nn (K : KernelChoices) (p : Clip) (hσ : 0 < σ) (hC : 0 ≤ C) (hm : 0 ≤ M) : 0 ≤ marketFee P G K p σ n C M := by
  have hl := (Small.foot_nn P G (staging_pos hσ n) n hC).1; have hr := receive_nn P G hσ n hC
  have ht : 0 ≤ Small.transportPrice P G σ n C M := Small.path_nn hσ hm hC
  exact add_nonneg (add_nonneg (mul_nonneg p.quadratic_pos.le (tag_nn hl hl)) (tag_nn ht ht)) (mul_nonneg K.penalty_pos.le (tag_nn hr hr))

structure Sharing (x : ℝ) (A : Stores S) (T U : Forest S.ratio) (k : S.Choices) (V : Config G c) (n : ℕ) (C : ℝ) : Prop where
  faces (s : Signed) (i : tile G f) : Allows n (fun z => petals S V s z i) 0 C
  noise (s : Signed) (i : raw G c) : Allows n (fun z => contacts x A T U k V s z i) 0 C

theorem sharing (G : Gauge) (P : Patch) (K : KernelChoices) (hp : P.Branches K G) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → 100*(1+radiusB x) ≤ c.val →
    ∀ (A : Stores S) (T U : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V → Sharing x A T U k V n C := by
  obtain ⟨D,hD,h⟩ := petals_pay G n
  obtain ⟨C,hC,h'⟩ := contacts_pay G P K hp n
  exact ⟨max D C, le_max_of_le_left hD, h'.mono fun x hx c f S hS hK hR A T U k V hV =>
    ⟨fun s i => (h S V s i).mono (le_max_left ..),fun s i => (hx S hS hK hR A T U k V hV s i).mono (le_max_right ..)⟩⟩

namespace Sharing
variable (h : Sharing x A T U k V (n+1) C)
  (hS : S.patch.Branches S.kernel G) (hs : 0 < σ) (hC : 0 ≤ C)
  (hm : 0 ≤ M) (hW : Sheet W σ M) (hd : 0 ≤ d) (hx : d ≤ tier σ n)
include h hS hs hC hd hx
lemma both_priced (s : Signed) : Bundle (ray G c) (marks G c d) (native c) (named S s) (home S) (matrix (petals S V s)) 0 n (staging σ n) (Small.low S.patch G σ n C) ∧
    Bundle (ray G c) (marks G c d) (native c) (namedCo s) (home S) (matrix (contacts x A T U k V s)) 0 n (staging σ n) (receive S.patch G σ n C) := by
  have hγ := staging_pos hs n
  have he := hx.trans ((ordering hs n).2.1.trans (ordering hs n).2.2.1)
  exact ⟨local_prices (named S s) S (contDiffAt_pi.mpr fun i => (h.faces s i).analytic) n _ hC hγ hd he ((home_volume _ _ _ hγ).le (le_max_left ..))
      ((named_volume _ _ _ _ hγ).le (le_max_right ..)) (fun i => Eventually.of_forall (fun z => petals_local S V s z i)) fun i j hj => (h.faces s i).norm_le _ (Nat.add_le_add_right hj _),
    local_prices (namedCo s) S (contDiffAt_pi.mpr fun i => (h.noise s i).analytic) n _ hC hγ hd he ((home_volume _ _ _ hγ).le (le_max_left ..))
      ((co_volume _ _ _ _ _ hγ).le (le_max_right ..)) (fun i => Eventually.of_forall (fun z => contacts_local hS z i)) fun i j hj => (h.noise s i).norm_le _ (Nat.add_le_add_right hj _)⟩
include hm hW
lemma outlet_priced (s : Signed) (p : Clip) (r : Admit) : Bundle (ray G c) (marks G c d) (native c) (home S) (home S)
    (outlet x A T U k V s p W r) 0 n (tier σ n) (marketFee S.patch G S.kernel p σ n C M) := by
  have ⟨h1,h2,h3,h4⟩ := ordering hs n; have hγ := staging_pos hs n
  have hl := (Small.foot_nn S.patch G hγ n hC).1; have hr := receive_nn S.patch G hs n hC
  have ht : 0 ≤ Small.transportPrice S.patch G σ n C M := Small.path_nn hs hm hC
  have hw : 0 ≤ (n:ℝ) := by positivity
  have hu : 2*staging σ n+2*n*d ≤ σ/2 := by nlinarith only [h4,mul_le_mul_of_nonneg_left hx hw]
  have hv : wider σ n+n*d ≤ staging σ n := add_le_add_right (mul_le_mul_of_nonneg_left hx hw) _
  obtain ⟨hl',hr'⟩ := both_priced h hS hs hC hd hx s
  have hyg := transport_rows V S s W r n hs hW hm hd hγ hu 0 (fun _ _ => Nat.zero_le _)
  simp only [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] at hyg
  have hp := position_move (native c) (hearth (G:=G) (r:=1)) hd
  have hh := hyg.multiply hl' hp hd le_rfl (longPrice_nn _ _ hs hm) hl (h1.le.trans h2) hv
  have he : tier σ n+n*d ≤ wider σ n := add_le_add_right (mul_le_mul_of_nonneg_left hx hw) _
  have hw := hl'.mono h3 le_rfl; have hv := hr'.mono h3 le_rfl
  have H := (((hw.transpose.multiply hw hp hd le_rfl hl hl h1.le he).scale p.direct).one_add
    (hh.transpose.multiply hh hp hd le_rfl ht ht h1.le he)).one_add ((hv.transpose.multiply hv hp hd le_rfl hr hr h1.le he).scale S.kernel.penalty)
  rw [abs_of_pos p.quadratic_pos,abs_of_pos S.kernel.penalty_pos] at H; exact H

lemma market_priced (p : Clip) (r : Admit) : Bundle (ray G c) (marks G c d) (native c) (home S) (home S)
    (market x A T U k V p W r) 0 n (tier σ n) (marketFee S.patch G S.kernel p σ n C M) := by
  have H := (Bundle.sum_all Finset.univ _ (fun s _ => outlet_priced h hS hs hC hm hW hd hx s p r)).scale (Fintype.card Signed:ℝ)⁻¹
  have hh : 0 < (Fintype.card Signed : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ, abs_of_pos (inv_pos.mpr hh), ← mul_assoc,inv_mul_cancel₀ hh.ne',one_mul] at H
  exact H
end Sharing
end YM.SelectedOrderedKernels.Selected
