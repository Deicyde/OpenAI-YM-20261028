import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Counter
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Receipts

/-!
# Additional uniform open-domain no-hole pricing in exact Lie currency

An actual strengthening of the Taylor point derivations (fixed-L). This
is on the very same physical operators and includes the same pairwise and
star sums. Requires a globally chord-small V in one trivialization, NOT just
small plaquettes or a mere finite patch with defects outside, and not the
SectorChange A (see AuthorizedLoans for different applications).
Retain any tree hypothesis needed for directGap, all fields/derivative
slots and one tag test of Affine (`changed`) in each. Mixed extent & tag
gain. No cost here justifies selecting an analytic width before L.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Precision Tree Exterior Function Filter Topology Bloch Laurent Metric Matrix FreeResolvent Affine
  Lifted TestD Mark Set Lever NoHole Window
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {P : Patch} {K : KernelChoices} {n k : ℕ} {S : StepData c f} {p : Clip}
  {σ C M r d γ u : ℝ} {t : S.Choices} {V : Config G c} {W : PathData G}

lemma obtain_log (G : Gauge) {r : ℝ} (hr : 0 < r) : ∃ δ : ℝ, 0 < δ ∧ ∀ {c : Side} (V : Config G c),
    (∀ i, G.chord (V i) ≤ δ) → ∃ z : Vec G c 1, ‖z‖ < r ∧ increment 1 (paint G c z) = V := by
  obtain ⟨D,e,hD,he,hv⟩ := Next.Fluctuations.log_chart_cost G
  refine ⟨min e (r/2/D),lt_min he (by positivity),?_⟩
  intro c V hV
  let b : Directions G c := fun i => G.plog (G.mat (V i))
  have hz i := hv (V i) ((hV i).trans (min_le_left ..))
  refine ⟨(paint G c).symm b,lt_of_le_of_lt (b:=r/2) ?_ (half_lt_self hr), by
    rw [ContinuousLinearEquiv.apply_symm_apply]; funext i; simp [increment,b,(hz i).1]⟩
  apply (pi_norm_le_iff_of_nonneg (half_pos hr).le).mpr; intro i
  change ‖b (edge i) i.2.2‖ ≤ _
  refine (color_le (G:=G) ..).trans (((hz _).2).trans ?_)
  rw [mul_comm D, ← le_div_iff₀ hD]; exact (hV _).trans (min_le_right ..)

abbrev togetherAt (n : ℕ) (d : ℝ) := narrow n d / (2*(n+3:ℕ))

variable {ι : Type*} [Fintype ι] {e : ι → raw G f} {m h : ℕ → ℝ} {F : Forest S.ratio → Config G c → Matrix ι ι ℝ}
lemma boughtHere (he : Injective e) (hk : k ≤ n) (hd : 0 < d) (p : Paid S (home S ∘ e) k (narrow n d) d γ m h F V)
    (hγ : d ≤ γ) : Receipt S (home S ∘ e) k (togetherAt n d) (coins G S.patch (togetherAt n d)) m h F V := by
  have hs : 0 < togetherAt n d := div_pos (narrow_pos n hd) (by positivity)
  have he' : 2*(n+3:ℕ)*togetherAt n d ≤ narrow n d := by rw [mul_comm]; exact (div_mul_cancel₀ _ (by positivity)).le
  refine p.bought hs (le_trans (by gcongr) he') (narrow_le n hd.le) ((narrow_le n hd.le).trans hγ)
    ((torusPay_nn _ _ hs).trans (le_max_left ..)) (((home_volume _ 1 _ hs).comp he).le (le_max_left ..))
    ((volume c _ _ hs).le (le_max_right ..))

variable (V) in
structure Trade (S : StepData c f) (t : S.Choices) (p : Clip) (W : PathData G) (σ M C : ℝ) (k n : ℕ) : Prop where
  prices (u : ℝ) : 0 ≤ u → ∀ R : Admit,
    let d := stage S.patch G S.kernel p σ n C M
    let E := purse S.patch G S.kernel p σ n C M; let K := volumeCost G S.patch d
    let F R := paddedGram S t p W R; let s := togetherAt n d; let Y := coins G S.patch s
    let basis (m e : ℕ → ℝ) (T : Forest S.ratio → Config G c → Matrix (raw G f) (raw G f) ℝ) := Receipt S (home S) k s Y m e T V
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → raw G f}, Injective e →
      Receipt S (home S ∘ e) k s Y (fun j => offFee G j * charges j 1 E (drain u)) (fun j => offFee G j * (E*drain u*drain u))
        (fun T => resolver (fun V => (F R T V).submatrix e e) u) V) ∧
    (∀ (R : ℕ), let fee j := offFee G j * cutback S.patch G S.kernel p σ n R C M u
      basis fee fee (fun T => resolver (F (shorter R) T) u - resolver (F all T) u)) ∧
    ∀ {I : raw G f → Type} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)] (Z : Survey I),
      basis (fun j => offFee G j * (K*charges j 1 E (drain u))) (fun j => offFee G j * (K*(E*drain u*drain u)))
        (fun T => columns Z (F R T) u) ∧ ∀ ρ, Z.Near (native c) (home S) ρ →
          let fee j := offFee G j * crumb S.patch G S.kernel p σ n C M ρ u
          basis fee fee (fun T => columns Z (F R T) u - resolver (F R T) u)




end YM.SelectedOrderedKernels.Small
