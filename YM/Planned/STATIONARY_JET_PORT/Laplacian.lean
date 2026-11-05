import YM.Planned.STATIONARY_JET_PORT.Lines
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Progress.STATIONARY_SCENES.Green


set_option warningAsError false
/-!
# Pricing the unperturbed (zeroth in field differentiation) lines

Route through the earlier `Green.inverse` weighted argument, obtaining a
rate uniform also in the real nonnegative shift. In particular this can be
used with Uniform's Tame powers even on nonflat collars. `H` is the active
uncut real Hessian in use cases, NOT a masked Laplacian. Empty sigma is fine.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Filter Function Lattice Metric Matrix Push.Uniform
open Progress.StationaryScenes.Green
open scoped Topology ContDiff BigOperators Classical

variable {σ τ : Type} {n : Side} [Fintype τ] [Fintype σ]
    {l : τ → Site n} {A : Matrix τ τ ℝ} {r M C : ℝ}

/-- On rates already strictly positive. No shorthand assuming tower cost. -/
def console (r C : ℝ) (K : ℕ) := 1+C*((K:ℝ)*countCost (r/2))
def diminish (r M C : ℝ) (K : ℕ) := min 1 ((M/2)/console r C K)
def groundRate (r M C : ℝ) (K : ℕ) := diminish r M C K * (r/2)
def grounding (M : ℝ) := (min 1 (M/2))⁻¹
lemma console_pos (hr : 0<r) (hc : 0<C) (K : ℕ) : 0<console r C K := by
  have h := count_pos (half_pos hr); unfold console; positivity
lemma diminish_pos (hr : 0<r) (hM : 0<M) (hC : 0<C) (K : ℕ) : 0<diminish r M C K :=
  lt_min zero_lt_one (div_pos (half_pos hM) (console_pos hr hC K))
lemma groundRate_pos (hr : 0<r) (hM : 0<M) (hC : 0<C) (K : ℕ) : 0<groundRate r M C K :=
  mul_pos (diminish_pos hr hM hC K) (half_pos hr)
lemma grounding_pos (hM : 0<M) : 0<grounding M := inv_pos.mpr (lt_min zero_lt_one (half_pos hM))

lemma ticketBoth (h : Sealed l r A C) (hr : 0<r) (hc : 0<C) {K : ℕ} (hm : Multiplicity l K) :
    Both l l A (r/2) (console r C K) (console r C K) := by
  have he (A) (H : Sealed l r A C) (i : τ) := H.weighted hc.le hm (half_lt_self hr) i
  have hh (A) (H : Sealed l r A C) : Rows l l A (r/2) (console r C K) := by
    intro i
    unfold wt
    simp_rw [mul_comm (Real.exp _)]; apply (he _ H i).trans
    rw [show r-r/2=r/2 by ring]; exact le_add_of_nonneg_left zero_le_one
  exact ⟨hh _ h, hh _ h.tran⟩

section restriction
variable [DecidableEq σ] (i : σ ↪ τ)

omit [DecidableEq σ] in
lemma charge_sub (h : Charge A M) : Charge (A.submatrix i i) M := by
  change ∀ _, _
  have he : Bottom A M := fun x => by simpa only [dotProduct,pow_two] using h x
  have ht := Bottom.restrict he i; intro z; simpa only [dotProduct,pow_two] using ht z

/-- Full two-sided and old weighted Green's-function port on submatrix,
strong positive charge (hence log safe); both polynomially priced. -/
theorem ground (hA : A.IsHermitian) (h : Charge A M) (hz : Sealed l r A C)
    (hr : 0<r) (hm : 0<M) (hc : 0<C) {K : ℕ} (hK : Multiplicity l K) (u : ℝ) (hu : 0 ≤ u) :
    let S := A.submatrix i i + u • (1 : Matrix σ σ ℝ)
    Charge S (M+u) ∧ S.IsHermitian ∧ 0<S.det ∧ S⁻¹*S=1 ∧ S*S⁻¹=1 ∧
      Sealed (l ∘ i) (groundRate r M C K) S⁻¹ (grounding M/(1+u)) ∧
      (∀ x, (∑ j, (S⁻¹ *ᵥ x) j ^ 2) ≤ (M+u)⁻¹^2 * ∑ j, (x j)^2) := by
  intro S
  have hZ := charge_sub i h
  have hv : Charge S (M+u) := by
    intro x
    unfold S; rw [Matrix.add_mulVec,dotProduct_add,Matrix.smul_mulVec,one_mulVec,dotProduct_smul,add_mul]
    rw [show x ⬝ᵥ x=∑ j,x j ^ 2 from by unfold dotProduct; simp only [pow_two]]
    exact add_le_add_left (hZ x) _
  have hS : S.IsHermitian := (hA.submatrix i).add (show (u • (1 : Matrix σ σ ℝ)).IsHermitian by
    unfold IsHermitian; rw [conjTranspose_smul,star_trivial]; simp)
  have hd : 0<S.det := (hv.positive hS (by positivity)).det_pos
  have hi := isUnit_iff_ne_zero.mpr hd.ne'
  obtain ⟨hh,h'⟩ := ticketBoth hz hr hc hK
  let a := diminish r M C K
  let B := console r C K
  have hp : Bottom A M := fun x => by simpa only [dotProduct,pow_two] using h x
  obtain ⟨hAA,hAR,hR⟩ := Progress.StationaryScenes.Green.inverse (half_pos hr).le hm (diminish_pos hr hm hc K).le
    (show a ≤ 1 from min_le_left ..) ((le_div_iff₀ (console_pos hr hc K)).mp (show a ≤ M/2/B from min_le_right ..))
    (hA.submatrix i) (hp.restrict i) (h:=⟨hh.restrict i i,h'.restrict i i⟩) u hu
  refine ⟨hv,hS,hd,hAR,hAA,fun x y => ?_, hv.energy_inverse (add_pos_of_pos_of_nonneg hm hu) hi⟩
  have hs := hR x y
  let t := wt (a*(r/2)) (l (i x)) (l (i y))
  have ht : 0<t := Real.exp_pos _
  change t*|(S⁻¹) x y| ≤ _ at hs
  rw [_root_.mul_inv,← div_eq_mul_inv] at hs
  rw [show Decay (groundRate r M C K) ((l ∘ i) x) ((l ∘ i) y) = t⁻¹ by unfold t wt Decay; dsimp [groundRate,a]; rw [neg_mul,Real.exp_neg],
    ← div_eq_mul_inv, le_div_iff₀ ht,mul_comm]; exact hs
end restriction

section Atlas
variable {ι : Type} [Fintype ι] {m : ι → Site n} {F : Positions ι → Matrix τ τ ℝ} [DecidableEq σ]
    {x : Positions ι} {N K : ℕ}

/-- Shift doesn't modify any nonzero derivative invoice. -/
def caisson (F : Positions ι → Matrix τ τ ℝ) (u : ℝ) (i : σ ↪ τ) (x : Positions ι) :=
  (F x).submatrix i i + u • (1 : Matrix σ σ ℝ)
omit [Fintype σ] [Fintype τ] in
lemma bornMatrix.collar (h : bornMatrix F x) (u : ℝ) (i : σ ↪ τ) : bornMatrix (caisson F u i) x :=
  fun j k => by unfold caisson; simp only [Matrix.add_apply, Matrix.submatrix_apply]; exact (h _ _).add contDiffAt_const

def ruling (r M C : ℝ) (K : ℕ) := min r (groundRate r M C K)
lemma ruling_pos (hr : 0<r) (hm : 0<M) (hc : 0<C) (K : ℕ) : 0<ruling r M C K :=
  lt_min hr (groundRate_pos hr hm hc K)

theorem rebuild (hr : 0<r) (hm : 0<M) (hc : 0<C) (hK : Multiplicity l K)
    (hF : bornMatrix F x) (hH : (F x).IsHermitian) (hW : Charge (F x) M)
    (h : Cable m l l none r N F x C) (i : σ ↪ τ) (u : ℝ) (hu : 0 ≤ u) :
    let T := caisson F u i
    let a := ruling r M C K; let b := l ∘ i
    Charge (T x) (M+u) ∧ (T x).IsHermitian ∧ 0<(T x).det ∧ (T x)⁻¹*(T x)=1 ∧ (T x)*(T x)⁻¹=1 ∧
    Sealed b (groundRate r M C K) (T x)⁻¹ (grounding M/(1+u)) ∧
      bornMatrix (fun y => (T y)⁻¹) x ∧
    (∀ k ≤ N, Cable m b b none (weakLine a k) k (fun y => (T y)⁻¹) x (lineCost a C (grounding M) K k/(1+u))) ∧
      (∀ v, (∑ j, ((T x)⁻¹ *ᵥ v) j ^ 2) ≤ (M+u)⁻¹^2 * ∑ j, (v j)^2) := by
  intro T a b
  have hh : Sealed l r (F x) C := fun j k => by
    simpa only [entry,iteratedFDeriv_zero_apply,Real.norm_eq_abs,thread_none,spanSites, Fin.sum_univ_zero,
      Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using h j k 0 (Nat.zero_le _) Fin.elim0
  obtain ⟨hB,hM,hD,h₁,h₂,hS,hQ⟩ := ground i hH hW hh hr hm hc hK u hu
  have hT := hF.collar u i
  refine ⟨hB,hM,hD,h₁,h₂,hS,hT.inverse hD.ne',fun k hk => ?_,hQ⟩
  apply inverse_lines hT hD.ne' (hK.comp i.injective) (ruling_pos hr hm hc K) hc (grounding_pos hm) (1+u) (by linarith) _ _ k hk
  · intro j w; exact (hS j w).trans (mul_le_mul_of_nonneg_left
      (decay_mono (show a ≤ groundRate r M C K from min_le_right ..) _ _)
      (div_nonneg (grounding_pos hm).le (by positivity)))
  intro k' hk' d j w
  have he : (fun y => finger T d y j w) =ᶠ[𝓝 x] (fun y => finger F d y (i j) (i w)) := by
    filter_upwards [(hF (i j) (i w)).eventually (by simp)] with z hz
    unfold finger T coordinate caisson; simp only [of_apply,Matrix.add_apply,Matrix.submatrix_apply];
    rw [fderiv_fun_add (hz.differentiableAt (by simp)) (differentiableAt_const _),fderiv_const_apply,add_zero]
  intro g hg q
  unfold entry; rw [(he.iteratedFDeriv ℝ g).eq_of_nhds]
  exact (((h.takeFinger hF hk' d).rate hc.le (show a ≤ r from min_le_left ..)) (i j) (i w)) g hg q
end Atlas
end YM.Planned.JetPort
