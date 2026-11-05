import YM.Push.FREE_RESOLVENT.SmallArc

/-!
# Budget the finite-radius and uncut affine precision at the flat B

No masks inside the cell reading the inverse; T, r and measurement
orientations fixed through germ. True lengths even for periodized paths,
the input not from periodized estimates. Preserve the exponential costs on
B-*indices* even across radius truncations on each path. All prices post-L
(and may depend on k) but present as explicit symbolic bounds in the given
pre-L prices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set Mark
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Bundle
variable {ι κ μ τ X E : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Mark τ X} {D : Cost X} {v : τ → E} {a : ι → X} {b : κ → X} {k : ℕ} {M N s : ℝ}
variable {F H : E → Matrix ι κ ℝ} {x : E} (hF : Bundle v C D a b F x k s M)

def switch (ι κ : Type*) [Fintype ι] [Fintype κ] : Matrix ι κ ℝ →L[ℝ] Matrix κ ι ℝ := LinearMap.toContinuousLinearMap
  ({ toFun := Matrix.transpose, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } : Matrix ι κ ℝ →ₗ[ℝ] Matrix κ ι ℝ)

include hF
lemma transpose : Bundle v C D b a (fun x => (F x).transpose) x k s M := by
  constructor
  · exact (switch ι κ).contDiff.contDiffAt.comp x hF.smooth
  intro l hl
  erw [show jet v _ l x = (jet v F l x).transpose from jet_linear v l (switch ι κ) (smooth_of_le hF.smooth hl)]
  exact (hF.bound l hl).flip

lemma one_add (hH : Bundle v C D a b H x k s N) : Bundle v C D a b (fun x => F x+H x) x k s (M+N) := by
  constructor
  · exact hF.smooth.add hH.smooth
  intro l hl
  rw [jet_add v l (smooth_of_le hF.smooth hl) (smooth_of_le hH.smooth hl)]
  exact (hF.bound l hl).add (hH.bound l hl)

omit hF
lemma rated {α β : Type*} [Fintype α] [Fintype β] {a : α → X} {b : β → X} {A : Matrix α β ℝ}
      {l : List τ} (r : ℝ) (H : C.Rates D a b l s M A) : C.Rates D a b l s (|r| * M) (r • A) := by
    constructor; intro i
    simp_rw [Matrix.smul_apply, smul_eq_mul, abs_mul, mul_left_comm (D.weight _ _ _) |r|,← Finset.mul_sum,
      mul_left_comm (C.pay l (a i)) |r|]
    exact mul_le_mul_of_nonneg_left (H.rows i) (abs_nonneg _)

lemma scale (hF : Bundle v C D a b F x k s M) (r : ℝ) : Bundle v C D a b (fun x => r • F x) x k s (|r| * M) := by
  constructor
  · exact hF.smooth.const_smul r
  intro l hl
  have he := hF.bound l hl
  erw [show jet v _ l x=r • (jet v F l x) from jet_linear v l (r • ContinuousLinearMap.id ℝ (Matrix ι κ ℝ)) (smooth_of_le hF.smooth hl)]
  exact ⟨rated r he.row,rated r he.col⟩

lemma compress [Fintype μ] {F : E → Matrix ι ι ℝ} {x : E} (hF : Bundle v C D a a F x k s M)
    {u : μ → ι} (hu : Injective u) : Bundle v C D (a ∘ u) (a ∘ u) (limitTo F u) x k s M := by
  constructor
  · exact (selectL u).contDiff.contDiffAt.comp x hF.smooth
  intro l hl
  rw [compressed u l (smooth_of_le hF.smooth hl)]
  exact (hF.bound l hl).submatrix hu hu

lemma sum_all {θ : Type*} (T : Finset θ) {F : θ → E → Matrix ι κ ℝ} (n : θ → ℝ) (h : ∀ i ∈ T,
    Bundle v C D a b (F i) x k s (n i)) : Bundle v C D a b (fun y => ∑ i ∈ T, F i y) x k s (∑ i ∈ T, n i) := by
  constructor
  · exact ContDiffAt.sum fun i hi => (h i hi).smooth
  intro l hl
  rw [jet_sum v l T F (fun i hi => smooth_of_le (h i hi).smooth hl)]
  exact Bill.sum_budget _ _ _ fun i hi => (h i hi).bound l hl
end Bundle

namespace Affine
variable {G : Gauge} {p : Clip} {c f : Side} {k : ℕ} {W : PathData G} {A σ d : ℝ}

/-- Rate options for input with true-length sums at σ. One multiplication
cost layer per composite row, one per stack Gram. Use Rate.tier for the
remaining comparisons, room eventually strictly below that at inverse. -/
def tier (σ : ℝ) (k : ℕ) := σ/(16*(k+1:ℕ))
def wider (σ : ℝ) (k : ℕ) := tier σ k+(k:ℝ)*tier σ k
def staging (σ : ℝ) (k : ℕ) := wider σ k+(k:ℝ)*tier σ k
lemma ordering (h : 0 < σ) (k : ℕ) : 0 < tier σ k ∧ tier σ k ≤ wider σ k ∧ wider σ k ≤ staging σ k ∧ 2*staging σ k+2*k*tier σ k ≤ σ/2 := by
  have ht : 0 < tier σ k := div_pos h (by positivity)
  have he : 0 ≤ (k:ℝ)*tier σ k := mul_nonneg (by positivity) ht.le
  refine ⟨ht, le_add_of_nonneg_right he, le_add_of_nonneg_right he, ?_⟩
  have hh : tier σ k*(16*(k+1:ℕ))=σ := div_mul_cancel₀ _ (by positivity)
  unfold staging wider; push_cast at *; linarith only [he,ht,hh]
lemma staging_pos (h : 0 < σ) (k : ℕ) : 0 < staging σ k := (ordering h k).1.trans_le ((ordering h k).2.1.trans (ordering h k).2.2.1)

/-- post-L no-hole costs -/
def longPrice (G : Gauge) (P : Patch) (k : ℕ) (M σ : ℝ) :=
  torusPay (Co P.L (PAC G 2)) (staging σ k) * (M*elbow G k (σ/4))
def phasePrice (G : Gauge) (P : Patch) (K : KernelChoices) (k : ℕ) (M σ : ℝ) :=
  tagPrice 1 k (longPrice G P k M σ) (lowBudget G P K (staging σ k) k)
def stageCost (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (k : ℕ) (M σ : ℝ) :=
  let x := lowBudget G P K (staging σ k) k; let y := phasePrice G P K k M σ; let z := highBudget G P K (wider σ k) k
  p.direct * tagPrice 1 k x x + tagPrice 1 k y y + K.penalty * tagPrice 1 k z z
lemma longPrice_nn (G : Gauge) (P : Patch) {k : ℕ} (hs : 0 < σ) (ha : 0 ≤ A) : 0 ≤ longPrice G P k A σ :=
  mul_nonneg (torusPay_nn _ _ (staging_pos hs k)) (mul_nonneg ha (elbow_nn ..))
lemma tag_nn {k : ℕ} {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ tagPrice 1 k v w := by unfold tagPrice; positivity
lemma phase_nn (G : Gauge) (P : Patch) (K : KernelChoices) {k : ℕ} (hs : 0 < σ) (ha : 0 ≤ A) : 0 ≤ phasePrice G P K k A σ :=
  tag_nn (longPrice_nn G P hs ha) (low_nn k _ _ (staging_pos hs k))
lemma stage_nn (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) {k : ℕ} (hs : 0 < σ) (ha : 0 ≤ A) :
    0 ≤ stageCost G P K p k A σ := by
  have hw := (ordering hs k).1.trans_le (ordering hs k).2.1
  have h1 := low_nn (G:=G) k P K (staging_pos hs k); have h2 := phase_nn G P K (k:=k) hs ha; have h3 := high_nn (G:=G) k P K hw
  exact add_nonneg (add_nonneg (mul_nonneg p.quadratic_pos.le (tag_nn h1 h1)) (tag_nn h2 h2)) (mul_nonneg K.penalty_pos.le (tag_nn h3 h3))

abbrev gram (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) := fun B => tracks S s W r B * response S s B

section pay
variable (S : StepData c f) (hm : 1 < c.val) (s : Signed)
variable (h : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : 0 ≤ d) (hx : d ≤ tier σ k)
include hm h ha hW he hx

lemma gram_paid (r : Admit) (R : ℕ) (hr : ∀ z, r z=true → R ≤ z.length) :
    Bundle (ray G c) (marks G c d) (native c) (named S s) (home S) (gram S s W r) 0 k (wider σ k)
      (Real.exp (-(σ/4)*R)*phasePrice G S.patch S.kernel k A σ) := by
  obtain ⟨h1,h2,h3,h4⟩ := ordering h k; have hS := h1.trans_le (h2.trans h3)
  have hw : 0 ≤ (k:ℝ) := by positivity
  have hy : 2*staging σ k+2*k*d ≤ σ/2 := by nlinarith only [h4,mul_le_mul_of_nonneg_left hx hw]
  have hv : wider σ k+k*d ≤ staging σ k := add_le_add_right (mul_le_mul_of_nonneg_left hx hw) _
  have hg := track_rows S s W r k h hW ha he hS hy R hr
  apply (hg.multiply (price_D (G:=G) S s hm k hS he ((hx.trans h2).trans h3)) (position_move _ _ he)
    he le_rfl (by have := torusPay_nn (Co S.patch.L (PAC G 2)) _ hS; have := elbow_nn G k (σ/4); positivity)
      (low_nn _ _ _ hS) (h1.le.trans h2) hv).mono le_rfl
  unfold phasePrice tagPrice longPrice; apply le_of_eq; ring
lemma funding (r : Admit) : Bundle (ray G c) (marks G c d) (native c) (named S s) (home S) (gram S s W r) 0 k (wider σ k)
    (phasePrice G S.patch S.kernel k A σ) := by
  simpa only [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using gram_paid S hm s h ha hW he hx r 0 (fun x _ => Nat.zero_le _)

lemma priced_channel (hr : S.patch.Branches S.kernel G) (p : Clip) (r : Admit) (t : S.Choices) :
    Bundle (ray G c) (marks G c d) (native c) (home S) (home S) (channel S s t p W r) 0 k (tier σ k)
      (stageCost G S.patch S.kernel p k A σ) := by
  obtain ⟨h1,h2,h3,h4⟩ := ordering h k
  have hS := h1.trans_le (h2.trans h3); have hT := h1.trans_le h2
  have hu := funding S hm s h ha hW he hx r
  have hw := (price_D (G:=G) S s hm k hS he ((hx.trans h2).trans h3)).mono h3 le_rfl
  have hv := price_Q S s t hm k hr hT he (hx.trans h2)
  have he' : tier σ k+k*d ≤ wider σ k := add_le_add_right (mul_le_mul_of_nonneg_left hx (by positivity)) _
  have hu' := phase_nn G S.patch S.kernel (k:=k) h ha
  have hx' := low_nn (G:=G) k S.patch S.kernel hS; have ht' := high_nn (G:=G) k S.patch S.kernel hT
  -- squareQ
  have H := (((hw.transpose.multiply hw (position_move _ _ he) he le_rfl hx' hx' h1.le he').scale p.direct).one_add
    (hu.transpose.multiply hu (position_move _ _ he) he le_rfl hu' hu' h1.le he')).one_add
      ((hv.transpose.multiply hv (position_move _ _ he) he le_rfl ht' ht' h1.le he').scale S.kernel.penalty)
  rw [abs_of_pos p.quadratic_pos, abs_of_pos S.kernel.penalty_pos] at H; exact H

lemma priceBlock (hr : S.patch.Branches S.kernel G) (p : Clip) (r : Admit) (t : S.Choices) :
    Bundle (ray G c) (marks G c d) (native c) (home S) (home S) (block S t p W r) 0 k (tier σ k)
      (stageCost G S.patch S.kernel p k A σ) := by
  have H := (Bundle.sum_all Finset.univ _ (fun s _ => priced_channel S hm s h ha hW he hx hr p r t)).scale (Fintype.card Signed:ℝ)⁻¹
  have hh : 0 < (Fintype.card Signed : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ, abs_of_pos (inv_pos.mpr hh), ← mul_assoc,inv_mul_cancel₀ hh.ne',one_mul] at H
  exact H

lemma priority (hr : S.patch.Branches S.kernel G) (T : Forest S.ratio) (p : Clip) (r : Admit) (t : S.Choices) :
    Bundle (ray G c) (marks G c d) (native c) (theta _ T) (theta _ T) (primary S T t p W r) 0 k (tier σ k)
      (stageCost G S.patch S.kernel p k A σ) := (priceBlock S hm h ha hW he hx hr p r t).compress (plant_inj T)

-- telescope rather than losing exponential on path subtraction
lemma tail_channel (R : ℕ) (p : Clip) (t : S.Choices) :
    let r := phasePrice G S.patch S.kernel k A σ
    Bundle (ray G c) (marks G c d) (native c) (home S) (home S)
      (fun x => channel S s t p W all x - channel S s t p W (shorter R) x) 0 k (tier σ k)
      (Real.exp (-(σ/4)*R) * (2*tagPrice 1 k r r)) := by
  obtain ⟨h1,h2,h3,h4⟩ := ordering h k
  intro r; let F := gram S s W all; let P := gram S s W (longer R); let Q := gram S s W (shorter R)
  have he' : tier σ k+k*d ≤ wider σ k := add_le_add_right (mul_le_mul_of_nonneg_left hx (by positivity)) _
  let θ := Real.exp (-(σ/4)*R)
  have hh (x : RG.Slot) (h : longer R x=true) : R ≤ x.length := by simp only [longer,shorter,Bool.not_eq_true',decide_eq_false_iff_not] at h; omega
  have hP := gram_paid S hm s h ha hW he hx (longer R) R hh
  have hF := funding S hm s h ha hW he hx all
  have hQ := funding S hm s h ha hW he hx (shorter R)
  have hv : 0 ≤ r := phase_nn _ _ _ h ha
  have hθ : 0 ≤ θ*r := mul_nonneg (Real.exp_pos _).le hv
  have hM := (hF.transpose.multiply hP (position_move _ _ he) he le_rfl hv hθ h1.le he').one_add
        (hP.transpose.multiply hQ (position_move _ _ he) he le_rfl hθ hv h1.le he')
  apply Bundle.glue (A:=fun x => (F x).transpose*P x+(P x).transpose*Q x) (hM.mono le_rfl ?_)
  · filter_upwards [remaining_work S s W R h hW] with x hh
    have he : F x=Q x+P x := by unfold F Q P gram; rw [hh, Matrix.add_mul]
    unfold channel; change _ = (_ + squareQ (F x) + _) - (_ + squareQ (Q x) + _)
    rw [he,add_sub_add_right_eq_sub, add_sub_add_left_eq_sub]; unfold squareQ; rw [Matrix.mul_add, transpose_add]; simp only [Matrix.add_mul]; abel
  unfold tagPrice; change 2^k* (1^k*r*(θ*r))+2^k*(1^k*(θ*r)*r) ≤ θ*(2*( _ ))
  apply le_of_eq; ring

lemma tail_block (R : ℕ) (p : Clip) (t : S.Choices) :
    let r := phasePrice G S.patch S.kernel k A σ
    Bundle (ray G c) (marks G c d) (native c) (home S) (home S)
      (fun x => block S t p W all x-block S t p W (shorter R) x) 0 k (tier σ k)
      (Real.exp (-(σ/4)*R) * (2*tagPrice 1 k r r)) := by
  intro r
  have H := (Bundle.sum_all Finset.univ _ (fun s _ => tail_channel S hm s h ha hW he hx R p t)).scale (Fintype.card Signed:ℝ)⁻¹
  have hh : 0 < (Fintype.card Signed : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ, abs_of_pos (inv_pos.mpr hh), ← mul_assoc,inv_mul_cancel₀ hh.ne',one_mul] at H
  simp_rw [Finset.sum_sub_distrib, smul_sub] at H; exact H
lemma tail_primary (R : ℕ) (T : Forest S.ratio) (p : Clip) (t : S.Choices) :
    let r := phasePrice G S.patch S.kernel k A σ
    Bundle (ray G c) (marks G c d) (native c) (theta _ T) (theta _ T)
      (primary S T t p W all-primary S T t p W (shorter R)) 0 k (tier σ k)
      (Real.exp (-(σ/4)*R) * (2*tagPrice 1 k r r)) := (tail_block S hm h ha hW he hx R p t).compress (plant_inj T)
end pay
end YM.FreeResolvent.Affine
