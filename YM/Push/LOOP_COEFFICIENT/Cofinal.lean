import YM.Push.LOOP_COEFFICIENT.Samples

/-!
# Actual two-wave comparisons through cofinal periods

Real frequencies first; no asserted Ward identity on an interpolated mesh.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Bloch Laurent Lattice Matrix Complex
open scoped Topology BigOperators ContDiff ComplexConjugate

private def raster (p : Momentum) (n : Side) : Cover := fun i => ⌊(p i).re * n.val / (2*Real.pi)⌋

def freq (p : Momentum) (n : Side) := quant n (raster p n)
def freqSite (p : Momentum) (n : Side) := wrap n (raster p n)
lemma freq_match (p : Momentum) (n : Side) : Matches (freq p n) (freqSite p n) := quant_matches ..

variable {s : ℕ → Side}

def Expands (s : ℕ → Side) := Tendsto (fun i => (s i).val) atTop atTop

lemma freq_limit (hs : Expands s) {p : Momentum} (hp : star p = p) : Tendsto (fun i => freq p (s i)) atTop (𝓝 p) := by
  let r := 2*Real.pi
  have hr : 0 < r := by unfold r; positivity
  apply tendsto_pi_nhds.mpr; intro i
  have he (n : Side) : (p i).re - r/n.val ≤ r*(raster p n i)/n.val ∧ r*(raster p n i)/n.val ≤ (p i).re := by
    rw [le_div_iff₀ (side_pos n), div_le_iff₀ (side_pos n)]; constructor
    · rw [sub_mul, div_mul_cancel₀ _ (side_pos n).ne']; unfold raster
      have h := Int.lt_floor_add_one ((p i).re*n.val/r)
      rw [div_lt_iff₀ hr,add_mul] at h; linarith
    unfold raster; have h := Int.floor_le ((p i).re*n.val/r)
    rw [le_div_iff₀ hr] at h; linarith
  have hW : Tendsto (fun j : ℕ => r / (s j).val) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hs)
  have hT := tendsto_of_tendsto_of_tendsto_of_le_of_le (f:=fun j : ℕ => r*(raster p (s j) i)/(s j).val)
    (show Tendsto _ atTop (𝓝 _) by simpa only [sub_zero] using! (tendsto_const_nhds (x:=(p i).re)).sub hW) tendsto_const_nhds
    (fun j => (he (s j)).1) (fun j => (he (s j)).2)
  have hx : conj (p i) = p i := congr_fun hp i
  rw [Complex.conj_eq_iff_re] at hx
  rw [← hx]; refine ((continuous_ofReal.tendsto _).comp hT).congr (fun b => ?_)
  simp only [Function.comp_apply, r, ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_intCast, ofReal_natCast, freq, quant,reciprocal,Pi.smul_apply,smul_eq_mul]; rw [inv_mul_eq_div]

variable {a b : Type} [DecidableEq a] [DecidableEq b]
  {E F : ℕ → Type} [∀ i, Fintype (E i)] [∀ i, Fintype (F i)] {A : ∀ i, Grid (s i) (E i) a} {B : ∀ i, Grid (s i) (F i) b}
  {X : ∀ i, Matrix (E i) (F i) ℂ} {V : Momentum → Matrix a b ℂ}

def Mirrors (A : ∀ i, Grid (s i) (E i) a) (B : ∀ i, Grid (s i) (F i) b) (X : ∀ i, Matrix (E i) (F i) ℂ) (V : Momentum → Matrix a b ℂ) :=
    ∀ (p : Momentum) (f : ℕ → Momentum) (k : ∀ i, Site (s i)), star p=p → Tendsto f atTop (𝓝 p) → (∀ i, Matches (f i) (k i)) →
      Tendsto (fun i => sample (A i) (B i) (X i) (-k i) (k i)) atTop (𝓝 (V p))

lemma exp_error_limit (hs : Expands s) {η : ℝ} (hη : 0<η) (C : ℝ) :
    Tendsto (fun i => C*Real.exp (-η*(s i).val)) atTop (𝓝 0) := by
  simpa only [neg_mul,mul_zero] using! ((Real.tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot).comp
    (Tendsto.const_mul_atTop hη (tendsto_natCast_atTop_atTop.comp hs)))).const_mul C)

lemma compares_mirror {tol : ℕ → ℝ} (h : ∀ i, Compares (A i) (B i) (X i) V (tol i))
    (hv : ∀ p, star p = p → ContinuousAt V p) (hT : Tendsto tol atTop (𝓝 0)) : Mirrors A B X V := by
  intro p f k hp hf hk
  apply tendsto_pi_nhds.mpr; intro j; apply tendsto_pi_nhds.mpr; intro l
  let U i := sample (A i) (B i) (X i) (-k i) (k i)
  have he : Tendsto (fun i => U i j l - V (f i) j l) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr <|
    squeeze_zero (fun i => norm_nonneg _) (fun i => (h i).price (hk i) j l) hT
  have hL := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ((hv p hp).tendsto.comp hf) j) l
  simpa only [Function.comp_apply,sub_add_cancel,zero_add,U] using! he.add hL

lemma Mirrors.unique {W : Momentum → Matrix a b ℂ} (h : Mirrors A B X V) (h' : Mirrors A B X W) (hs : Expands s) {p : Momentum} (hp : star p = p) : V p = W p :=
    tendsto_nhds_unique (h p _ _ hp (freq_limit hs hp) (fun _ => freq_match ..)) (h' p _ _ hp (freq_limit hs hp) (fun _ => freq_match ..))
end YM.Push.Loops
