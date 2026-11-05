import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Creed

/-!
# Quantitative launch for marks

Positive on the *actual* completed coordinates. For price of
directional log change this uses TestD receipt only on the built AFull
Gram. *No permission* to pass through changing Σ*. At hard tests on V
use fixed Stores kept, not changing flags during any differential. Even on
equality, h demands validity on the actual extension whose derivative is used --
doesn't assert every family has licensed analytic extensions. Price procurement
only required at the point, not neighborhood bounds, not invertibility at all y.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Physical
open Function Filter Set Matrix MeasureTheory Lattice RG Wilson Pressure Tree
open Next.SectorChange Completion FreeResolvent Ink TestD Differential
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {σ M η ε U a C d b b' x : ℝ} {k l B : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : Type*} {H : Mark τ (Site c)} {v : τ → E} {z : E}
variable {T : Tube G S} {A : Stores S} {F : Forest S.ratio} {K : S.Choices} {V : E→Config G c}



lemma canons (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (V : Config G c) (K : S.Choices) :
    Matrix.IsHermitian (AFull T A F x V K) := by
  apply Matrix.IsHermitian.submatrix
  apply Matrix.isHermitian_iff_isSymm.mpr
  unfold Matrix.IsSymm wide Rows.gram; simp [Matrix.fromBlocks_transpose]



omit [NormedSpace ℝ E] in
lemma follows {v C η b : ℝ} (J : Certified S T x v C η b) (A : Stores S) (F : Forest S.ratio)
    (K : S.Choices) (V : Config G c) (hp : A.flags=RG.flags (temp x) V) : FreeResolvent.Gap (AFull T A F x V K) (min η 1) := by
  have hh := J.text A F K V hp
  let Q := Rows.gram T x V K (shots S x) A F
  let e := sorted A F (x:=x) (G:=G)
  exact (gapped' _ (wide_gap (Matrix.isHermitian_iff_isSymm.mp hh.2.1.isHermitian) hh.1 (β:=vacant A F x G)).2).submatrix e.symm e.symm.injective



section sales
namespace Stipend
variable (J : Stipend G S l k a σ M η U C b b' d (radiusB x))
    {A : E→Square (Key G f)} (h : Speech (native c) (place S) (windows S x) H v A z k (faceBudget σ M η k) U C (currency b (radiusB x)) ε)
    (he : ∀ᶠ y in 𝓝 z,Aperture (place S) (radiusB x) (windows S x) (A y))
variable {L : List τ}

private lemma blank (v : τ→E) (L : List τ) (z : E) : jet v (fun _=> (0:ℝ)) L z=0 := by
  by_cases h : L=[]
  · subst L; rw [zeroth]
  rw [jet_const v _ h]

lemma betabill (B : ℕ) (p : Key G f→Site c) (s : ℝ) {q q' : ℝ} (h : q ≤ q') (hq : 0≤q) (hC : 0≤C)
    {n : ℕ} (z : Letter (Key G f) n) : ticket p B s C q z ≤ ticket p B s C q' z := by
  unfold ticket; dsimp only; split
  next hh =>
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq h _) hC)
      (road_pos _ _ (fun _ _=>fares_nn ..) (fun _ _=> fares_nn ..) ..)
  exact le_rfl
include J h he

variable [FiniteDimensional ℝ E]



omit [FiniteDimensional ℝ E] in
lemma bought (hl : L.length ≤ k) (w : Letter (Key G f) 0) :
    let f y:=errata (windows S x) (A y) w
    ContDiffAt ℝ k f z ∧ H.pay L (place S w.2.1)*|jet v f L z| ≤ ticket (place S) (radiusB x) (faceBudget σ M η k) C (currency b' (radiusB x)) w := by
  intro f
  obtain ⟨hx,hp⟩ := h.stamp w L hl
  have hq := mul_nonneg (multiplier_pos k h.paper).le h.profit
  refine ⟨hx, le_trans ?_ (betabill _ _ _ J.binds hq (zero_le_one.trans h.letter) w)⟩
  unfold ticket; dsimp only; split
  · exact hp.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (pow_nonneg hq _) J.left)
      (road_pos _ _ (fun _ _=> fares_nn ..) (fun _ _=> fares_nn ..) ..))
  next hu =>
    have hx : jet v f L z=0 := (identical v (he.mono fun y hy => (Aperture.quiet hy w hu : f y=(fun _ : E=>0) y)) _).trans (blank v L z)
    rw [hx,abs_zero,mul_zero]
end Stipend
end sales

namespace Stipend
variable [FiniteDimensional ℝ E] (J : Stipend G S l k a σ M η U C b b' d (radiusB x))
  (h : Knew H (native c) (place S) v z k σ M η ε (fun y=>AFull T A F x (V y) K))
    (hi : 0≤ε) (he : ε≤1) (hM : H.Move (native c) (faceBudget σ M η k) U)
include J h hi he hM

end Stipend
end YM.AnalyticBridge.RelativeLogdet.Physical
