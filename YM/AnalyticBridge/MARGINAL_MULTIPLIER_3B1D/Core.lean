import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Matrices
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger

/-!
Index sets and predicates external, color/counting conventions internal. Later
`Sector.lean` binds the data to the literal sector formula with the *remainder*
retained (not block factorization of det, inverse, Gaussian, or gas). May also
use smooth extensions for pre-mask derivatives, with equality checks.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Lattice RG Wilson Next.SectorChange Pressure Push.SectorMeasure Precision
  FiniteMatrix Matrix
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

structure Location (f : Side) (I J : Type) where
  address : I ⊕ J ↪ Bond f

structure Kernel (G : Gauge) (c : Side) (I J ρ : Type) where
  cov : Config G c → Gaussian.Table (I × G.ColorIndex)
  gram : Config G c → Gaussian.Table (I × G.ColorIndex)
  flat : Gaussian.Table ((I ⊕ J) × G.ColorIndex)
  mean : Config G c → LogArray G I
  draw : Config G c → Prices G I
  signal : Config G c → Prices G I
  offset : Config G c → Gaussian.Vec ρ
  holds : LinkArray G J

namespace Kernel
variable {G : Gauge} {c f : Side} {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ]
    (h : Kernel G c I J ρ)

/-- Fsct marginal version. Includes the frozen link deficit and Aflat
normalization, even if this C is a window approximation. -/
def ledger (s : ℝ) (V : Config G c) := -(Fintype.card J:ℝ)*Real.log s +
  2⁻¹ * (Real.log (h.cov V).det + Real.log h.flat.det)
/-- Offset stores the normalized (divided by actual g) mean residual at each
selected scalar row of the physical `Rows.direct`. Signal is eta, no 1/2. -/
def correction (V : Config G c) := -2⁻¹*(h.offset V ⬝ᵥ h.offset V) + h.signal V ⬝ᵥ h.draw V +
  2⁻¹ * (h.draw V ⬝ᵥ (((h.cov V)⁻¹-h.gram V)*ᵥ h.draw V))

def stage (g : ℝ) (V : Config G c) : LogArray G I := h.mean V+g • tape (h.draw V)

def atLinks (S : StepData c f) (P : Location f I J) (g : ℝ) (V : Config G c) : Config G f := fun e =>
  if he : ∃ i, P.address (.inl i)=e then G.lieExp (h.stage g V he.choose)*replica S.ratio V e
  else if hy : ∃ j, P.address (.inr j)=e then h.holds hy.choose else 1
lemma west_link (S : StepData c f) (P : Location f I J) (g : ℝ) (V : Config G c) (i : I) :
    h.atLinks S P g V (P.address (.inl i)) = G.lieExp (h.stage g V i)*replica S.ratio V (P.address (.inl i)) := by
  have he : ∃ j, P.address (.inl j) = P.address (.inl i) := ⟨i,rfl⟩
  rw [atLinks,dif_pos he,(Sum.inl.inj (P.address.injective he.choose_spec))]
lemma east_link (S : StepData c f) (P : Location f I J) (g : ℝ) (V : Config G c) (j : J) :
    h.atLinks S P g V (P.address (.inr j)) = h.holds j := by
  have he : ∃ i, P.address (.inr i) = P.address (.inr j) := ⟨j,rfl⟩
  have ht : ¬∃ i, P.address (.inl i) = P.address (.inr j) := fun ⟨i,hi⟩ => by cases P.address.injective hi
  rw [atLinks,dif_neg ht,dif_pos he,(Sum.inr.inj (P.address.injective he.choose_spec))]
lemma empty_link (S : StepData c f) (P : Location f I J) (g : ℝ) (V : Config G c) (i : Bond f) (hi : i ∉ Set.range P.address) :
    h.atLinks S P g V i = 1 := by
  rw [atLinks, dif_neg (fun ⟨j,hj⟩ => hi ⟨.inl j,hj⟩), dif_neg (fun ⟨j,hj⟩ => hi ⟨.inr j,hj⟩)]

def chartLog (q : Chi) (Z : ChartRatio G) (d g : ℝ) (V : Config G c) := ∑ i, logGuard q Z d (h.stage g V i)

def light (S : StepData c f) (P : Location f I J) (R : Rep G f) (i : ℕ) (V : Config G c) := R.activities.E i (h.atLinks S P (coupling R.beta) V)
def heavy (S : StepData c f) (P : Location f I J) (R : Rep G f) (i : ℕ) (V : Config G c) := R.activities.K i (h.atLinks S P (coupling R.beta) V)

/-- For an exact occurrence choose the list `lights` with *true* mask checks
at U. For jets this is unmasked on this recorded list. Other rows of drows,
canonical atoms and tails not called part of the Gaussian submultiplier here.
-/
def expense (S : StepData c f) (P : Location f I J) (R : Rep G f) (q : Chi) (Z : ChartRatio G) (d : ℝ)
    (lights : Finset ℕ) (V : Config G c) :=
  h.ledger (spare Z R.beta) V + h.correction V + h.chartLog q Z d (coupling R.beta) V -
    ∑ i ∈ lights, h.light S P R i V

def multiplier (S : StepData c f) (P : Location f I J) (R : Rep G f) (q : Chi) (Z : ChartRatio G) (d : ℝ)
    (lights heavies : Finset ℕ) (V : Config G c) :=
  doors q d (h.stage (coupling R.beta) V) * (∏ j∈heavies, h.heavy S P R j V) * Real.exp (h.expense S P R q Z d lights V)

variable (h' : Kernel G c I J ρ)
structure Ground (V : Config G c) (H : ℝ) : Prop where
  covariance : (h.cov V).PosDef
  precision : (h.gram V).PosDef
  kinetic : h.flat.PosDef
  budget : 0 ≤ H
  eastCost : Upper (h.cov V)⁻¹ H
  mass : Upper h.flat⁻¹ H

structure Matrices (k : ℕ) (D : Directions G c → Prop) (V : Config G c) (a b : ℝ) : Prop where
  abs_nn : 0≤a
  pert_nn : 0≤b
  covariance : Entries k D V h.cov h'.cov a b
  precision : Entries k D V h.gram h'.gram a b
  kinetic : Entries k D V (fun _ => h.flat) (fun _ => h'.flat) a b
  offset (i : ρ) : Compare k D V (h.offset · i) (h'.offset · i) a b 1
  draw (i) : Compare k D V (h.draw · i) (h'.draw · i) a b 1
  signal (i) : Compare k D V (h.signal · i) (h'.signal · i) a b 1
variable (I J ρ G)
private abbrev live := Fintype.card (I × G.ColorIndex)
private abbrev free := Fintype.card ((I ⊕ J) × G.ColorIndex)

def ledgerCost (k : ℕ) (a H s : ℝ) := |-(Fintype.card J : ℝ)*Real.log s| +
  2⁻¹ * (logCost (live G I) a H k + logCost (free G I J) a H k)
def ledgerReaction (k : ℕ) (a H : ℝ) := 2⁻¹ * (logReaction (live G I) a H k + logReaction (free G I J) a H k)

def correctionCost (k : ℕ) (a H : ℝ) := let N := (live G I:ℝ)
  2⁻¹*(Fintype.card ρ*(a*a)*2^k) + N*(a*a)*2^k +
    2⁻¹ * (N*(N*(a*((stock (live G I) a H k+a)*a)))*3^k)
def correctionReaction (k : ℕ) (a H : ℝ) := let N := (live G I:ℝ)
  2⁻¹*(Fintype.card ρ*(2*a)*2^k) + N*(2*a)*2^k +
    2⁻¹ * (N*(N*(2*a*(stock (live G I) a H k+a)+a^2*(reaction (live G I) a H k+1)))*3^k)

variable {I J ρ G h h'} {k : ℕ} {D : Directions G c → Prop} {V : Config G c} {a b H : ℝ}
lemma ledger_estimate (e : Matrices h h' k D V a b) (hW : Ground h V H) (hE : Ground h' V H) (s : ℝ) :
    Compare k D V (h.ledger s) (h'.ledger s) (ledgerCost G I J k a H s) (ledgerReaction G I J k a H * b) 1 := by
  have hf := log_jets e.covariance e.abs_nn e.pert_nn hW.budget hW.covariance hE.covariance hW.eastCost hE.eastCost
  have ht := log_jets e.kinetic e.abs_nn e.pert_nn hW.budget hW.kinetic hE.kinetic hW.mass hE.mass
  let x := -(Fintype.card J:ℝ)*Real.log s
  have H := (Compare.same (Bound.const x (Real.norm_eq_abs _).le zero_le_one)).add ((hf.add ht).scale (2:ℝ)⁻¹)
  refine H.weaker (by norm_num [ledgerCost,x]) ?_ le_rfl
  unfold ledgerReaction; rw [mul_assoc _ _ b,add_mul]; norm_num [live, free]

lemma correction_estimate (e : Matrices h h' k D V a b) (hW : Ground h V H) (hE : Ground h' V H) :
    Compare k D V h.correction h'.correction (correctionCost G I ρ k a H) (correctionReaction G I ρ k a H * b) 1 := by
  have hf := inverse_jets e.covariance e.abs_nn e.pert_nn hW.budget hW.covariance.isUnit hE.covariance.isUnit hW.eastCost hE.eastCost
  have H1 := ((Compare.univ (fun i => (e.offset i).mul (e.offset i)) (by norm_num)).flatten (by norm_num)).scale (-2⁻¹)
  have H2 := (Compare.univ (fun i => (e.signal i).mul (e.draw i)) (by norm_num)).flatten (by norm_num)
  have H3 := ((Compare.univ (fun i => Compare.univ (fun j => (e.draw i).mul (((hf i j).sub (e.precision i j)).mul (e.draw j))) (by norm_num)) (by norm_num)).flatten (by norm_num)).scale 2⁻¹
  have he (h : Kernel G c I J ρ) V : h.draw V ⬝ᵥ (((h.cov V)⁻¹ - h.gram V)*ᵥ h.draw V) = ∑ i,∑ j,h.draw V i*((((h.cov V)⁻¹ i j)- h.gram V i j) * h.draw V j) := by
    unfold dotProduct mulVec; simp only [Matrix.sub_apply,dotProduct,Finset.mul_sum]
  unfold correction; simp_rw [he]
  refine ((H1.add H2).add H3).weaker ?_ ?_ le_rfl
  · exact le_of_eq (by norm_num [correctionCost,live])
  exact le_of_eq (by norm_num [correctionReaction,live]; ring)

/-- The quadratic growth of this particular marginal correction is paired
with the *same* marginal force. After paying signal²/gap it leaves a Gaussian
reserve; no volume of the ambient torus is charged here. -/
lemma correction_upper {η : ℝ} (hp : 0 < η) (he : Schur.Gapped (h.gram V) η) : h.correction V - Gaussian.force (h.cov V) (h.draw V)/2 ≤
    Schur.sumSq (h.signal V)/η - η/4*Schur.sumSq (h.draw V) := by
  let z := h.draw V; let v := h.signal V
  have hv : v ⬝ᵥ z ≤ Schur.sumSq v/η + η/4*Schur.sumSq z := by
    unfold dotProduct Schur.sumSq; rw [Finset.sum_div,Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hx := sq_nonneg (v i- (η/2)*z i)
    field_simp; nlinarith
  unfold correction Gaussian.force
  rw [Matrix.sub_mulVec,dotProduct_sub,← Schur.sumSq_dot]
  dsimp only [v,z] at hv; linarith only [he (h.draw V),hv,Schur.sumSq_nn (h.offset V)]
end Kernel
end YM.AnalyticBridge.MarginalMultiplier3b1d
