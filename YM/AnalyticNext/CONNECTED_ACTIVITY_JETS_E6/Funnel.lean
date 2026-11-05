import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Caps
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Combo
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Peak
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tax

/-!
# Ratio arms and projections

Even support endpoints protected ON full chart; outside guards we
cap all quadratic factors individually. This allows pointwise rather than
L4 pay on ratio letters. Signed anchors grouping by link blocks remains
mandatory. A inactive identity completion; its payout in the chart integral
needs no degrees for ghost. Real split with Ghost Z expenditure explicitly
subtracted and restored.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

lemma square_heat {β : ℝ} (h : 0<β) : β * (Coat.gStep β)^2=1 := by
  unfold Coat.gStep; rw [inv_pow,Real.sq_sqrt h.le,mul_inv_cancel₀ h.ne']
lemma inverse_heat {β : ℝ} (h : 0<β) : β*Coat.gStep β=(Coat.gStep β)⁻¹ := by
  have hp := square_heat h; let g := Coat.gStep β; have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr h)
  rw [pow_two,← mul_assoc] at hp; exact mul_right_cancel₀ hg.ne' (hp.trans (inv_mul_cancel₀ hg.ne').symm)

namespace Coat
open Pulse Itinerary
variable (X : Coat T F)

/-- Log ratios before exponential. E covariance; inactive extraction is literal `0`. -/
def hatted (β : ℝ) := -((gStep β)⁻¹) • (X.plate *ᵥ X.driftM + X.linearBill)
def qlinear (β : ℝ) (z : Air f G) (i : Bond f) := ∑ j : G.ColorIndex, z (i,j) * X.hatted β (i,j)

/-- use local extension. ψ only for Hot (others never require an a-read). -/
def aperture (β : ℝ) (z : Air f G) (a : ℝ) (i : Bond f) := if X.Hot i then X.cone (2*a) (X.liftA β z) i else 1

def qfirst (β : ℝ) (z : Air f G) (a : ℝ) (i : Bond f) := X.aperture β z a i * X.qlinear β z i

def finale (N : ℕ) (i : ℕ) := if i ≤ N then -X.shreds else X.plate

def circle {n : ℕ} (z : Air f G) (i : Bond f) (p : Itinerary f (n+2)) :=
    let v := arrive i p
    (1/2:ℝ)*(∑ j : G.ColorIndex, z (i,j)*∑ k : G.ColorIndex, combo i p (X.finale n) j k*z (v,k))

def qunique (z : Air f G) (p : Ledger f 2) := X.circle z p.2.1 p.2.2

def chain (β : ℝ) (z : Air f G) (a : ℝ) (p : Ledger f 2) :=
    X.aperture β z a p.2.1 * X.aperture β z a (arrive p.2.1 p.2.2) * X.qunique z p

lemma finale_chain (n : ℕ) : Itinerary.product (n+2) (X.finale n)= (-X.shreds)^(n+1)*X.plate := by
  induction n with
  | zero =>
    change Itinerary.product 2 _=_
    simp only [Itinerary.product,finale,Nat.reduceAdd,le_refl, mul_one, pow_one,not_le.mpr
      (Nat.zero_lt_one), ↓reduceIte]
  | succ n ih =>
    rw [Itinerary.product]
    have hp (i : ℕ) : X.finale (n+1) (i+1)=X.finale n i := by unfold finale; simp
    simp_rw [hp, ih]; rw [finale,if_pos (by omega),pow_succ' _ (n+1), mul_assoc]

lemma circling (i : Bond f) (n : ℕ) (z : Air f G) :
    (∑ p : Itinerary f (n+2), X.qunique z ⟨n,i,p⟩) =
      (1/2:ℝ)*∑ j : G.ColorIndex, z (i,j)*(((-X.shreds)^(n+1)*X.plate) *ᵥ (WithLp.ofLp z)) (i,j) := by
  rw [← X.finale_chain]; unfold qunique circle; dsimp only; rw [← Finset.mul_sum, sum_comm]
  let v := X.finale n
  apply congrArg _; apply sum_congr rfl; intro j hj
  rw [← Finset.mul_sum]; apply congrArg _; unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type]
  have hp b k := Pulse.Itinerary.multiply S i v b j k (n:=n+2)
  change _=∑ b, ∑ k, product (n+2) v (i,j) (b,k)*z (b,k)
  simp_rw [hp, sum_mul]
  simp_rw [sum_comm (t:= (@univ (Itinerary f (n+2)) _))]
  apply sum_congr rfl; intro p _
  rw [Finset.sum_eq_single (arrive i p)]
  · simp [v]
  · intro b _ he; simp [Ne.symm he]
  simp

lemma startk (β : ℝ) (z : Air f G) : (∑ i, X.qlinear β z i) = dotProduct (WithLp.ofLp z) (X.hatted β) :=
    (Fintype.sum_prod_type (fun j : Tubular f G => z j * X.hatted β j)).symm

lemma sleeping {η r Q Y : ℝ} {L : Side} (h : Rotator P L η r Q Y X) :
    X.sleepy *ᵥ stand X.μ=0 := by
  funext i; rw [X.sleepy_act]; split
  · rfl
  next hv => unfold stand; rw [X.μ_sleep h.scale h.room.accepted i.1 hv]; rfl

/-- Before contour extensions. Explicit energy of the ghost gaussian that
can be inserted. This equality holds even on Coat points where the whole
profile will vanish (pure algebra).
-/
def ghost (z : Air f G) := dotProduct (WithLp.ofLp z) (X.sleepy *ᵥ WithLp.ofLp z)/2

lemma correcting {β : ℝ} (hp : 0<β) {η r Q Y : ℝ} {L : Side} (h : Rotator P L η r Q Y X)
    (z : Air f G) :
    -β*X.liftSq (X.liftA β z)-X.ghost z= -β*X.liftSq X.μ + dotProduct z.ofLp (X.hatted β) +
      dotProduct z.ofLp ((X.relating⁻¹-X.plate) *ᵥ z.ofLp)/2 - dotProduct z.ofLp (X.relating⁻¹ *ᵥ z.ofLp)/2 := by
  obtain ⟨_,_,H,-⟩ := h.room.accepted.feeds; unfold liftA
  let g := gStep β; let w := WithLp.ofLp z; let b := X.linearBill + (X.form.transpose*X.form) *ᵥ stand X.μ
  have hp' : X.hatted β = - (β*g) • b := by
    rw [inverse_heat hp,hatted,show X.driftM=stand X.μ from rfl,plate,Matrix.add_mulVec,X.sleeping h, add_zero,add_comm]
  have ht := X.balance H X.μ (g • X.atmos z)
  have hk : stand (g • X.atmos z)=g • w := rfl
  rw [hk, Matrix.mulVec_smul, smul_dotProduct,smul_dotProduct,dotProduct_smul] at ht
  have hv := square_heat hp
  unfold ghost; rw [hp',plate]
  simp only [Matrix.sub_mulVec,Matrix.add_mulVec, dotProduct_add, dotProduct_sub,dotProduct_smul,smul_eq_mul] at *
  unfold g w b at *
  let K := dotProduct z.ofLp ((X.form.transpose * X.form) *ᵥ z.ofLp)
  have he : β*gStep β^2*K=K := by rw [hv,one_mul]
  unfold K at he; rw [dotProduct_add]; nlinarith only [ht, hv, he, congr_arg (β * ·) ht]
end Coat
end YM.ConnectedActivityE6
