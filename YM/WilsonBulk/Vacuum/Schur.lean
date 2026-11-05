import YM.WilsonBulk.Vacuum.Quadratic

/-!
# Cancellation and cutoff comparison of the leading flat primitive

Derive the overlap cutoff rate by the **Schur identity on the difference of precisions**.
We don't need separate rates for the pole split and moving stage filters. Crossing two
histories' A₀ columns gives the EXACT pull interrelation (the rest cancels, including at
zero momentum and on every physical period). `normalized` killed degree 0..2 Taylor terms of
these differences in actual `Width`. Thus putting Newton cost of the columns into the pull
with any fixed widths meeting the *before L* conditions gives uniform exponentially weighted
contraction over arbitrary depths.

This concerns the flat POTENTIAL kernel, not two-form metric rows in noncurl directions,
and no comparison with `Rep.eval`. Importantly avoid asserting such precision for fitted
actual beta or the source/density paths. Strict operations later in formal perturbation can
use the cutoff-independent horizontal identities and the quantitative cutoff results for the
*tree* covariance, for which precisely this convergence of the precision can be used. Actual
curvature and nonlinear lifts need separate bounds (and transforming between covers/windows).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open Push.AbsoluteSums RG Finset Work.F08 Precision Exterior Craft
open scoped Topology BigOperators Classical
open Matrix
variable {G : Gauge} {a : Levels G} {c f : Side}
variable (S : StepData c f)

lemma schur_identity (A B : Matrix (Body 1 f) (Body 1 c) ℝ) {P Q : Matrix (Body 2 f) (Body 2 f) ℝ}
    {W V : Matrix (Body 2 c) (Body 2 c) ℝ} (h : Precision.Inputs S A P W)
    (g : Precision.Inputs S B Q V) (hs : P.transpose=P) (hq : W.transpose=W) :
    K W - K V = A.transpose * ((K P - K Q)*B) := by
  have h₁ : A.transpose * K P = K W * mean S := by
    simpa only [Matrix.transpose_mul,ksym hs, ksym hq, Matrix.transpose_transpose] using
      congrArg Matrix.transpose h.primal
  have h₂ : A.transpose * (mean S).transpose = 1 - S.kernel.penalty⁻¹ • K W := by
    rw [← Matrix.transpose_mul, h.dual,transpose_sub, Matrix.transpose_one, transpose_smul, ksym hq]
  rw [Matrix.sub_mul, g.primal, Matrix.mul_sub, ← Matrix.mul_assoc,h₁,
    Matrix.mul_assoc, g.dual, ← Matrix.mul_assoc A.transpose, h₂, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  simp [sub_sub_sub_cancel_right]

variable {H P : Horizon a} {N N' m : ℕ} {F F' : MapPrices}

lemma periods_up (S : Schedule) (m : ℕ) : Tendsto (fun p => (S.side m p).val) atTop atTop := by
  apply tendsto_atTop_mono _ S.period_strict.tendsto_atTop
  intro n; rw [Schedule.side, PNat.mul_coe]; exact Nat.le_mul_of_pos_right _ (S.denominator _).pos

lemma many_acts {α β : Type} {A B : Row α β} (hA : A.safe) (hB : B.safe)
    {n : ℕ → Side} (h : Tendsto (fun p => (n p).val) atTop atTop) (he : ∀ᶠ p in atTop, A.acts (n p)= B.acts (n p)) :
    A=B := by
  funext x y z
  exact tendsto_nhds_unique ((Next.Free.entry_limit n h A hA x y z).congr' (he.mono fun p hp => by rw [hp]))
    (Next.Free.entry_limit n h B hB x y z)

-- explicitly keep contraction constant here so no post-size `σ` can be charged
-- as if free. Flat-power Λ bookkeeping moves separately.
def kineticBill (T U : ℝ) (θ σ : ℝ) :=
  ((Fintype.card PotentialForm:ℝ) * Fintype.card PotentialForm) * T * outlay θ σ 3 * U
abbrev L (a : Levels G) (m : ℕ) : ℝ := (a.S.block m).val
abbrev stage (a : Levels G) := a.clock.J

lemma canon_a0 (h : H.Suffices F) (hm : m<N) :
    (H.towers N m).A0.strip (F.α (stage a (m+1))) (F.Ω (stage a (m+1)) / L a m) := by
  simpa using! (((h.costs N m hm).2.2.2 [] (Nat.zero_le _)).1)

lemma energy_diff (h : H.Suffices F) (hP : P.Suffices F') (hm : m<N) (hm' : m<N') :
    minusRows (flat H N m) (flat P N' m) = twoPull (H.towers N m).A0
      (minusRows (flat H N (m+1)) (flat P N' (m+1))) (P.towers N' m).A0 := by
  let x := flat H N m; let y:= flat P N' m; let u:= flat H N (m+1); let v:=flat P N' (m+1)
  let A:= (H.towers N m).A0; let B:= (P.towers N' m).A0
  have hx := strip_mono (canonical_strip h hm.le) (F.alpha_pos _).le le_rfl
  have hy := strip_mono (canonical_strip hP hm'.le) (F'.alpha_pos _).le le_rfl
  have hu := strip_mono (canonical_strip h (show m+1≤N from hm)) (F.alpha_pos _).le le_rfl
  have hv := strip_mono (canonical_strip hP (show m+1≤N' from hm')) (F'.alpha_pos _).le le_rfl
  have hA := strip_mono (canon_a0 h hm) (F.alpha_pos _).le le_rfl
  have hB := strip_mono (canon_a0 hP hm') (F'.alpha_pos _).le le_rfl
  refine many_acts (Row.rights _ _ (strip_minus hx hy) le_rfl) (Row.rights _ _
    (strip_compose (le_refl 0) (strip_trans hA) (strip_fine (le_refl 0) (strip_minus hu hv) hB)) le_rfl) (periods_up a.S m) ?_
  filter_upwards with p
  let s : StepData (a.S.side m p) (a.S.side (m+1) p):= a.clock.op m p
  change (minusRows x y).acts _ = (twoPull A _ B).acts (a.S.side m p)
  unfold x y A B; rw [acts_minus (le_refl 0) hx hy]; erw [
    twoPull_acts (X:=s.ratio) (le_refl 0) (strip_minus hu hv) hA hB,
    acts_minus (le_refl 0) hu hv]
  rw [canonical_period h hm.le, canonical_period hP hm'.le, canonical_period h hm,
    canonical_period hP hm']
  exact schur_identity _ _ _ (h.crossings _ _ _ hm).trial (hP.crossings _ _ _ hm').trial
    (h.all _ _ hm _).symmetric.1 (h.all _ _ hm.le _).symmetric.1

lemma energy_step {θ σ B : ℝ} (hθ : 0< θ) (hσ : 0≤ σ)
    (h : H.Suffices F) (hP : P.Suffices F') (hm : m<N) (hm' : m<N')
    (hJ : 5 ≤ stage a (m+1)) (ha : σ≤ F.α (stage a (m+1)))
    (ha' : σ≤ F'.α (stage a (m+1))) (hc : σ / L a m ≤ θ/2)
    (hK : (minusRows (flat H N (m+1)) (flat P N' (m+1))).strip θ B) :
    (minusRows (flat H N m) (flat P N' m)).strip σ
      (kineticBill (F.Ω (stage a (m+1))) (F'.Ω (stage a (m+1))) θ σ * B / L a m) := by
  let j:= stage a (m+1); let T:=F.Ω j; let U:=F'.Ω j; let z:= L a m
  have hU: 0≤ U := Pert.Bulk.merit (hP.rows N' (m+1) hm')
  have he : ∀ l: List Axis, l.length = 3 → (advanceC (a.S.block m) (P.towers N' m).A0 l).strip σ (U / z^4) := by
    intro l hl
    have ht := ((hP.costs _ _ hm').2.2.2 l (hl.symm ▸ (show 3 ≤ j-2 from by unfold j; omega))).1
    simp_rw [hl] at ht; exact strip_mono ht ha' le_rfl
  rw [energy_diff h hP hm hm']
  convert twoPull_bound hθ hσ (strip_mono (canon_a0 h hm) ha le_rfl) hK (blind_flat_diff h hP hm hm')
    (canon_a0 hP hm') (F'.alpha_pos _).le (div_nonneg hU (by positivity : 0≤z^4)) he hc (a.S.block_odd m) using 1
  dsimp only [kineticBill,L,z,U,j]; field_simp

end YM.WilsonBulk
