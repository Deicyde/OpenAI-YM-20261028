import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.Progress.DIRECTED_RECIPE.Recipe
import YM.Push.BETA_TRANSPORT.History
import YM.Push.STRESS_FLUX.Haar
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Handoff
import YM.UVNext.COUPLING_RESET.Regular


/-!
Physical open inputs at the *intact* Gaussian sector operation.

Never ask for activities satisfying a post-reset Hessian constraint, or
for two separate scalar estimates with omitted multipliers.

The coupled
numerator assembly AND local payments (incl fixed lists) are required on
one and the same EARLY presentation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Return
open Function Filter Set Lattice Wilson RG RG.Shoot RG.Supply Pressure MeasureTheory Next.SectorChange Next.Fluctuations.Sector Push.SectorMeasure
open Precision UVNext.CouplingReset Collection Input Tree
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)

abbrev Wages := ℕ → ℕ → ℝ
def effort (g : Wages) (m : ℕ) := g (B.a.clock.J (m+1)) (B.a.clock.J m)
def radius (g : Wages) (m : ℕ) := effort B g m * B.a.clock.threshold (m+1)
abbrev Bookings (m p : ℕ) (g : Wages) := Allocation G (B.a.clock.op m p) (B.a.clock.hatBeta m) (effort B g m)
abbrev Wood (m p : ℕ) := Forest (B.a.clock.op m p).ratio
abbrev Higher (m p : ℕ) := Rep G (B.a.S.side (m+1) p)
abbrev Work (m p : ℕ) := Config G (B.a.S.side m p)
variable (N : ℕ) {m p : ℕ} (T : Wood B m p) {g : Wages} (d : Bookings B m p g) (χ : Chi) (r : Wages)

/-- Includes the true active chart determinant, sieve, β and Haar products,
with the specific fog and stationary displacements and no implicit positive
logarithm assumption. -/
def gaussian (Q : Higher B m p) (V : Work B m p) :=
  let S := B.a.clock.op m p
  let U := Testing.ships B N m p
  let x := B.a.clock.hatBeta m
  ∑ A : Stores S, Presented.sieve U Q.beta x V * ∑ k,
    let C := fog A T U x V k
    let l := meanLog A T U x V k χ (radius B r m)
    prefactor S G Q.beta * Z.scale ^ Fintype.card (Active A x T) * chartCost C (coupling Q.beta) *
      ∫ y, (∫ z, dyed U x V k A Q (shots S x) T d χ Z (radius B r m) C l y z ∂Gaussian.cloud C) ∂piHaar G (Frozen A x T)

def licensed (Q : Higher B m p) :=
  let S := B.a.clock.op m p; let U := Testing.ships B N m p; let x := B.a.clock.hatBeta m
  ∀ V : Work B m p, ∀ (A : Stores S) (k : S.Choices), let C := fog A T U x V k
    Licenses U x V k A Q (shots S x) T d χ Z (radius B r m) C (meanLog A T U x V k χ (radius B r m)) ∧
      (A.flags = flags (temp x) V → C.PosDef)

lemma earnings {E : Wages} (hW : Testing.Ringing K g W) (bill : Cosmos Z K W g r E) (hm : m<N)
    (Q : Higher B m p) (hQ : Lives B.bake N (m+1) p Q) (hb : Q.beta∈band B.a (m+1)) :
    0 < radius B r m ∧ licensed B N T d χ r Q ∧ (B.a.clock.op m p).push Q.beta Q.eval = gaussian B N T d χ r Q := by
  obtain ⟨_,hr,_,_,_,_,_,ν,_,hv⟩ := committed B hW bill N m p hm Q hQ hb
  obtain ⟨_,h,he⟩ := hv d T χ
  exact ⟨hr,fun V A k => ⟨(h A k V).2.2, fun hh => ((h A k V).2.1 hh).1⟩,funext he⟩

/-- Exact coupled answer before kinetic/affine reorganization. Which field
shapes and support relations really admit such an atlas at the bought costs
is *not* proved. (The equality without Bounds alone has no such content.)
α term uses quadratic row-pair supports including kept-test halo. Book/terms
fixed throughout, including during parameter comparisons; mask queries on
both sides take real V, at equality too. No approximation of the pushed law
in place of this input for any step of the history. -/
def atlas (Q : Higher B m p) (X : Listing G (B.a.S.side m p)) (v : Collection.Source G (B.a.S.side m p)) (τ : ℝ) :=
    gaussian B N T d χ r Q = earlyValue X (B.kin.path N m) (B.a.params m).clip (B.a.budget m) v Q.beta τ (B.kin.alpha N m)
variable {l : Set ℝ} {Q : In B.a m p} {X : Listing G (B.a.S.side m p)} {v : ℝ → Collection.Source G (B.a.S.side m p)} {τ H w : ℝ → ℝ}
    {q : ResetPrices}
lemma grants {E} (hW : Testing.Ringing K g W) (bill : Cosmos Z K W g r E) (hm : m<N)
    (hb : ∀ x∈l,Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta∈band B.a (m+1))
    (ha : ∀ x∈l,atlas B N T d χ r (Q x) X (v x) (τ x)) (hs : ∀ x∈l, Local X (B.a.budget m) (v x) (H x) (w x))
    (he : ∀ x∈l, H x ≤ funds B.a m q / 4) :
    (∀ x∈l, target Q x = earlyValue X (B.kin.path N m) (B.a.params m).clip (B.a.budget m) (v x) (Q x).beta (τ x) (B.kin.alpha N m)) ∧
    Prereset B q l N m p Q τ (fun x => X.read (v x)) := by
  have h (x : ℝ) (hx : x ∈ l) := ((earnings B N T d χ r hW bill hm (Q x) (hb x hx).1 (hb x hx).2).2.2).trans (ha x hx)
  refine ⟨h,fun x hx => ?_, fun x hx V hV => ?_⟩
  · obtain ⟨u,hu,hk⟩ := (hs x hx).unweighted; exact ⟨u,hu,fun o => Push.AbsoluteSums.budget_loosen (hk o) (he x hx)⟩
  change _ = Real.exp _
  let R := B.kin.path N m; let c := (B.a.params m).clip
  have hu := unmasked_precision R c hV
  have hr := B.support.cap N m hm.le
  have ht : receipt R c (B.a.budget m) V = secondTerm c R V := allGoodPrice hr V hV
  change (B.a.clock.op m p).push (Q x).beta (Q x).eval V = _
  rw [h x hx,earlyValue,Rep.eval]
  change Real.exp _ * (X.read (v x)).gas (B.a.budget m) V * _ = _
  rw [Activities.gas_one _ _ hV, mul_one,← Real.exp_add]
  congr 1
  change (τ x * sites _ - R.inChannels c (B.a.budget m) (Q x).beta V - _) + -_ * receipt R c _ V = _
  rw [Push.BetaTransport.channels_split V (Q x).beta, hu.1,hu.2.1,ht]; dsimp only [frozen,R,c]; ring
end YM.AnalyticBridge.VerifiedReset.Return
