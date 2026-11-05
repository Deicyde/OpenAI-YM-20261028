import YM.AnalyticNext.QUARTIC_MATCH.Costed
import YM.AnalyticNext.QUARTIC_MATCH.Local.Centerline
import YM.AnalyticNext.QUARTIC_MATCH.Local.Limits
import YM.AnalyticNext.QUARTIC_MATCH.Mint.Layout

/-!
# Scripting at heights forecast

Expose the two prices after charging. `AdmitsMesh` used when actually supplying.
Quantification over any K at which booking likely feasible. J × J
includes transitions and all corners (observation is only needed for Adj).
Do not average nonlinear paths on the side involutions before planning.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Mint
open Filter Function Lattice Laurent Matrix RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Next Tree Joint BoxChain Mail Analyzers
open Progress.Joint Local Local.Budget Local.Rotate Local.Wages Hessian Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
namespace Affairs
variable {G : Gauge}
def Shortens (P : PathData G) (K : MapPrices) (i : ℕ) := Rotate.Curves P (min (K.α i) 1) (rowBill K i)


variable (G : Gauge) (K : MapPrices) (L : KernelChoices) (j i : ℕ)

def Upcoming (P : Printed 2) (s B D : ℝ) := ∀ (a : Levels G), a.clock.kernel=L → ∀ {m N : ℕ}, a.clock.J (m+1)=j → a.clock.J m=i →
    ∀ H : Horizon a,H.Suffices K → Progress.Joint.Swears H → AdmitsMesh a m → m<N →
    ∀ R W : PathData G, Funded H N (m+1) W → Funded H N m R → (∀ x,(R.cubic x).coeff=0) → (∀ x,(R.quartic x).coeff=0) →
    Shortens W K j → Shortens R K i → B ≤ (a.params (m+1)).width*(a.S.block m).val →
      ∀ (t : ℝ) (Y : Answer H N m W t),
        ∃ A : rootArray G 2, Ink (letters P A) s (D*assistance (a.S.block m) (a.params (m+1)).paths 0) ∧
          UpTo Y 3 (third R (letters P A))

def NextUp (P : Printed 3) (δ B s C D : ℝ) := ∀ (a : Levels G), a.clock.kernel=L → ∀ {m N : ℕ}, a.clock.J (m+1)=j → a.clock.J m=i →
    ∀ H : Horizon a,H.Suffices K → Swears H → AdmitsMesh a m → m<N →
    ∀ R W : PathData G, Funded H N (m+1) W → Funded H N m R → (∀ x,(R.quartic x).coeff=0) →
    Shortens W K j → Shortens R K i →
      B ≤ (a.params (m+1)).width*(a.S.block m).val →
      let x := a.params (m+1); let b := a.S.block m;
      Ink R.cubic s (C*assistance b x.paths 0) → ∀ (t : ℝ) (Y : Answer H N m W t), UpTo Y 3 R →
          ∃ A : rootArray G 3, Ink (letters P A) δ (D*(assistance b x.paths x.paths+assistance b x.paths 0^2)) ∧
            UpTo Y 4 (fourth R (letters P A))

omit G L in
lemma narrows (β : ℝ) (he : 0 < β) : ∃ u : ℝ, 0<u ∧ boom u ≤ K.α j ∧
    20*boom u ≤ min (K.α j) 1 ∧ 20*boom u ≤ min (K.α i) 1 ∧ 20*boom u ≤ β := by
  let b := min β (min (min (K.α j) 1) (min (K.α i) 1));
  have hb : 0<b := lt_min he (lt_min (lt_min (K.alpha_pos _) one_pos) (lt_min (K.alpha_pos _) one_pos))
  let u := b/80; have hp : 0<u := by unfold u; positivity
  have heq : 20*boom u=b := by unfold boom u; ring
  refine ⟨u,hp,?_,heq ▸ (min_le_right .. |>.trans (min_le_left ..)),heq ▸ (min_le_right .. |>.trans (min_le_right ..)),heq ▸ (min_le_left ..)⟩
  have hh : b ≤ K.α j := (min_le_right ..).trans ((min_le_left ..).trans (min_le_left ..)); linarith






end Affairs
end YM.AnalyticNext.QuarticMatch.Mint
