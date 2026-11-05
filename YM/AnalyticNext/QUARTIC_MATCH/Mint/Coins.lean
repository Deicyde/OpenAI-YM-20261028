import YM.AnalyticNext.QUARTIC_MATCH.Local.Rest
import YM.AnalyticNext.QUARTIC_MATCH.Mint.Layout

/-!
# Separated order-3 / order-4 pieces, for any Answer

Main classical is nonlinear. Keep exact atoms and true-length costs; user
may select any `Printed` family before the quote. Per operation these general
calls use `Led` with ORIGINAL widths of every path. Even `Funded` alone doesn't
assert e.g. that an abridged/prescribed row scheme was used; discharge Led on
`scripts` later. Post-L only variants using the current Funding at its actual
smaller/incomplete price also follow.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Mint
open Filter Function Lattice Laurent Matrix RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Next Tree Joint BoxChain Mail Analyzers
open Local Local.Rotate Local.Budget Hessian Local.Wages Tensor
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable (G : Gauge) (j : ℕ) (K : MapPrices) (L : KernelChoices)
variable (θ D D' : ℝ) (he : 0<θ) (hw : boom θ ≤ K.α j)
include he hw



/-- Requires EXACT three on THAT lower unmasked model; not just the third homogeneous polynomial
of its affine-linear pieces. Then charges the quartic operation. -/
theorem quartic (P : Printed 3) (B : ℝ) (hb : 0≤B) (ht : θ ≤ Tracks.purchase j (K.η j) (K.α j) (K.Ω j) L.penalty) :
    ∃ s C : ℝ,0<s ∧ 0≤C ∧ ∀ (a : Levels G), a.clock.kernel=L → ∀ {m N}, a.clock.J (m+1)=j →
      ∀ H : Horizon a,H.Suffices K → Progress.Joint.Swears H → AdmitsMesh a m → m<N →
        ∀ R W : PathData G, Funded H N (m+1) W → Funded H N m R → (∀ i,(R.quartic i).coeff=0) →
      ∀ {t v σ C3 C4 : ℝ}, Led W (a.S.block m) 4 (boom θ) v D C3 C4 →
        Led R 1 4 (boom θ) σ D' (B*assistance (a.S.block m) C3 0) 0 →
        ∀ Y : Answer H N m W t, UpTo Y 3 R → ∃ A : rootArray G 3,
          Ink (letters P A) s (C*(assistance (a.S.block m) C3 C4+assistance (a.S.block m) C3 0^2)) ∧
          UpTo Y 4 (fourth R (letters P A)) := by
  obtain ⟨δ,C,hδ,hC,H⟩ := charge_four G j D D' θ L.penalty (K.α j) (K.Ω j) (K.η j) he hw L.penalty_pos (K.eta_pos _) P B hb ht
  refine ⟨δ,C,hδ,hC,?_⟩
  intro a hj m N hk S hs hh hp ha R W hW hR hy t v σ C3 C4 h₁ h₂ Y hh'
  subst L j
  obtain ⟨_,⟨Z⟩⟩ := purchased hW hs hh ha
  obtain ⟨A,hA,h⟩ := H Z rfl rfl hW.bound hR.bound h₁ h₂ hW.ties (hs.all N (m+1) ha) (fun c => hh _ _ _ ha)
    (hs.rows _ _ ha).2.1 hy (S.towers N m).A0 (fun c _ => visit hs ha c) (a.S.side m) (threshold_paid hp) (tends a m)
    (fun _ k hk => upward Y hW hp hh' k hk)
  exact ⟨A,hA,descend Y hW hp h⟩
end YM.AnalyticNext.QuarticMatch.Mint
