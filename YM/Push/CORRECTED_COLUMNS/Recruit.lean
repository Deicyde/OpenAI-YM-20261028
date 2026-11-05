import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Bel
import YM.Push.CORRECTED_COLUMNS.Funding



/-!
# Possible route to Seed, conditional (downstream demo)

This version fixes *one* candidate real basis and set of probes and
gets `π.Ready` for them. No hypothesis even quantifying over every
RankWidths/Columns user. See `common` for flexible consumption with
own X, W, different γ per family etc.

Only assumptions on the actual regulator and free comparator: e.g.
keep one α positive-stage budget through every weight d (so also
monitor^(η-γ) price).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Recruit
open MeasureTheory Lattice RG RG.Supply Filter Function Extraction Next.Extract Cells Dash
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {P : Sheet G} {w : Rolls P} {T : Protection w} {U : Delays T} {W : Bar U} {L : Wait W} {f : Extraction.Order}
variable (h : G.Simple) (S : Table C.book) {a : Axis} (H : (standard C).RealSpin) (hw : Bel.oneRP (standard C) a)

def basis (d : ℕ) : Columns C S d := (Bel.columnsOf C S d H hw).choose
-- geometry is not an existence hypothesis about labels


/-- The remaining RESEARCH GATE on this basis. Choose Series at
prescribed b, get tuning coefficients (see also `Issue.charge`,
`Issue.selects` – not to *retune* after the estimate). Then necessary
l-uncorrected data and estimates (Meeting) and W propagation (`Courtesy`)
on this path. `Makes` doesn't assume root bounds, projection comparison,
limit labels, or Valid in any form. -/
structure Makes (d : ℕ) (f : Extraction.Order) (α : ℕ → ℝ) (γ b : ℝ) : Prop where
    activate : ∃ Y : Tests (basis S H hw d), Y.B.b=b ∧
      (∀ k, ∃ D : ℝ, 0 ≤ D ∧ ∀ p : ℕ, ∀ᶠ i in atTop, ∀ j,
        ‖Y.tune k (f.mesh i) p j‖ ≤ D) ∧
      ∀ k, f.late fun N p => ∃ B : Wire C (Y.B.side k) (Y.B.depth k) N p,
        Flow.Crew Y k N p B (α ((lvl C).clock.J (Y.B.side k))) ((lvl C).clock.monitor (Y.B.depth k)^γ)

variable {α : ℕ → ℝ} {γ η : ℝ} {b : ℕ→ℝ} (hn : Paid L (lvl C))
  (hx : 0 < η) (hg : η < γ) (h' : Last.OnPage U η 2 α) (hA : ∀ j, 0≤α j)
  (hs : ∀ d, Makes S H hw d f α γ (b d))
include hn hA hx hg hs h' h
theorem together : ∃ π : Survey C S, π.X=basis S H hw ∧ (∀ d, (π.Y d).B.b=b d) ∧ π.Ready f := by
  choose Y hB hQ hz using fun d => (hs d).activate
  exact ⟨⟨basis S H hw,Y,fun d => Last.prices (Y d).B h γ η hx hg⟩,rfl,hB,
    fun d => Flow.train (Y d) hn f h hx hg h' hA (hQ d) (hz d)⟩


end YM.Push.Corrected.Recruit
