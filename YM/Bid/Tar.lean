import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Org.Input
import YM.Shift.Exchange
/-!
# Tube & support mission
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Function Set Filter Analysis Spectral MeasureTheory Measure Distribution Mink Mink.Poincare Boundary Boundary.Surface Probe Complex
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ContDiff

variable {G : Gauge} {L : Register G} {n : ℕ} {S T : Table L}

-- dual damping
structure Wide (n : ℕ) : Prop where
  rim p y : p∈coneM n → y∈shores n → 0 ≤ inner ℝ p y
  cone (y : Points n) (p : y∈fields n) : ∃ c : ℝ,0<c ∧ ∀ᶠ u in 𝓝 y,∀ p∈coneM n,c * ‖p‖ ≤ inner ℝ p u

def C10 : Prop := ∀ i, Wide i

def C11 : Prop := ∀ i, Nonempty (Blanket i)

def C12 : Prop := ∀ n, Wide n → ∀ A : Blanket n, A.Modified

/-- Entire open tube holomorphy and existence of Lens test. -/
def C13 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (W : Surface S) (D : ∀ i, Blanket i),
    (∀ i, Wide i) → (∀ i, (D i).Modified) →
    ∃ X : W.Aurora D, ∀ n (v : Fin n → S.Union), AnalyticOnNhd ℂ (X.emit v) (tube n)

-- C18 uses FullBody Visible ∀ F; assumption supplies both Hol actual choices

structure Income {W : Surface S} {D} (Y : W.Aurora D) : Prop where
  builds (n : ℕ) (v : Fin n → S.Union) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    (D n).partialD (W.W n v) y f= ∫ x,Y.emit v (glow x y) * f x
  leaned (n : ℕ) (v : Fin n → S.Union) (y : Points n) (hy : y∈fields n) (f : Joint n) :
    Integrable (fun x => Y.emit v (glow x y) * f x)

def cones (W : Surface S) := ∀ n (v : Fin n → S.Union), dsupport (Distn.fourier (W.W n v)) ⊆ coneM n
-- possible Mathlib Moulin integral vector difficulty. REVIEW size.
def C14 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (W : Surface S) (D : ∀ i,Blanket i),
    (∀ i,(D i).Modified) → cones W → C10 → ∀ Y : W.Aurora D, (∀ n (v : Fin n→ S.Union), AnalyticOnNhd ℂ (Y.emit v) (tube n)) → Income Y

def C15 : Prop := ∀ {G : Gauge} {L : Register G} {S T : Table L} (W : Surface S) (D : ∀ i,Blanket i), (∀ i,(D i).Modified) →
    cones W → ∀ Y : W.Aurora D, (∀ n (v : Fin n→ S.Union), AnalyticOnNhd ℂ (Y.emit v) (tube n)) → Income Y → ∀ F : Waves S,
    F.Region T → F.Breathes → F.Bounds → F.during W → Y.FullBody F

def rect (K : Lorentz) (x : Full n) := glow (togetherL K n (reality x)) (togetherL K n (shade x))

def wave_turn (_ : Waves S) (W : Surface S) (D : ∀ i,Blanket i) (Y : W.Aurora D) (U : Spins S) :=
    ∀ n (v : Fin n→S.Union) (K : Lorentz) x, x∈tube n → Y.emit v x=Y.emit (fun i => U.rail K (v i)) (rect K x)

def C16 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (W : Surface S) (K : Spins S) (D : ∀ i,Blanket i) (Y : W.Aurora D) (F : Waves S),
    (∀ i,(D i).Modified) → cones W → Urs W K → Y.FullBody F → wave_turn F W D Y K

-- Holomorphic path standard API for transfer.
def augment (e : Ray) (z : ℂ) (x : Full n) : Full n :=
    x + (Complex.sinh z) •
      glow (points fun i => e.crossT (reality x i)) (points fun i => e.crossT (shade x i)) +
      (Complex.cosh z-1) • glow (points fun i => e.scalesT (reality x i)) (points fun i => e.scalesT (shade x i))

/-- absolute y's; both signs because inverse function's coordinate order. -/
def travelable (e : Ray) (P : NearPair n) (t : ℝ) (x : Full n) :=
    0<t ∧ augment e (↑t*I) x∈tube n ∧ P.name (augment e (-↑t*I) x)∈tube n ∧
    (∀ᶠ y in 𝓝[tube n] x,∀ b : ℝ, b∈Icc 0 t → augment e (↑b*I) y∈tube n) ∧
    (∀ᶠ y in 𝓝[P.name ⁻¹' tube n] x,∀ b : ℝ, b∈Icc 0 t → P.name (augment e (-↑b*I) y)∈tube n)

def C17 : Prop := ∀ n (P : NearPair n), ∃ y : ℕ→Heights n, Tendsto (dawn ∘ y) atTop (𝓝 0) ∧
    ∀ m, P.Fleck (y m) ∧ ∀ x∈ P.gap, ∃ (e : Ray) (t : ℝ), travelable e P t (glow x (dawn (y m)))

/-- boost path extends to imaginary parameter. Independent of pane/tensor. -/
def Weighty {S : Table L} (K : Spins S) := ∀ (d : ℕ) (e : Ray), ∃ U : ℂ→ (S.Field d→L[ℂ] S.Field d), AnalyticOnNhd ℂ U univ ∧ ∀ (t : ℝ) v,
    U (↑t) v=K.shell d (e.boost t) v

def C18 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (R : S.Rotation) (h : S.RealSpin) (K : Spins S), K.Descends R h →
    Weighty K

def C19 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (K : Spins S) (W : Surface S) (D : ∀ i, Blanket i) (F : Waves S)
    (X : W.Aurora D), cones W → X.FullBody F → ∀ R h (_ : K.Descends R h),∀ P : DiffPlan S,
    S.Symmetric → P.Inclusions S → Weighty K → wave_turn F W D X K → ∀ n v (Z : NearPair n) (y : Heights n),
    Z.Fleck y → (∀ x∈Z.gap,∃ (e : Ray) (t : ℝ), travelable e Z t (glow x (dawn y))) → Nonempty (Z.Panes X v y)

/-- same data at boundary via jets, no global Schwarz reflection assumption. -/
def C20 : Prop := ∀ {G : Gauge} {L : Register G} {S T : Table L} (P : DiffPlan S) (F : Waves S) (Y : Surface S) (D : ∀ i,Blanket i) (Z : Y.Aurora D),
    S.Symmetric → P.Inclusions S → T.Symmetric → T.Smooth → T.respects S → F.Region T → Z.FullBody F →
    ∀ n (v : Fin n → S.Union) (h : Heights n) (X : NearPair n) (A : X.Panes Z v h), A.sameGround

/-- table restrictions are the partial distribution from emitted germ. -/
def C21 : Prop := ∀ {G : Gauge} {L : Register G} {S : Table L} (F : Waves S) (Y : Surface S) (D : ∀ i,Blanket i) (Z : Y.Aurora D),
    (∀ i,(D i).Modified) → Z.FullBody F → ∀ n (v : Fin n → S.Union) (h : Heights n) (X : NearPair n) (A : X.Panes Z v h), A.Forms
end YM.Bid
