import YM.Progress.STATIONARY_SCENES.Classical


/-!
# Invoke RScene inside a `Planned` construction

Sufficient client script. Specifies EXACTLY open Top and per-call inputs
for this version. Each `go` is made on the just purchased Answer and THEIR
chosen rho. Choose alpha and the actual next W together using THAT solution,
for all period demands. Show full output keeping the Invoice invariant. Not
interpret availability of the green schedule/scene as constructing those
classical/quantum data. Don't silently pay at lesser widths or work on other
trees. `retain` optional further unary path controls to carry step estimates
(e.g. higher-width, auxiliary representational tests); if using those also
expose and prove them. This isn't the only route; can call Service instead
directly inside a more history-sensitive induction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes
open Filter Lattice RG RG.Supply Wilson Precision Bid Tree Function Matrix Exterior
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Q : PostCost D} {O : ChartRatio G}
  {a : Levels G} {H : Horizon a} {K : MapPrices}

/-- Remaining peak invoice. -/
def Summit (a : Levels G) (N : ℕ) (P : PathData G) : Prop :=
    (∀ i, (P.loop i).coeff=0) ∧ ∀ p,
      let f := fun x : Dir G (a.S.side N p) => mainTerm (a.params N).clip P (represent x)
      let g := fun x : Dir G (a.S.side N p) => Wilson.energy (represent x)
      iteratedFDeriv ℝ 3 f 0 = iteratedFDeriv ℝ 3 g 0 ∧
      iteratedFDeriv ℝ 4 f 0 = iteratedFDeriv ℝ 4 g 0

/-- Full remaining invoice this client uses. alpha tested at REAL sign
with the planned pre price. Post period-error constants unmodified in the
JOINT generation of that coefficient and the same next T. Open path invoice
also below, don't claim from these estimates such normalization can be done.
One tag/tree for this version; `thermal_match` and `classical_match` even
allow the one geometry to test to be different in the two verifications. -/
def Handoff (O : ChartRatio G) {P : PathData G} {N m : ℕ} (R : Answer H N m P (Q.η (a.clock.J (m+1))))
    (α : ℝ) (T : PathData G) : Prop :=
    |α + G.slopeConstant*Real.log (a.S.block m).val| + 1 ≤ (a.params (m+1)).drift ∧
      ∀ p : ℕ, ∃ (t : (a.clock.op m p).Choices) (F : Forest (a.clock.op m p).ratio),
        let f := R.classicalValue p F t
        let c := a.S.side m p
        let v := (a.params m).clip
        let g := fun x : Dir G c => mainTerm v T (represent x)
        let h := thermal F t (a.params (m+1)).clip P (R.station p F) O
        let j := a.clock.J (m+1)
        iteratedFDeriv ℝ 3 f 0 = iteratedFDeriv ℝ 3 g 0 ∧
        iteratedFDeriv ℝ 4 f 0 = iteratedFDeriv ℝ 4 g 0 ∧
        ∀ (x y : Site c) (σ τ : TypeFace 1 → G.ColorIndex → ℂ),
          (∀ x y, ‖σ x y‖≤1) → (∀ x y, ‖τ x y‖≤1) →
          let W := ![wave x σ,wave y τ]
          |iteratedFDeriv ℝ 2 h 0 W - iteratedFDeriv ℝ 2 (draft α T v) 0 W| ≤
            (Fintype.card (Site c):ℝ)*Q.Γ j*a.clock.loopCap (m+1)*Real.exp (-Q.c j*c.val)

/-- Generators conditional. `retain` can be True if e.g. proving the estimates
literally on every funded W. Else MUST inherit, from N right downwards to 0.
Doesn't assume Scene, doesn't demand all paths chosen in advance. -/
structure Proposals (C : Service a K Q H) (O : ChartRatio G)
    (retain : ℕ → ℕ → PathData G → Prop) : Prop where
  top N : ∃ P : PathData G, Funded H N N P ∧ retain N N P ∧ Summit a N P
  go N m (h : m < N) (P : PathData G) (hp : Funded H N (m+1) P) :
    retain N (m+1) P → ∃ α T, Funded H N m T ∧ retain N m T ∧ Handoff (Q:=Q) O (C.sends h hp) α T

namespace Client
variable {C : Service a K Q H} {d : ℕ → ℕ → PathData G → Prop}


end Client


end YM.Progress.StationaryScenes
