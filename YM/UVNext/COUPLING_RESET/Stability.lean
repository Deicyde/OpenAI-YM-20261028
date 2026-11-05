import YM.UVNext.COUPLING_RESET.Advance



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# No loss of the bought one-step resetting accuracy through cutoff shooting

Conditional on unmarked physical suppliers with the actual retained Rep &
all evaluation/label and deviation conventions. Thread exactly one choice
and no uncontrolled change of exponents/dictionaries. Relative to the SAME
alpha path the per-edge accuracy is retained, even on a plateau of the
smoothing index; when summing beta shifts we incur their ordinary sum (NOT
claiming this is bounded independently of depth via delaying each index).
Little-o residual is the one guaranteed by the paid calculus at `.Selected`.
No uniqueness across campaigns or among shooting histories and no promotion
to C.Makes or existence. Additional extraction tests & simultaneous-witness
production stay outside this cut.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.BetaTransport Lattice Wilson RG RG.Shoot RG.Supply Input Precision Filter Function Set
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {B : Directed G I Z K P}

/-- In particular `hands` would require
*existence* of activities/masks themselves, even with varying inputs and at
periods/levels not reached by a given successful trajectory.

Exact same paths,
clips & trials, budgets and full near-root shape control, not just validity of
one of several unrelated witnesses at each x. -/
structure Supplier (B : Directed G I Z K P) (η : ℕ → ℝ) (q : ResetPrices) : Prop where
  begins N p : ∃ F, Curve (B.a.budget N) (n:=B.a.S.side N p) F (band B.a N) ∧
      ∀ β∈band B.a N,(F β).beta=β ∧ Lives B.bake N N p (F β) ∧ B.bake.Starter N p (F β)
  hands (N p m) : m < N → ∀ l u : ℝ, l ≤ u → ∀ Q, Curve (B.a.budget (m+1)) Q (Icc l u) →
      (∀ x∈ Icc l u, Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta ∈ band B.a (m+1)) →
      (∃ V, Usable B η N m p V) →
      ∃ V F, Usable B η N m p V ∧ Income B N m p q (Icc l u) Q V F ∧ Remainder B N m p q (Icc l u) Q V F

variable {η : ℕ → ℝ} {q : ResetPrices} {N p m : ℕ}

def Accurate (B : Directed G I Z K P) (q : ResetPrices) (N m p : ℕ) (u : Rep G (B.a.S.side m p))
    (v : Rep G (B.a.S.side (m+1) p)) := |u.beta - v.beta - B.kin.alpha N m| ≤ width B.a m q

lemma Supplier.ports (h : PricedReset B.a η q) (hs : Supplier B η q) (hm : m < N) (l u : ℝ) (hl : l ≤ u)
    (Q : In B.a m p) (hc : Curve (B.a.budget (m+1)) Q (Icc l u))
    (hx : ∀ x∈ Icc l u, Lives B.bake N (m+1) p (Q x) ∧ (Q x).beta ∈ band B.a (m+1)) :
    ∃ T, Curve (B.a.budget m) T (Icc l u) ∧ ∀ x∈Icc l u,
      B.Move N m p (T x) (Q x) ∧ Accurate B q N m p (T x) (Q x) := by
  obtain ⟨V,F,hu,he,hr⟩ := hs.hands N p m hm l u hl Q hc hx (usable B h hm.le p)
  obtain ⟨d,hd,hT⟩ := advance h hm hu he hr hc (fun x hy => (hx x hy).1)
  refine ⟨_,hd,fun x hy => ⟨(hT x hy).1,?_⟩⟩
  convert (hT x hy).2 using 1
  unfold Accurate
  dsimp only [Template.install,Template.trial,predictor]
  simp only [show (Q x).beta + B.kin.alpha N m + d x - (Q x).beta - B.kin.alpha N m = d x by ring]

lemma program (h : PricedReset B.a η q) (hs : Supplier B η q) : B.Program := by
  refine ⟨hs.begins,fun N p m hm l u hl Q hc hx => ?_⟩
  obtain ⟨T,ht,H⟩ := hs.ports h hm l u hl Q hc hx
  exact ⟨T,ht,fun x hy => (H x hy).1⟩






end YM.UVNext.CouplingReset
