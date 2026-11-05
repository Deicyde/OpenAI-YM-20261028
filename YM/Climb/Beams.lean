import YM.Climb.Peaks
import YM.Spin.Lands
import YM.Ward.Axis

/-!
# assembly ports including H weak comparator matrix demands

K spins. d-term specialization inside τ maybe sign-flipped T, not
requiring a particular formula of stress in final. Need witness meets on
all finite boxes & all degrees; κ chosen fixed and nonzero. Need a common
choice of sign of stress0 as d,m,N increases: criterion need uses depend;
if comparing sign-dependent subsequences only prove this by finite pigeonhole
across cofinal demands (can flip *all* choices or select same orientation infinite subsequence).

This is stronger than T claim. Production outstanding.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Climb
open Filter Function Set Analysis Extraction Table Spin Ward Maxwell
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {G : Gauge} {L : Register G} {S : Table L}

structure Lighthouse (L : Register G) where
  W : DiffPlan (Bel L)
  K : Rotation (Bel L)
  J : (Bel L).Stress
  κ : ℝ
  hκ : κ ≠ 0

/-- K covariance ordinary rotations Extend by calculus proved later. J needn't
be canonical Maxwell stress in formal proof, but planning κ*negative chosen.
-/
structure Lighthouse.Goes (L : Register G) (T : Lighthouse L) (h : RealSpin (Bel L)) : Prop where
  edges : T.W.Inclusions (Bel L)
  pales : T.W.Derivatives (Bel L)
  hers : T.W.Orientation h
  turns : T.K.Laws T.W h
  preserves : T.K.Oriented (Bel L)
  delta : StressLaws (Bel L) T.J ((T.κ : ℝ) • T.W.deriv) (T.κ • T.K.lie)
  born : leaves T.W.deriv 4 ≠ 0
  cuts : ∃ n : ℕ, ∀ d≥n, ∃ e : Select L d, Ens e T.W h

structure Track (X : Scaling S) (P : DiffPlan S) (T : Lighthouse L) (J : S.Stress)
    (H : S.RealSpin) (h : (Bel L).RealSpin) (N d m : ℕ) (R : ℝ) : Prop where
  path : X.Align P T.W H h (max d 4)
  thick : X.jets N d m R
  loc : X.meter J T.J

structure ActLaw (P : DiffPlan S) (T : Lighthouse L) (J : S.Stress) (H : S.RealSpin) (h : (Bel L).RealSpin) : Prop where
  connects N d m R : (1:ℝ)≤R → ∃ X, Track (S:=S) X P T J H h N d m R

lemma comparison {P : DiffPlan S} {T : Lighthouse L} {J h a} (hp : ActLaw P T J h a) : Maxwell.Ranks S h := by
  refine ⟨a,fun d => ?_⟩
  obtain ⟨X,hX⟩ := hp.connects 0 d 0 1 le_rfl
  let U := X.U 0 d
  have HH := hX.path.Hsym 0 d (le_max_left ..)
  refine ⟨U.symm,fun x => U.injective ?_,fun k x => U.injective ?_⟩
  · rw [show _=_ from HH.2 (U.symm x)] -- orientation?
    change U _=S.conj h d (U _)
    rw [U.apply_symm_apply,U.apply_symm_apply]
  rw [show U ((Bel L).mirror _ d k (U.symm x)) =_ from HH.1 k _]
  change _=S.mirror h d k (U (U.symm x)); rw [U.apply_symm_apply,U.apply_symm_apply]

/-- Param pivot used BEFORE assigning any spin law. -/
structure Pre (H : S.Hierarchy) (V : DiffPlan S) (J : S.Stress) (p : Parts S) (Y : SpinRows S) : Prop where
  tensor : Conserved V H.spin J
  symmetric : RawTensor H.spin J
  raw : StressLaws S J p Y


def localTurn (p : Parts S) (T : SpinRows S) (K : Ortho.Skew) {n : ℕ} (q : Fin n → S.Tag) (x : Points n) :=
    ∑ i, (disc (update q i (turns T K (q i))) x + ∑ b : Axis, ((M4.move K.val (x i) b) •
      disc (update q i (⟨_,p _ b (q i).2⟩:S.Tag)) x))

structure Shapes (H : S.Hierarchy) (V : DiffPlan S) (J : S.Stress) (p : Parts S) (Y : SpinRows S) : Prop where
  local_ : Pre H V J p Y
  rights : ColorLaw p V H.spin
  fills : transverse p
  orient (K : Ortho.Skew) (a : Axis) (n : ℕ) (q : Fin n → S.Tag) (x : Points n) : x∈conf _ → onLine a x → localTurn p Y K q x=0

/-- After actual Γ= c^-1 S. Need derive brackets, not assume small comm. -/
structure Crystal (H : S.Hierarchy) (V : DiffPlan S) (J : S.Stress) (p : Parts S) (Y : SpinRows S) (c : ℝ) : Prop where
  positive : c≠0
  pre : Shapes H V J p Y
  sizes d : leaves p d=c • leaves V.deriv d
  ready : commutes V ((c⁻¹:ℝ) • Y) ∧ Collinear V ((c⁻¹:ℝ) • Y)

/-- Explicit consumer taking same weak matrices V Y J. -/
lemma descends (T : Lighthouse L) {a : RealSpin (Bel L)} (hT : T.Goes L a) (H : S.Hierarchy) (V : DiffPlan S)
    {J : S.Stress} {p : Parts S} {c : ℝ} {Y : SpinRows S} (hc : Crystal H V J p Y c) (h : V.Derivatives S)
    (hp : (∀ n (x : Points n), x∈conf n → Still V (c⁻¹ • Y) x) → ∀ d, ∃ U w, Spin.Tilt T.K H.spin a (c⁻¹ • Y) d U w) :
    ∃ U : ∀ d,Spin.change S d, (∀ d,realH H.spin a (U d)) ∧ let Z := morph T.K (c⁻¹ • Y) U; Spin.Port Z H.spin ∧
      ∀ n (x : Points n), x∈conf n → Still V Z.lie x := by
  have hv n (x : Points n) (hx : x∈conf n) : Still V (c⁻¹ • Y) x := Ward.global S H V _ h hc.ready.1 hc.ready.2 x hx
  obtain ⟨U,hU,hr⟩ := Spin.produces (S := S) T.K _ (hp hv)
    (⟨hT.turns.spin,hT.turns.fixes,hT.turns.group,hT.turns.signed,hT.turns.real,hT.turns.infinitesimal⟩)
  exact ⟨U,hU,hr,hv⟩
end YM.Climb
