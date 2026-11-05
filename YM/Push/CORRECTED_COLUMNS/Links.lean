import YM.Push.CORRECTED_COLUMNS.Axes
import YM.Push.CORRECTED_COLUMNS.Intermediate
import YM.Push.CORRECTED_COLUMNS.Vacuum

/-!
# To the output Offers

Deliberately state the l→h propagation input precisely, on the actual
hierarchy and markers. `train` is one possible sufficient-hypotheses
theorem, with a last common vacuum path. We DON'T give the
physics lemma of unscaled propagation; and the pricing of all the
antecedents (`A_j`, comparison indices and thresholds, terminal gauge,
etc.) together with its own engine fees (pre-L etc.), during original
calendar construction, remains required for usage. Cf. . In particular, cannot use positivity of a
wrong projection, assume weak couplings stay in a band by fiat in that
producer, or pay the K polynomial only for two cells here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Flow
open RG.Supply Filter Function Set Lattice Wilson RG MeasureTheory Marker Overlay Prepare Width Endpoint Cells Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {d : ℕ} {X : Columns C S d} (Y : Tests X)

-- `Meeting.uniform` on the very same columns isn't another assumption.
-- Prove even for all k (finitely many small k covered, no ties problem).


-- All markers descend to the known parent address.
def origin (k N p : ℕ) (i : Row X) {m : ℕ} (h : Y.B.depth k ≤ N) (hn : m≤N)
    (s : Copies Y k p × Mark X i) : Site (C.side m p) :=
    let T := center C.S p ((Y.B.side_le k).trans h) 0
    (C.S.toDepth hn p).parent (T.copyMap s.1 (Y.location k N p i s.2))

section
variable (k N p) (B : Wire C (Y.B.side k) (Y.B.depth k) N p)

/-- Actual per-step at j. `K` is a representation (can take all P
*enlarged*) in this stretch, keeping paths etc, empty padding available.
Tests same RHS on its actual full-copy arrays. `g`, `x` and `e` are
roof value bounds available (weights *already restored*) on each step, e
the forced-only cap (may need smallness in a stronger norm than its part
of the total). -/
def Wears (h : Y.B.depth k ≤ N) (i : Row X) (c : AxisX X)
    {j : ℕ} (hn : j ≤ N) (K : Rep G (C.side j p)) (a w g x e : ℝ) :=
    ∃ W : Bands (Marks.all (Copies Y k p × Mark X i)) K,
    ∃ u v r : ℝ, u≤g ∧ u+v+r ≤ x ∧ r ≤ e ∧ W.origins = origin Y k N p i h hn ∧
      Further W (fun _ => w) K.p.B a u v r ∧ W.density=B.station ((Y.B.side_le k).trans h) hn (Y.pattern k N p i c)
/-- One possible *input* for the next steps (from kraw analogue).
At every step in the parent run r ≤ j < middle, having Wears at
j+1 SCOPED to THE actual polynomial for these columns, produce anew at j.
No independent arrays aside from each i,c full-marker use. It is intended
one chooses `g` thresholds/witnesses including the appropriate decrease
rates *before* calling these estimates; needs to remain affordable at the
next rung, including same-exponent if required. It includes no conceptual
L stretch past chosen Calendar. Witness of vacuum on all used scales
required separately.
-/
structure Courtesy (h : Y.B.depth k≤N) (K : ∀ m, Rep G (C.side m p)) (a g x e : ℕ→ℝ) (w : ℝ) : Prop where
    flow (m : ℕ) (hm : m≤Point.middle Y.B k) (hr : Y.B.side k ≤ m) :
      let R:= Pad.enlarge (K m)
      R.eval = B.vacuum m (hm.trans ((Point.debits Y.B k).trans h)) ∧ R.beta=B.cost m ∧ ∃ κ, Last.Comparable C (m:=m) R κ
    step (i : Row X) (c : AxisX X) m (ht : m < Point.middle Y.B k) (hr : Y.B.side k ≤ m) :
      let t : m+1≤N := ht.trans_le ((Point.debits Y.B k).trans h)
      Wears Y k N p B h i c t (Pad.enlarge (K (m+1))) (a (m+1)) w (g (m+1)) (x (m+1)) (e (m+1)) →
      Wears Y k N p B h i c (le_trans (Nat.le_succ m) t) (Pad.enlarge (K m)) (a m) w (g m) (x m) (e m)

lemma turns {h : Y.B.depth k≤N} {K} {a g x e w} (H : Courtesy Y k N p B h K a g x e w) (i : Row X) (c : AxisX X)
    (ht : let m := Point.middle Y.B k
          Wears Y k N p B h i c ((Point.debits Y.B k).trans h) (Pad.enlarge (K m)) (a m) w (g m) (x m) (e m)) :
    let m := Y.B.side k
    Wears Y k N p B h i c ((Y.B.side_le k).trans h) (Pad.enlarge (K m)) (a m) w (g m) (x m) (e m) := by
  let l := Point.middle Y.B k
  have he : l≤N := (Point.debits Y.B k).trans h
  have hu m (hm : m ≤ l) (hh : Y.B.side k≤m) :
      Wears Y k N p B h i c (hm.trans he) (Pad.enlarge (K m)) (a m) w (g m) (x m) (e m) := by
    induction hm using Nat.decreasingInduction with
    | self => exact ht
    | of_succ j hj ih => exact H.step i c j hj hh (ih (hh.trans j.le_succ))
  exact hu _ (Point.credit Y.B k) le_rfl

/-- SCOPED input crew to reach Offers, concrete per-level hypotheses (`Meeting`
and `step` remain highly nontrivial/open). `starts` needs at the level
`middle`, same as comparisons; one K even if its expansions per row differ.
For concreteness bank F etc. universe fixed: can use ℕ for X (addresses),
as comparison budgets are explicitly absolute. `α` threshold for total
marker price at width. -/
structure Crew (α : ℝ) (W : ℝ) : Prop where
  arrives : ∃ (h : Y.B.depth k ≤ N), ∃ K a g x e, Courtesy Y k N p B h K a g x e W ∧ x (Y.B.side k) ≤ α ∧
    ∀ (i : Row X) (c : AxisX X),
    let l := Point.middle Y.B k
    let H := K l
    let hp := (Point.debits Y.B k).trans h
    let y := origin Y k N p i h hp
    ∃ (A : Heads (K l).p y G) (F : Original H y (Marks.all (Copies Y k p × Mark X i))) (L : Atoms (K l).p (Marks.all _) y G ℕ),
       ∃ w D κ b η ζ J R q₀ m,
       Meeting Y k N p i c B A F L ((Y.B.side_le k).trans h) hp w W D κ b η ζ (a l) J R q₀ m ∧
       0 ≤ g l ∧ rewardE (Mark X i) (a l) b ζ W η q₀ + rewardK J κ m ≤ x l ∧ rewardK J κ m ≤ e l
end

/-- These mark bills, coupled to geometry pricing and buys at the same
startup parameters, actually yield the Offer used in `common`. For one
concrete exponents scope pair γ,η at all clusters.
-/
theorem train {q : Sheet G} {w : Rolls q} {T : Protection w} {W : Delays T} {v : Bar W} {U : Wait v}
    (hp : Paid U (lvl C)) (f : Extraction.Order) {α} {γ η : ℝ} (h : G.Simple) (hη : 0<η) (hγ : η < γ)
    (ha : Last.OnPage W η 2 α) (hα : ∀ j,0≤α j)
    (he : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ∀ p, ∀ᶠ i : ℕ in atTop, ∀ c, ‖Y.tune k (f.mesh i) p c‖ ≤ D)
    (H : ∀ k, f.late fun N p => ∃ (B : Wire C (Y.B.side k) (Y.B.depth k) N p), Crew Y k N p B
      (α ((lvl C).clock.J (Y.B.side k))) ((lvl C).clock.monitor (Y.B.depth k)^γ)) :
    Tests.Offer Y (Last.prices Y.B h γ η hη hγ) f := by
  refine Last.page Y hp f h hη hγ ha hα he fun k => ?_
  refine (H k).mono fun j hj => hj.mono ?_
  rintro m ⟨B,U⟩
  obtain ⟨hn,K,a,g,x,e,hK,hx,h⟩ := U.arrives
  let l := Point.middle Y.B k
  let n := Y.B.side k
  obtain ⟨hi,hh,κ,hP⟩ := hK.flow n (Point.credit Y.B k) le_rfl
  refine ⟨hn,B,Pad.enlarge (K n),κ,hP,hi,hh,fun i c => ?_⟩
  obtain ⟨A,F,L,w,D,k₀,b,η,ζ,J,R,q₀,p,hM,hu,hc,hR⟩ := h i c
  obtain ⟨W,hW,hU,hS⟩ := (Endpoint.print Y k _ _ i c B A F L hM).2
  have hw := turns Y k _ _ B hK i c ⟨W,_,_,_,hu, by rw [zero_add]; exact hc,hR,hW,hS.2,hS.1⟩
  obtain ⟨Q,u,b',c',-,hz, -,hi,he,h⟩ := hw
  refine ⟨Q,u,b',c',hz.trans hx,he.toValue,fun z U => ?_, fun i => ?_⟩
  · rw [h]; exact Wire.station_point ..
  rw [hi]
  exact Y.anchor k _ _ _ i.2 hn i.1
end YM.Push.Corrected.Flow
