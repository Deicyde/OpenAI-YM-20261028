import YM.Next.UV_STRESS.Arrange
import YM.Work.A01.Support
import YM.Work.A04



/-!
# Isomorphisms actually from the weak estimates

Finite comparison used with all-spectator quotient (no uniform-test-space
infinite determinant). Do this already at the smeared level, before jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Table Ward Climb Extraction
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {T : Table L} {n : ℕ} {C : Family G} {F : Order} {S : Table C.book}

/-- A joint test of the first slot of a correlation. -/
structure MeterTest (T : Table L) where
  n : ℕ
  t : Test (n+1)
  q : Fin n → T.Tag

namespace MeterTest
variable (y : MeterTest T)

def headTest (d : ℕ) (v : T.Field d) := Fin.cons (α:=fun _ : Fin (y.n+1) => T.Tag) ⟨d,v⟩ y.q

def checkAt (hc : T.Smooth) (d : ℕ) (r : ℝ) (hr : 0 < r) : T.Field d →ₗ[ℂ] ℂ where
  toFun v := y.t.applyTo fun x => disc (y.headTest d v) (r • x)
  map_add' b c := by
    let F (p : T.Field d) (x : Points (y.n+1)) := disc (y.headTest d p) (r • x)
    have H (p : T.Field d) : ContinuousOn (F p) (conf _) := (smoothZoom hc (y.headTest d p) hr).continuousOn
    have he : F (b+c)=F b+F c := by
      funext x; unfold F headTest disc
      simp only [Pi.add_apply, ← Work.A01.front_eval, map_add]
    change y.t.applyTo (F (b+c))=_
    rw [he]; exact test_add _ _ (H _) (H _) _
  map_smul' a b := by
    have he : (fun x => disc (y.headTest d (a • b)) (r • x))= a • (fun x => disc (y.headTest d b) (r • x)) := by
      funext x; unfold headTest disc; simp only [Pi.smul_apply, ← Work.A01.front_eval, map_smul]
    rw [he]; exact test_smul ..

def zeroScale (hc : T.Smooth) (d : ℕ) := checkAt y hc d 1 one_pos
lemma zeroScale_eq (hc : T.Smooth) (d : ℕ) (v : T.Field d) : zeroScale y hc d v=y.t.applyTo (disc (y.headTest d v)) := by
  change y.t.applyTo (fun x => disc (y.headTest d v) ((1:ℝ) • x))=_; simp

lemma known (T : Table L) (H : T.Hierarchy) (d : ℕ) : Injective (LinearMap.pi fun y : MeterTest T => zeroScale y H.smooth d) := by
  intro u v he
  apply T.field_ext H.laws.toSymmetric
  intro n q x hx
  let F (v : T.Field d) := disc (Fin.cons (α:=fun _ : Fin (n+1) => T.Tag) ⟨d,v⟩ q)
  have hv (v) : ContinuousOn (F v) (conf _) := (smoothDisc H.smooth _).continuousOn
  refine (Test.unique_kernel (hv u) (hv v)).1 (fun t => ?_) hx
  let Y : MeterTest T := ⟨n,t,q⟩
  exact Eq.trans (Y.zeroScale_eq H.smooth _ _).symm ((congr_fun he Y).trans (Y.zeroScale_eq H.smooth _ _))

lemma detects (T : Table L) (H : T.Hierarchy) (d : ℕ) :
    ∃ s : Finset (MeterTest T), Injective (LinearMap.pi (fun y : s => zeroScale y.val H.smooth d)) :=
  Work.A04.finite_faithful _ (known T H d)

variable {U : ℕ → Panel S} {X : Zoom}

def rescaled (H : S.Smooth) (U : Panel S) (y : MeterTest (Bel C.book)) (r : ℝ) (hr : 0<r) (d : ℕ) :
    (Bel C.book).Field d →ₗ[ℂ] ℂ :=
  let z : MeterTest S := ⟨y.n,y.t,panels U ∘ y.q⟩
  (z.checkAt H d r hr).comp (U d)

lemma rescaled_eval (H : S.Smooth) (U : Panel S) (y : MeterTest (Bel C.book)) {r : ℝ} (hr : 0<r) (d : ℕ)
    (v : (Bel C.book).Field d) : rescaled H U y r hr d v = y.t.applyTo (tested r U (y.headTest d v)) := by
  have he : panels U ∘ y.headTest d v = Fin.cons ⟨d,U d v⟩ (panels U ∘ y.q) :=
    Work.A01.comp_cons (panels U) ⟨d,v⟩ _
  unfold tested; simp_rw [he]; rfl

lemma reads_limit (H : S.Smooth) (h : (Bel C.book).Smooth) (ht : Approaches X U)
    (y : MeterTest (Bel C.book)) (d : ℕ) (v : (Bel C.book).Field d) :
    Tendsto (fun k => rescaled H (U k) y (X.r k) (X.positive k) d v) atTop (𝓝 (zeroScale y h d v)) := by
  let q := y.headTest d v
  have he := (ht.values _ q).at_test y.t |>.add_const (zeroScale y h d v)
  rw [zero_add] at he
  refine he.congr fun k => ?_
  rw [rescaled_eval, test_sub (tested (X.r k) (U k) q) _ (smoothZoom H (panels (U k) ∘ q) (X.positive k)).continuousOn
    (smoothDisc h _).continuousOn, zeroScale_eq]
  exact sub_add_cancel _ _

lemma injects (H : S.Smooth) (h : (Bel C.book).Hierarchy) (ht : Approaches X U) (d : ℕ) :
    ∀ᶠ k in atTop, Injective (U k d) := by
  classical
  obtain ⟨s,hs⟩ := detects (Bel C.book) h d
  let F := fun k => LinearMap.pi (fun y : s => rescaled H (U k) y.val (X.r k) (X.positive k) d)
  have he := Dash.fit_plane F (LinearMap.pi fun y : s => zeroScale y.val h.smooth d)
    (fun v => tendsto_pi_nhds.mpr fun y => reads_limit H h.smooth ht _ d v)
  have hp : ∀ᶠ k in atTop, Injective (LinearMap.toContinuousLinearMap (F k)) :=
    he.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (show _ ∈ setOf _ from hs))
  filter_upwards [hp] with k hk
  intro a b h
  apply hk
  change F k a=F k b
  funext y
  change rescaled H (U k) y.val _ (X.positive k) _ _=rescaled H (U k) y.val _ (X.positive k) _ _
  simp only [rescaled,LinearMap.comp_apply,h]
end MeterTest

/-- Only the numerical upper rank. Comes here from `RankWidths.span` (can
alternatively call prep before Seed via another proof of this upper bound). -/
def DimAbove {L : Register G} (S : Table L) := ∀ d, Module.finrank ℂ (S.Field d) ≤ Module.finrank ℂ ((Bel L).Field d)

lemma cap_given (H : Cells.RankWidths C F S) : DimAbove S := by
  intro d
  obtain ⟨X,Z,H⟩ := H d
  obtain ⟨k,hk⟩ := H.span.exists
  rw [show Module.finrank ℂ ((Bel C.book).Field d)= _ from Module.finrank_eq_card_basis X.basis]
  exact finrank_le_of_span_eq_top hk

variable {V : DiffPlan (Bel C.book)} {W : DiffPlan S} {H : S.Hierarchy} {a : (Bel C.book).Hierarchy}

/-- Eventual coherence per degree. Allows spreading requirements for a Track
into how far to go along the path. -/
structure Stable (H : S.RealSpin) (a : (Bel C.book).RealSpin) (W : DiffPlan S) (V : DiffPlan (Bel C.book))
    (X : Scaling S) : Prop where
  hsym d : ∀ᶠ k in atTop, _root_.YM.Spin.realH H a (X.U k d)
  rises (d e : ℕ) (h : d≤e) : ∀ᶠ k in atTop, ∀ v, X.U k e (V.rise h v)=W.rise h (X.U k d v)
  units d : ∀ᶠ k in atTop,X.U k d ((Bel C.book).unit d)=S.unit d

abbrev isoPanel (X : Scaling S) (k : ℕ) : Panel S := fun d => (X.U k d).toLinearMap
def path (X : Scaling S) : Zoom := ⟨X.r,X.positive,X.later,X.drips⟩

/-- First build the exact incl/H path from corrections. Not assumed in station
cost. `Scaling.xi` here does not yet do anything. -/
theorem Stations.equivalences (H : S.Hierarchy) (h : F.Ordered C S) (a : (Bel C.book).Hierarchy)
    (ht : Stations C F a.spin) (hW : W.Inclusions S) (hp : W.Orientation H.spin)
    (hV : V.Inclusions (Bel C.book)) (hf : V.Orientation a.spin) (dim : DimAbove S) :
    ∃ X : Scaling S, Approaches (path X) (isoPanel X) ∧ Stable H.spin a.spin W V X := by
  classical
  obtain ⟨x,U,hU,hy,ha⟩ := Stations.build_curve (H:=H) h a ht
  choose R hR hb hr using fun d => signed_section (H:=a) (Nat.le_succ d) hV hf
  let Q k := corrected W V R (U k)
  have hu d := solid (H:=H) (a:=a) U hp hf R hb hr hU d
  have ha : Approaches x Q := adjusts H a hW hV x R ha
  have he d : ∀ᶠ k : ℕ in atTop, Bijective (Q k d) := by
    filter_upwards [MeterTest.injects H.smooth a ha d] with k hk
    exact ⟨hk,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (le_antisymm (LinearMap.finrank_le_finrank_of_injective hk) (dim d))).1 hk⟩
  let M k d := if p : Bijective (Q k d) then LinearEquiv.ofBijective _ p else
    LinearEquiv.ofBijective _ (he d).exists.choose_spec
  let X : Scaling S := ⟨M,fun _ => 1,x.r,fun _ => one_pos,x.positive,x.shrinking,x.limits⟩
  have hX (d) : ∀ᶠ k in atTop, isoPanel X k d=Q k d := by
    filter_upwards [he d] with k hk
    dsimp only [isoPanel,X,M]; rw [dif_pos hk]; rfl
  have hv (k d e : ℕ) (h : d≤e) z : Q k e (V.rise h z)=W.rise h (Q k d z) :=
    balanced H a _ hW hV R hR d e h z
  refine ⟨X,⟨fun n v => ?_⟩,fun_kit hu hX hv ?_⟩
  · refine (ha.values n v).congr (fun k => (smoothZoom H.smooth _ (X.positive k)).sub (smoothDisc a.smooth v)) ?_
    filter_upwards [eventually_all.mpr (fun i : Fin n => hX (v i).1)] with k hk
    intro y _; change tested _ _ _ _ - _ = tested _ _ _ _ - _
    unfold tested; rw [show (panels (Q k) ∘ v)=panels (isoPanel X k) ∘ v from funext (fun i => by
      change Sigma.mk (v i).1 (Q k _ _) = Sigma.mk (v i).1 (isoPanel X k (v i).1 (v i).2)
      rw [hk])]; rfl
  intro k; simpa only [Q,corrected] using hy k
where
  fun_kit {Q : ℕ → Panel S} {X : Scaling S} (hq : ∀ d, ∀ᶠ k in atTop, StraightAt H.spin a.spin (Q k) d)
      (hX : ∀ d, ∀ᶠ k in atTop, isoPanel X k d=Q k d)
      (hp : ∀ k d e : ℕ, ∀ h : d≤e,∀ z,Q k e (V.rise h z)=W.rise h (Q k d z))
      (hu : ∀ k,Q k 0 ((Bel C.book).unit 0)=S.unit 0) : Stable H.spin a.spin W V X := by
    refine ⟨fun d => ?_,fun d e h => ?_,fun d => ?_⟩
    · filter_upwards [hX d,hq d] with k hk ht
      constructor
      · intro h x
        change (isoPanel X k d) _= S.mirror _ _ _ ((isoPanel X k d) _)
        rw [hk]; exact ht.reflects ..
      intro x; change (isoPanel X k d) _= S.conj _ _ ((isoPanel X k d) _)
      rw [hk]; exact ht.bars ..
    · filter_upwards [hX d,hX e] with k hk he v
      change (isoPanel X k e) _=W.rise h ((isoPanel X k d) _)
      rw [he,hk,hp]
    filter_upwards [hX d] with k hk
    change (isoPanel X k d) _=_
    let h := Nat.zero_le d
    rw [hk,← V.fixs hV a.laws h,hp,hu,W.fixs hW H.laws h]
end YM.Next.UVStress
