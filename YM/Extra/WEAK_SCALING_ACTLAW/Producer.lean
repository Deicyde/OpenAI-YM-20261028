import YM.Extra.WEAK_SCALING_ACTLAW.Normalize
import YM.Next.BOUNDARY.Synchronize

/-!
# The conditional common-field ActLaw producer

Retain the full input even if using later ordered refinements in pricing
finite demands / extracting columns. No period- or stress-dependent change
of continuum tables permitted. Choose the sign consistently **before** any
applications of the curve hypotheses to the rest of reconstruction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Function Filter Set Table Ward Climb Extraction Org Spec
open scoped Topology ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {V : DiffPlan S} {T : Lighthouse L} {J : S.Stress}
variable {h : S.RealSpin} {H : (Bel L).RealSpin}

lemma smaller {X : Scaling S} {N d m N' d' m' : ℕ} {R Q : ℝ} (hr : 1 ≤ R) (hr' : R ≤ Q)
    (hn : N ≤ N') (hd : d ≤ d') (hm : m ≤ m') (hw : Track X V T J h H N' d' m' Q) : Track X V T J h H N d m R := by
  have he := max_le_max_right 4 hd
  refine ⟨⟨fun k d hb => hw.path.Hsym k d (hb.trans he),fun k d hb => hw.path.carries k d (hb.trans he),
    fun k d e hi hb => hw.path.incl k d e hi (hb.trans he)⟩, fun n hN j hj v hv ε hε => ?_, hw.loc⟩
  filter_upwards [hw.thick n (hN.trans hn) j (hj.trans hm) v (fun i => (hv i).trans hd) ε hε] with k hk x hx
  have h : Q⁻¹ ≤ R⁻¹ := (inv_le_inv₀ (by linarith) (by linarith)).2 hr'
  exact hk x ⟨fun i j he => h.trans (hx.1 i j he), hx.2.trans hr'⟩

lemma coherent (hw : ∀ N d m (R : ℝ), 1 ≤ R → (∃ X, Track X V T J h H N d m R) ∨
    (∃ X, Track X V (flip T) J h H N d m R)) : ActLaw V T J h H ∨ ActLaw V (flip T) J h H := by
  by_cases ht : ∀ N d m (R : ℝ), 1 ≤ R → ∃ X, Track X V T J h H N d m R
  · exact Or.inl ⟨ht⟩
  push Not at ht
  obtain ⟨N,d,m,R,hr,hn⟩ := ht
  refine Or.inr ⟨fun n e j Q hQ => ?_⟩
  rcases hw (max N n) (max d e) (max m j) (max R Q) (hr.trans (le_max_left ..)) with ⟨X,hX⟩|⟨X,hX⟩
  · exact (hn X (smaller hr (le_max_left ..) (le_max_left ..) (le_max_left ..) (le_max_left ..) hX)).elim
  exact ⟨X,smaller hQ (le_max_right ..) (le_max_right ..) (le_max_right ..) (le_max_right ..) hX⟩

variable {C : Family G} {S : Table C.book} {f : Order}

/-- Can use further orders, even separately per comparison request **on f**.

Supplying it
only for some initial table or independent extraction disconnected from the
seed/order doesn't count.

Don't invoke the port afresh on a sub-subsequence
obtained after using it. -/
def Supply (C : Family G) (f : Order) (h : (Free C).RealSpin) : Prop :=
    ∀ M D Q, (1:ℝ) ≤ Q → ∃ (g : Order) (b : Stations C), FiniteCosts b (f.refine g) h M D Q

variable (s : Seed C f S) (W : MaxwellData C) (hc : Supply C f W.hT.spin)
include s
include hc in
lemma surveyed (M D : ℕ) (Q : ℝ) (hq : 1 ≤ Q) : Nonempty (Survey S s.kernel.spin W.hT.spin M D Q) := by
  obtain ⟨g,b,hb⟩ := hc M D Q hq
  obtain ⟨u,⟨hu⟩⟩ := hb.ready
  have hs := Next.BOUNDARY.keep_seed s (g.refine u)
  exact ⟨hu.survey hs (by linarith) (hb.further u)⟩

def Pool (s : Seed C f S) (W : MaxwellData C) := ∀ M D Q, 1 ≤ Q → Nonempty (Survey S s.kernel.spin W.hT.spin M D Q)

variable (hb : Pool s W)
include hb
lemma ranks_available (d : ℕ) : Nonempty (YM.Spin.change S d) := by
  obtain ⟨M,D,Q,-,hd,hq,-,hw⟩ := equipment W.hT d 0 1
  obtain ⟨b⟩ := hb M D Q hq.le
  obtain ⟨k,hk⟩ := (b.eventually_bijective s hd (hw d le_rfl)).exists
  exact ⟨LinearEquiv.ofBijective _ hk⟩

variable {V : DiffPlan S} {I : IR (C:=C) S}
lemma Pool.curves (N D : ℕ) (R : ℝ) (hr : 1 ≤ R) (hV : V.Inclusions S) (hV' : V.Derivatives S) :
    ∃ Q : ℝ, R < Q ∧ Nonempty (Curve V W.T.W s.kernel.spin W.hT.spin N D Q) := by
  obtain ⟨M,D',Q,hM,hD',hQ,-,hw⟩ := equipment W.hT D N R
  obtain ⟨b⟩ := hb M D' Q (hr.trans hQ.le)
  have he := Work.D06.answer s.cutoff s.kernel.smooth s.kernel.laws.toSymmetric s.generic V hV' hV s.kernel.spin
  exact ⟨Q,hQ,trace_curve s (H:=W.hT) b (ranks_available s W hb) hM hD' hw hV W.lit.edges hV' W.lit.pales he W.lit.hers⟩

/-- Includes **the same** J on input and output. W must already have its
stress along the nonzero free Wick stress with mean removed (obligation
`Line` and `W.lit` etc. on this same W; will get J⁰ or -J⁰, not an arbitrary
limit or k-dependent multiple). Does not use/assign normalization to p,Y
here. They keep their local laws at J.
-/
theorem Pool.act (hV : V.Inclusions S) (hV' : V.Derivatives S) (hp : Pre s.kernel V I.J I.p I.Y)
    (hJ : I.J ≠ 0) (hz : Centered I.J) (hW : Line W.T W.hT.spin) :
    ActLaw V W.T I.J s.kernel.spin W.hT.spin ∨ ActLaw V (negative W).T I.J s.kernel.spin (negative W).hT.spin := by
  refine coherent fun N d m R hr => ?_
  obtain ⟨Q,hQ,⟨b⟩⟩ := Pool.curves s W hb (max N 1) ((max d 4)+m+1) R hr hV hV'
  exact b.choose_track hr hQ le_rfl (by omega) s.kernel hV' W.hT W.lit.pales hJ hp.tensor hp.symmetric hz hW

omit hb
include hc
theorem weak_curve (N D : ℕ) (R : ℝ) (hr : 1 ≤ R) (hV : V.Inclusions S) (hV' : V.Derivatives S) :
    ∃ Q : ℝ, R < Q ∧ Nonempty (Curve V W.T.W s.kernel.spin W.hT.spin N D Q) := Pool.curves s W (surveyed s W hc) N D R hr hV hV'

theorem act (hV : V.Inclusions S) (hV' : V.Derivatives S) (hp : Pre s.kernel V I.J I.p I.Y)
    (hJ : I.J ≠ 0) (hz : Centered I.J) (hW : Line W.T W.hT.spin) :
    ActLaw V W.T I.J s.kernel.spin W.hT.spin ∨ ActLaw V (negative W).T I.J s.kernel.spin (negative W).hT.spin :=
    Pool.act s W (surveyed s W hc) hV hV' hp hJ hz hW

lemma grades (hV : V.Inclusions S) (hV' : V.Derivatives S) (hp : Pre s.kernel V I.J I.p I.Y)
    (grill : Grill C f) (hJ : I.J ≠ 0) (hz : Centered I.J) (hW : Line W.T W.hT.spin) :
    UV C f S V W I ∨ UV C f S V (negative W) I := by
  have he := Work.D06.answer s.cutoff s.kernel.smooth s.kernel.laws.toSymmetric s.generic V hV' hV s.kernel.spin
  rcases act s W hc hV hV' hp hJ hz hW with h|h
  · exact Or.inl ⟨s,he,hp,h,grill⟩
  exact Or.inr ⟨s,he,hp,h,grill⟩

omit s hc in
theorem keep_uv {W : MaxwellData C} {S₀ : Table C.book} {P : ℕ → Table C.book} (A : Arrives C f S₀ P)
    (B : Cleaner S₀ P S V f) (H : UV C f S V W I) (g : Order) :
    Arrives C (f.refine g) S₀ P ∧ Cleaner S₀ P S V (f.refine g) ∧ UV C (f.refine g) S V W I := by
  refine ⟨Next.BOUNDARY.keep_arrives A g,Next.BOUNDARY.keep_cleaner B g, Next.BOUNDARY.keep_seed H.basis g,
    H.aligned,H.planet,H.weak, fun d m => ?_⟩
  obtain ⟨k,hk,hw⟩ := H.tables d m
  refine ⟨k,hk,fun n v ht hV x hx => ?_⟩
  obtain ⟨X,hX⟩ := hw n v ht hV x hx
  exact ⟨X,(Next.BOUNDARY.refine_fits f g).plots hX⟩
end YM.Extra.WeakScaling
