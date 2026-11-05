import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Season
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Line

/-! # The joint-load and same-law event consumer with actual trigger
choices & support tests (through rank prices even at charged zeros)

NOT supplying `Casting` or its terms/identities/true view etc. Explicit
remaining hypotheses in `Ordered`/`Plaid`. OTHER parts of `Ω_ht`, h-parents
before the ξ-telescope and all ineligible/compulsory exponents still need
their per-factor bills; the recursive outputs still need to absorb those &
the ancillary/polynomial pieces of `invests`. Trigger suppression per
DISTINCT physical address actually given in the components of this word.
Doesn't allow identifications of occurrences at repeated tuples later. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure ProjectorNext.Equivariance Heir AnalyticBridge.LocalGaussian
   Spot Spot.Programme Notice Reading Tariff Pitch Folio Clockwork MeasureTheory
open AnalyticBridge.AnnulusRatioInsertions.Prism AnalyticBridge.AnnulusRatioInsertions.Parade AnalyticBridge.NonflatCovarianceLocality.Placement
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio} {κ : S.Choices} {d : Desk G S} {u : Spot d} {V : Config G c}
    {Ω : Set (Config G c)} {H R ι α β γ : Type} {X : Support c} {l : Viewport u X H R ι} {ds : u.Slices} {b : Finset ℕ} {q : Programme ds b} {n : q.Run α β γ} {D : Record} {N m : ℕ}
    {a : Notice l} {s : Reading a n} {t : Seats l n} {θ L r r' W : ℝ} {o : Site c} {v : Charges} {Wt : Income α β γ (H⊕R)}
    {C : Libretto G m} {Bt : Baton G} {Pt : Teller G}
    [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

structure Casting (l : Viewport u X H R ι) (n : q.Run α β γ) (D : Record) (M : Income α β γ (H⊕R)) where
  cast (j : α) : Option (Line l n j D)
  exposes (i : H⊕R) : i∈M.expose ↔ ∃ j J, cast j=some J ∧ J.focus = i

structure Ordered (V : Config G c) (B : Casting l n D Wt) (s : Reading a n) (t : Seats l n) (v : Charges) (r L : ℝ) (o : Site c) (N : ℕ) : Prop where
  realRows (i : β) : i∈Wt.body → ∃ r : RowPosts c f, n.settled i=.inl r
  tours (p : Reel G H R ι) : Needed l r V p → s.Wakes p V → Pose s t V p ∧
    let y := Growth Wt t v o L N (a.imprint V p); let test := d.out.dirBound o (G:=G); let f:=s.turning p
    a.Score p V N test y ∧
    (∀ j, B.cast j=none → Ticket test N V (Wt.gate j) y (f.first j)) ∧
    (∀ j J, B.cast j=some J → ∃ u' : Line.Voices J s p V, u'.Parent Wt t v o L N) ∧
    (∑ j∈Wt.body,f.kept j V ≤ Wt.yen) ∧ (∀ i : β,i∉Wt.body → f.kept i V ≤ Wt.spend i) ∧
      (∀ i : β,Charge test N V y (f.kept i)) ∧ (∀ i : γ,t.tag i=none → Ticket test N V (Wt.wages i) y (f.optional i))

structure Plaid (V : Config G c) (B : Casting l n D Wt) (s : Reading a n) (t : Seats l n) (p : Display G H R ι) : Prop where
  realRows (i : β) : i∈Wt.body → ∃ r : RowPosts c f, n.settled i=.inl r
  first (i) : B.cast i=none → ‖s.ret i V p‖ ≤ Wt.gate i
  color (j J) : B.cast j=some J → ∀ y : Visual u, l.info y=p → ‖J.pitch.actual u.k D J.uses b V y‖ ≤ Wt.gate j
  counts : (∑ i∈Wt.body,s.logs i V p ≤ Wt.yen) ∧ (∀ i : β, i∉Wt.body → s.logs i V p ≤ Wt.spend i) ∧
      (∀ i : γ, t.tag i=none → ‖s.delta i V p‖ ≤ Wt.wages i)

namespace Casting
variable (B : Casting l n D Wt) (h : Sounded Pt C D Bt r d) (hθ : θ ≤ D.ε/32)
include h hθ
omit [DecidableEq γ] [DecidableEq β] [DecidableEq H] [DecidableEq R] [Fintype α] [Fintype γ] [Fintype β] in
lemma earned (ht : u.Clearing V) (p : Display G H R ι) (he : Plaid V B s t p) (hs : s.HeldAt V p) : EarningsAt s Wt t θ V p :=
  ⟨he.realRows,(fun i hi => let ⟨j,J,_,hx⟩ := (B.exposes i).mp hi; hx ▸ J.income h hθ ht hs), fun j => (by
    cases ha : B.cast j
    · exact he.first j ha
    next J => exact J.revenue Wt ht (he.color j J ha)),he.counts⟩
variable (hG : Gliss D d N) {ok : u.ActiveKey → Prop} (hv : ∀ i,ok (l.read i)) (ht : Part ok v d.radius d.tube u.k V d.out N d.broadCut d.g)
    (hT : Studio d.chart r' N L W) (he : Ordered V B s t v r' L o N)
include hG hv ht hT he
omit [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ] in
lemma enroll : Orders s Wt t v θ r' L o V N := by
  refine ⟨he.realRows,fun p hp hW => (he.tours p hp hW).1,fun p hp hW i hi => ?_,fun p hp hW => ?_⟩
  · obtain ⟨j,J,hJ,rfl⟩ := (B.exposes i).1 hi
    obtain ⟨hs,-,-,h',-⟩ := he.tours p hp hW
    obtain ⟨u',hh⟩ := h' j J hJ
    exact u'.demand hs hv ht hT hp h hθ hW
  obtain ⟨hs,hA,hN,h',hh⟩ := he.tours p hp hW
  refine ⟨hA,fun j => ?_,hh⟩
  cases hj : B.cast j
  · exact hN j hj
  next J => obtain ⟨u',hm⟩ := h' j J hj; exact u'.gate Wt hs hv ht hT hp hG hm
omit hθ hv ht hT he hG [Fintype α] [Fintype β] [Fintype γ] [Fintype H] [Fintype R] [DecidableEq β] [DecidableEq γ] [DecidableEq H] [DecidableEq R] in
theorem positioned (hu : u = spectacle d A F κ) (hV : u.Flags V) (hd : d.Valid) (j : α) {J : Line l n j D} (_hi : B.cast j=some J) (y : Visual u) :
    J.pitch.actual u.k D J.uses b V y = ∑ i,page u.k D J.path i b V y := by
  subst u
  refine recoup _ _ b J.eligible ?_ h ?_ y
  · intro l hl; obtain ⟨u',v',w,h',t,hq⟩ := hd.lawful; exact (hq.labels.regular.smooth l).sites
  rw [h.rehearsed.temp_eq]; exact Finset.disjoint_left.mpr fun i hi hh => Finset.disjoint_right.mp J.uses.away hi (Finset.mem_union_right _ (hV.symm ▸ hh))

omit hv ht he hT hG
variable {Q : Booth} {T : Menu} {K : Cafe} {J : Aux} (hs : Sweep J Pt K Q T d) (hθ' : T.θ ≤ D.ε/32)
    (hg : Gliss D d d.out.order) {j : ℕ}
omit hθ
include hθ' hg hs


omit hg

end Casting
end YM.PhysicalNext.JointLoad.Psalm
