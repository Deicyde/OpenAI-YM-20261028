import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Enrolled
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Pulse
import YM.Progress.STATIONARY_SCENES.SliceGap

/-! # Stencil/exact-query and projection port needed of the current physical
family for spending the trigger budget. No new raw expansion defined/assigned
here: keep distinct compulsory, optional & tagged μ-addresses at one Spot; do
not rebuild or implicitly re-test the real branch when taking h parents apart.
Use ONE snare marking on this projection before integration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure ProjectorNext.Equivariance Heir AnalyticBridge.LocalGaussian
   Spot Spot.Programme Notice Reading Pitch
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {u : Spot d} {V : Config G c}
    {H R K α β γ : Type} {X : Support c} {l : Viewport u X H R K} {ds : u.Slices} {b : Finset ℕ} {q : Programme ds b} {n : q.Run α β γ} {D : Record} {j : α}
    {B' : Notice l} {s : Reading B' n} {Wt : Income α β γ (H⊕R)}

def packet {I : Type} {Y : Support f} {X₀ : Support c} (a : Museum u.F d.betaHat u.A Y X₀ I) (p : Pitch S I) (b : Finset ℕ) : Programme.AtomID (u:=u) (b:=b) := match p with
  | .fine j => .inl (.inl (.inl j))
  | .noise j => .inl (.inl (.inr (.inl j)))
  | .frame o => .inl (.inl (.inr (.inr (.inl o))))
  | .connector j => .inl (.inl (.inr (.inr (.inr (.inl j)))))
  | .door i => .inl (.inl (.inr (.inr (.inr (.inr (a.seat i))))))
  | .inherit i => .inr (.inr (.inr (.inr (.inr (.inr i)))))
  | .void x => .inl (.inr (.inr x))

def optionalStamp (q : Programme ds b) (s : q.Stamp) : Prop := match s with
  | .heldGate .. => False
  | .billG .. | .billLog .. => True

/-- UPSTREAM eligibility and functional port; tests at known-flag and
POSE-dependent germs (`Voices`) later. The complete physical identification
& locality of all choices of this structure for the actual process is NOT
claimed! Particularly can't expect a seed-free halo around any failed
eligibility test. `kept` is a necessary inclusion, *not* a complete support
for every projection and view of the integrand. Never forget additional
seed, flag, chart or lexical reads in using it. -/
structure Line (l : Viewport u X H R K) (n : q.Run α β γ) (j : α) (D : Record) where
  I : Type
  [unit : Fintype I]
  B : Support f
  Y : Support c
  kept : Y⊆X
  uses : Museum u.F d.betaHat u.A B Y I
  pitch : Pitch S I
  optional : optionalStamp q (n.entry j)
  eligible : pitch.Eligibility uses
  notes : ℕ
  path : pitch.Ordering uses notes
  atNote : Fin notes
  link : I ↪ H ⊕ R
  hear i : l.read (link i)=uses.seat i
  marks : q.atom (n.entry j)=packet uses pitch b
  literal W (y : Visual u) : u.Clearing W → q.visit (n.entry j) W y=page u.k D path atNote b W y
attribute [instance] Line.unit
namespace Line
variable (J : Line l n j D)
def focus : H⊕R := J.link (J.path J.atNote).val
lemma footprint (s : Line l n j D) : s.notes ≤ Fintype.card s.I := s.path.excludes

/-- Exact remaining expression/guard support obligations of ONE marked
trigger parent and all its introduced reads in RAdvances. `U` assigns only
the unread exterior; there are no unspecified hard values INSIDE the reads.
Germs here *use continued* answers; equality at just the allocated point
when no hard default has yet been dropped is NOT enough for this handshake. -/
structure Voices [Fintype H] [Fintype R] (J : Line l n j D) (s : Reading B' n) (p : Reel G H R K) (V : Config G c) where
  remote : Healthy d.out.threshold J.Y V
  U : Config G c → Config G f
  genuine : (s.turning p).first j =ᶠ[𝓝 V] verse u.k D J.path J.atNote b U (scaleRead B' p J.link)

variable {J} [Fintype H] [Fintype R] {p : Reel G H R K} (u' : Voices J s p V)
  {t : Seats l n} {v : Charges} {L r W θ : ℝ} {N m : ℕ} {o : Site c}
    (hs : Pose s t V p) {ok : u.ActiveKey → Prop} (hv : ∀ i,ok (l.read i)) (h : Part ok v d.radius d.tube u.k V d.out N d.broadCut d.g)
    (hT : Studio d.chart r N L W) (hh : Needed l r V p)
    (hG : Gliss D d N) {Pt : Teller G} {Bt : Baton G} {C : Libretto G m} {K' : ℝ} (hc : Sounded Pt C D Bt K' d) (hθ : θ ≤ D.ε/32)

include u' hs hv h hT hh
omit hs hv h hT hh in
include hc in
lemma Voices.identified (ht : J.pitch.Allowed d) {y : Visual u} (he : l.info y=(p.1,B'.imprint V p)) :
    (s.turning p).first j V= page u.k D J.path J.atNote b V y := by
  rw [u'.genuine.eq_of_nhds]
  refine (page_matches u.k J.path J.atNote b u'.U _ J.eligible ht hc u'.remote y ?_).symm
  funext i; change y.2 (J.uses.seat i.1,i.2) = _; rw [← J.hear]; exact congr_fun (congr_arg Prod.snd he) (J.link i.1,i.2)

include hc hθ
omit hs hv h hT hh u' in
lemma stake : bills u θ ≤ height D d := by
  unfold bills height Psalm.cap AnalyticBridge.AnnulusRatioInsertions.Parade.anxious Desk.g
  have ht : 0 ≤ fiery G d.betaHat S.patch.L / coupling d.input.beta := div_nonneg d.paidScale.le hc.heat.le
  rw [hc.rehearsed.fiery_eq]; exact (mul_le_mul_of_nonneg_right hθ ht).trans_eq (by ring)
lemma Voices.demand (hW : s.Wakes p V) : bills u θ ≤ ‖tape (B'.imprint V p) J.focus‖ := by
  refine (stake (u:=u) hc hθ).trans (b:=height D d) ?_
  have he := ((hW (Sum.inl j)).and_eventually u'.genuine).mono (fun W hw => show verse u.k D J.path J.atNote b u'.U (scaleRead B' p J.link) W ≠ 0 from hw.2 ▸ hw.1)
  exact germ_event u.k D J.path J.atNote b u'.U (scaleRead B' p J.link) hc.heat (scale_cont J.link hs hv h hT hh) he

omit hc hθ
variable [Fintype γ] (Wt)
/-- Only the extra Ξ derivative prices earned here; *not* an unstated
bound for whole raw/masked E or tag/gate prerequisites! -/
def Voices.Parent (u' : Voices J s p V) (Wt : Income α β γ (H⊕R)) (t : Seats l n) (v : Charges) (o : Site c) (L : ℝ) (N : ℕ) : Prop :=
    Ticket (d.out.dirBound o) N V (Wt.gate j) (totalBill t v Wt o L N * Moments.powers (B'.imprint V p)^ (max 1 Wt.plan)) (continued u.k D J.uses J.pitch b u'.U (scaleRead B' p J.link))
include hG in
lemma Voices.gate (h' : u'.Parent Wt t v o L N) : Ticket (d.out.dirBound o) N V (Wt.gate j) (Growth Wt t v o L N (B'.imprint V p)) ((s.turning p).first j) :=
    (peeled_jet J.link hs hv h hT hh hG (J.path.toEmbedding.trans (Embedding.subtype _)) J.atNote (show Voices.Parent .. from h')).agree u'.genuine.symm

omit u' hs hv h hT hh
variable (J)
omit [Fintype H] [Fintype R] [Fintype γ] in
lemma page_value (s : Reading B' n) (ht : u.Clearing V) (y : Visual u) : s.ret j V (l.info y)=page u.k D J.path J.atNote b V y :=
    (s.retReached j V y ht).trans (J.literal _ _ ht)

variable [Fintype α] [Fintype β]
variable {Q : Display G H R K}
include hc hθ in
omit [Fintype γ] [Fintype β] [Fintype α] in
theorem income (ht : u.Clearing V) (hQ : s.HeldAt V Q) : bills u θ ≤ ‖tape Q.2 J.focus‖ := by
  obtain ⟨y,rfl⟩ := l.full Q
  have hp := hQ.1 j; rw [J.page_value s ht] at hp
  apply (stake (u:=u) hc hθ).trans (b:=height D d); have hh := page_event u.k D J.path J.atNote b hc.heat hp; rw [← J.hear] at hh
  exact hh

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype H] [Fintype R] in
lemma revenue (ht : u.Clearing V) (hp : ∀ y : Visual u, l.info y=Q → ‖actual u.k D J.uses J.pitch b V y‖ ≤ Wt.gate j) : ‖s.ret j V Q‖ ≤ Wt.gate j := by
  obtain ⟨y,he⟩ := l.full Q; rw [← he,J.page_value s ht,page,norm_mul]; obtain ⟨h1,h2⟩ := peel_price D J.path J.atNote (gaussRead u.k J.uses y)
  rw [Real.norm_of_nonneg h1]; exact (mul_le_of_le_one_left (norm_nonneg _) h2).trans (hp y he)

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma latch {A : Stores S} {F : Forest S.ratio} {k : S.Choices} (hz : u=spectacle d A F k) (hV : u.Clearing V) (hd : 0<d.radius) (hQ : s.ret j V Q≠0) (ht : ∀ i,J.pitch ≠ .door i)
    (i : H) (j : J.I) (hi : J.link j=Sum.inl i) (hj : j∈J.pitch.carriers J.uses) : ‖B'.bought V Q i‖ < 4*d.radius := by
  subst u; obtain ⟨y,rfl⟩ := l.full Q
  rw [J.page_value _ hV] at hQ
  have hh := page_protected _ _ _ _ _ hd ht hQ j hj; unfold actualRead at hh
  rw [show J.uses.seat j=l.read (.inl i) from (hi ▸ J.hear j).symm] at hh
  rw [show B'.bought V (l.info y) i=B'.powder V (l.info y) (.inl i) from rfl,B'.powder_arranged V hV y (.inl i)]
  exact hh
end Line
end YM.PhysicalNext.JointLoad.Psalm
