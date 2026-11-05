import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Assignment
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Outer

/-!
# The extra annulus bill on *one* sector packet or remote row

Do not use the literal core gain after occurring complements without
its local prerequisites. Pay on Coat, on the *one product* of all
turns, extended compared to Seeded (can use also in assembled words
that dropped defaults). V flags read through true distances. Value-only;
no differentiating clips/good regions. Include pre-Gaussian mean-square
subtractions (D rows at actual X on each channel, shell values already
pinned by Y). Prerequisites hold both in and out of original integral
after labeled unmasking.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows  Tags Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

section check
variable (X : Coat T F)

lemma frozen_positive (b : Cell f) (s : Signed) (u : Directions G f) : 0 ≤ yielding T X.x (pull s 0 (X.input u))
    (pull s 0 X.V) (choice s X.k) (.inl b) := add_nonneg (mul_nonneg T.high.quadratic_pos.le (flaw_nonneg _))
    (sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by norm_num))

lemma noise_positive (b : Bond c) (s : Signed) (u : Directions G f) : 0 ≤ yielding T X.x (pull s 0 (X.input u))
    (pull s 0 X.V) (choice s X.k) (.inr (.inl b)) := by
  let V := pull s 0 X.V; let U := pull s 0 (X.input u); let k:=choice s X.k
  change 0 ≤ T.workI (till X.x) (S.prediction U k) V (Pressure.temp X.x) b; rw [splitI]
  exact add_nonneg (mul_nonneg S.kernel.penalty_pos.le (flaw_nonneg _)) (div_nonneg (sq_nonneg _) (by norm_num))

lemma reply_spotF (s : Signed) (b : Cell f) (hs : X.selected s (.inl b)) (u : Directions G f) :
    X.extracted u s (.inl b)=∑ i : Bool, ‖X.realPath s (.inl (b,i)) u‖^2/2 := by
  unfold Coat.extracted parents
  simp [Finset.sum_insert,surcharge,spot,hs]
lemma reply_spotI (s : Signed) (b : Bond c) (hs : X.selected s (.inr (.inl b))) (u : Directions G f) :
    X.extracted u s (.inr (.inl b))=‖X.realPath s (.inr b) u‖^2/2 := by
  simp [Coat.extracted,parents,surcharge,spot,hs]

/-- Relative extension agrees with old drows outside core of the wide
charge, includes true threshold and kept selectors on the same mask.
Keep Width physical even for A containing only V flags. -/
lemma turn_debit (r : Room P S T X.x) {A : Stores S} (s : Signed) (u : Directions G f) (p : Spot c f)
    {W : ℝ} (hW : Tags.Wide A (300*X.B) (X.input u) X.k X.V X.x W) :
    let i:=X.addr s p
    Inside i A (200*X.B) → ¬ Inside i A (2*X.B) → X.debit u s p=X.light u s p := by
  intro i hi hk
  rcases p with b|b
  swap; · rfl
  let V := pull s 0 X.V
  let Y := pull s 0 (X.input u)
  let k := choice s X.k; let C := turnStore s A; let x := S.ratio.parent b.1
  have hr := hW.rotate s (SectorMeasure.funds_branch r.accepted)
  have hb : Interior S X.x W x X.B Y k V := by
    refine Interior.from_wide Y V k x hr (a:=200*X.B) ((rotates_dome ..).mpr hi) (by omega) ?_
    intro hh
    apply hk; refine Lattice.Corona.halo_mono (show X.B ≤ 2*X.B by omega) (Finset.Subset.refl _) ((rotates_dome ..).mp hh)
  let t := X.t
  have he : 0 ≤ t := r.fiery.le
  have hf : toll Y b ≤ t := (hb.fine b (show separation x x≤_ by simp)).trans (by linarith)
  have hh : PathData.kept T.high X.t b.1 Y := by
    intro p; by_cases hx : X.t*Real.exp (separation b.1 p.1 / T.high.relaxation) < 2
    · have h₂ := r.laneU _ hx
      have hu := hb.fine p ((Work.E04.parent_separation S.ratio b.1 p.1).trans (show separation b.1 p.1+1 ≤ X.B by
        unfold Coat.B; omega))
      have ht : t/2 ≤ t := by linarith
      apply (hu.trans ht).trans
      exact le_mul_of_one_le_right he (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) T.high.radius_pos.le))
    exact (G.chord_le_two _).trans (le_of_not_gt hx)
  unfold debit light; rw [show X.energy u s (.inl b)=T.workF X.R Y V t (Pressure.temp X.x) b from rfl]
  exact congr_arg (· - _) (splitF T X.x Y V k b hf hh)

/-- Strong use in a packet: selection may require any hot indexes at
coordinates from throughout the annulus. Guard factors through those
radii stay on. -/
def Controlled (d : ℕ) (A : Stores S) (u : Directions G f) (ζ : ℝ) := ∀ i : Bond f,
    atEdge S i∈A.dome d → X.Hot i → ‖u i‖ ≤ ζ

theorem fosters {A : Stores S} {W M γ : ℝ} (H : ShellAccess S G X.x W X.width γ) (s : Signed) (p : Spot c f)
    (u : Directions G f) (i:=X.addr s p) (_hp : i = X.addr s p) (hi : Inside i A (200*X.B))
    (he : ¬Inside i A (2*X.B)) (ht : Tags.Wide A (300*X.B) (X.input u) X.k X.V X.x W)
    (hc : Controlled X (304*X.B) A u M) (hg : γ*(2*(X.width*X.t)) ≤ M) :
    Grafted X.V (X.input u) (X.signal u) i X.B M S := by
  apply X.required u H _ _ hg
  · intro b hb; unfold distAt at hb
    exact Interior.from_wide _ _ _ _ ht (a:=201*X.B)
      (touch_extend hi (by omega)) (by omega) (clear he (by omega))
  exact fun b hb => hc b (touch_extend hi (by unfold distAt at hb; omega))
end check

/-- Bundle all *weak unmasked* estimates. Can be used at each
stencil independently of global U. H footprints for outer eligibility
purchased only beyond requiring Grafted on the realized U. For unselected F/I
assert ONE-SIDED bound. Out of the compulsory packets we'll request
selected, so retain two-sided price there too. -/
theorem light_costs (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (A : ℝ) (hA : 0<A)
    {w : ℝ → ℝ} (h : Rate G L (-(1/2)) w) (hp : ∀ᶠ x in atTop, 0 ≤ w x) :
    ∃ E : ℝ → ℝ, Rate G L (-(3/2)) E ∧ ∀ᶠ x in atTop,
    0 ≤ E x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Room P S T x → ∀ (u : Directions G f)
      (p : Spot c f) (s : Signed), Clean X.V X.x (X.addr s p) X.B →
      Grafted X.V (X.input u) (X.signal u) (X.addr s p) X.B (w x) S →
      Bid.Maximum A T x (pull s 0 X.V) →
        (-E x ≤ X.light u s p ∧ (X.selected s p → |X.light u s p| ≤ E x)) := by
  obtain ⟨E₁,H₁,h1⟩ := soft_bills P L D hd A hA h hp
  obtain ⟨E₂,H₂,h2⟩ := letters_N P L
  obtain ⟨E₃,H₃,h3⟩ := letters_C P L
  obtain ⟨E₄,H₄,h4⟩ := letters_LD P L D hd A hA h hp
  let E x := E₁ x + E₂ x + E₃ x + E₄ x
  refine ⟨E,((H₁.add (H₂.weaken (by norm_num))).add (H₃.weaken (by norm_num))).add H₄,?_⟩
  filter_upwards [h1,h2,h3,h4] with x hb hN hC hv
  have h₁ := hb.1; have h₂ := hN.1; have h₃ := hC.1; have h₄ := hv.1
  have hE : 0 ≤ E x := by unfold E; linarith
  refine ⟨hE,?_⟩
  intro c f S T F X hx hS hL hR u p s hW hU hm
  subst x
  let i := lead S p; let V := pull s 0 X.V
  let k := choice s X.k; let U := pull s 0 (X.input u); let v := displacement s (X.signal u) (replica S.ratio X.V)
  have hi : Clean V X.x i X.B := hW.turn
  have hP : 100 ≤ X.B := hR.sight.1
  have hu : Grafted V U v i (X.B/2) (w X.x) S := (hU.less (i:=X.addr s p) (d:=X.B/2+1)
    (by rw [separation_self, zero_add]; omega)).in_channel ..
  have hs := hb.2 c f S T hS hL hR U k V i v hm hi hu
  let r := E X.x
  have ho : E₁ X.x≤r := by unfold r E; linarith
  have hg (q : Spot c f) (he : |X.light u s q| ≤ r) : -r ≤ X.light u s q ∧
      (X.selected s q → |X.light u s q|≤r) := ⟨neg_le_of_abs_le he,fun _ => he⟩
  rcases p with p|p|(p | p)
  · by_cases hh : X.selected s (.inl p)
    · apply hg
      rw [light,X.reply_spotF s p hh u]
      exact ((hs.1 p rfl)).trans ho
    refine ⟨?_,fun hp => False.elim (hh hp)⟩
    rw [light,X.uncaptured u s _ hh,sub_zero]
    exact (neg_nonpos.mpr hE).trans (X.frozen_positive ..)
  · by_cases hh : X.selected s (.inr (.inl p))
    · apply hg
      rw [light,X.reply_spotI s p hh u, yielding]; dsimp only [Sum.elim]
      rw [show principal T X.x U V (S.prediction U k) (.inr (.inl p))=softI T X.x U V k p from splitI T X.x U V k p]
      exact ((hs.2 p rfl)).trans ho
    refine ⟨?_,fun hp => False.elim (hh hp)⟩
    rw [light,X.uncaptured u s _ hh, sub_zero]
    exact (neg_nonpos.mpr hE).trans (X.noise_positive ..)
  · apply hg
    rw [light]; unfold Coat.extracted; simp [parents]
    have hx := hC.2 c f S T hL hR V p (hi.toll (b:=p) (by change separation i i≤_; simp))
    have hh := hv.2 c f S T hL hS hR U V p k hm hi v hu
    change |T.workC X.R V (Pressure.temp X.x) p + (_ + _)| ≤ _
    exact ((abs_add_le ..).trans (add_le_add hx ((abs_add_le ..).trans hh))).trans (by unfold r E; linarith)
  · apply hg
    rw [light]; unfold Coat.extracted; simp [parents]
    exact (hN.2 c f S T hL hR V p (hi.shrink (by change separation i i + (X.B/4+1)≤_; simp only [separation_self]; omega))).trans
      (by unfold r E; linarith)

/-- Packed actual remainders in the annulus `H200 \\ H2`. These are BEFORE
any pricing of determinant or Gaussian correction. -/
theorem annulus (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (A : ℝ) (hA : 0<A)
    {w : ℝ → ℝ} (h : Rate G L (-(1/2)) w) (hp : ∀ᶠ x in atTop, 0 ≤ w x) :
    ∃ E : ℝ → ℝ, Rate G L (-(3/2)) E ∧ ∀ᶠ x in atTop,
    0 ≤ E x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → S.patch=D → S.patch.L=L → Room P S T x →
      ∀ (Z : Stores S) (u : Directions G f) (p : Spot c f) (s : Signed) (W γ : ℝ),
      Bid.Maximum A T x (pull s 0 X.V) → ShellAccess S G X.x W X.width γ →
      γ*(2*(X.width*X.t)) ≤ w x → Controlled X (304*X.B) Z u (w x) →
      Tags.Wide Z (300*X.B) (X.input u) X.k X.V X.x W →
      Inside (X.addr s p) Z (200*X.B) → ¬ Inside (X.addr s p) Z (2*X.B) →
        -E x ≤ X.debit u s p := by
  obtain ⟨E,e,H⟩ := light_costs P L D hd A hA h hp
  refine ⟨E,e,H.mono ?_⟩
  intro x h
  refine ⟨h.1,?_⟩
  intro c f S T F X hx hS hL hR Z u p s W γ hm hr hg hu hc hi hf
  subst x
  have hp : Clean X.V X.x (X.addr s p) X.B :=
    clean_halo Z hc (clear hf (by rw [separation_self]; omega)) hi (by omega)
  have hb := X.fosters hr s p u (X.addr s p) rfl hi hf hc hu hg
  rw [X.turn_debit hR s u p hc hi hf]
  exact (h.2 c f S T F X rfl hS hL hR u p s hp hb hm).1
end YM.ConnectedActivityE6.Coat
