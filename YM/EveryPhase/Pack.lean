import YM.Work.B02
import YM.Work.B14
import YM.EveryPhase.Compatibility

/-!
# Operator bound in a chamber receiving character values

Reuse the B13 train estimate (below through `actual` from YM.Work.B13, private there). Instead of transporting an operator inequality through the character order, transport a train
estimate. `Ground.X` on the unselected vacuum subspace controls `QRead` in the character chamber:
standing beyond a train costs at most the product of the slab operator norms. A fixed continuous
character eats one more (fixed!) constant which disappears when invoking `OS.producer`, i.e. the
power argument on the word span.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function OS OS.Ground Word
open scoped Topology NNReal

variable {G : Gauge} {C : Family G} {S T : Table C.book} {V : Chamber S timeAxis}
    (A : Spread V) {P : A.Resolution} {i : P.X}
    {d : ℝ≥0} {w : C.book.Word}

private lemma x_enter (h : Slab timeAxis d w) (v : Future C.book timeAxis) :
    Ground.X A (entering h v) = (A.place d w).comp (Ground.X A v) := by
  obtain ⟨e,he⟩ := Ground.future_reach v
  rw [standing A (entering h v) (connects h he), standing A v he]
  change (A.place (d+e) (linked timeAxis d w v.val)).comp _ = _
  rw [A.concatenate h he]
  rfl

private lemma x_train (H : S.Hierarchy) (h : Slab timeAxis d w) (D : ℝ) (hb : ‖A.place d w‖ ≤ D)
    (v : Future C.book timeAxis) (n : ℕ) : ‖Ground.X A (ride h v n)‖ ≤ ‖Ground.X A v‖ * D^(2*n) := by
  have hd : 0 ≤ D := le_trans (norm_nonneg _) hb
  induction n with
  | zero => rw [show ride h v 0=v from rfl]; simp
  | succ n ih =>
    let u := A.place d w
    let q := Ground.X A (ride h v n)
    have he : ride h v (n+1) = entering (mirrorsSlab h) (entering h (ride h v n)) := by
      simp [ride,iterate_succ_apply']
    rw [he,x_enter A (mirrorsSlab h), x_enter A h, ← A.adjoints h H.translations]
    change ‖(u.adjoint.comp u).comp q‖ ≤ _
    change ‖q‖ ≤ _ at ih
    change ‖u‖ ≤ D at hb
    calc
      _ ≤ ‖u.adjoint.comp u‖ * ‖q‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = (‖u‖ * ‖u‖) * ‖q‖ := by rw [ContinuousLinearMap.norm_adjoint_comp_self]
      _ ≤ (D*D)*(‖Ground.X A v‖ * D^(2*n)) := by gcongr
      _ = _ := by rw [Nat.mul_add, pow_add]; ring

/-- Diagonal train estimate suffices (in a chamber of a Hierarchy). -/
private lemma buys (H : S.Hierarchy) (hs : Steady V) (ho : P.Out) (hr : P.receives T i)
    (h : Slab timeAxis d w) (D : ℝ) (hb : ‖A.place d w‖ ≤ D) : QRead T D h := by
  have hd : 0 ≤ D := le_trans (norm_nonneg _) hb
  haveI : IsClosed (A.algebra : Set V.VacuumOp) := isClosed_closure
  letI : CStarAlgebra A.algebra := StarSubalgebra.cstarAlgebra A.algebra
  let f : A.algebra →L[ℂ] ℂ := { (P.character i).toAlgHom.toLinearMap with cont := ho.values i }
  have he (v : Future C.book timeAxis) : ‖T.gram timeAxis v.val v.val‖ ≤
      ‖f‖ * (‖Ground.X A v‖ * ‖Ground.X A v‖) := by
    let p := M A _ (twoSides v.property v.property)
    have hp : f p=T.gram timeAxis v.val v.val :=
      Extraction.Retain.pops A P hr _ (twoSides v.property v.property)
    rw [← hp]
    apply (f.le_opNorm p).trans_eq
    change ‖f‖ * ‖p.val‖ = _
    rw [show p.val = _ from slim A H hs v v, ContinuousLinearMap.norm_adjoint_comp_self]
  intro v
  refine ⟨‖f‖ * (‖Ground.X A v‖ * ‖Ground.X A v‖),fun n => ?_⟩
  apply (he (ride h v n)).trans
  have hx := x_train A H h D hb v n
  calc
    _ ≤ ‖f‖*((‖Ground.X A v‖ * D^(2*n))*(‖Ground.X A v‖ * D^(2*n))) := by gcongr
    _ = _ := by rw [show 4*n=2*n+2*n by omega, pow_add]; ring

private lemma actual (H : S.Hierarchy) (hs : Steady V) (ho : P.Out) (hr : P.receives T i)
    (Z : Chamber T timeAxis) (ht : T.Hierarchy) (h : Slab timeAxis d w) :
    ∃ U : Z.GNS.H.Op, ‖U‖ ≤ ‖A.place d w‖ ∧
      ∀ v, U (Z.GNS.plant v) = Z.GNS.plant (entering h v) := by
  let c := ‖A.place d w‖
  have hc : 0 ≤ c := norm_nonneg _
  have he (D : ℝ) (hd : c < D) := OS.producer Z h ht (buys A H hs ho hr h D hd.le) (hc.trans_lt hd)
  obtain ⟨U,-,hU⟩ := he (c+1) (by linarith)
  refine ⟨U,?_,hU⟩
  change ‖U‖ ≤ c
  by_contra! hn
  obtain ⟨D,hD,hD'⟩ := exists_between hn
  obtain ⟨U',hp,hp'⟩ := he D hD
  have hu : U'=U := Z.GNS.by_bud fun i => (hp' i).trans (hU i).symm
  rw [hu] at hp
  exact hD'.not_ge hp


/-- The unselected multiplet bounds themselves work, uniformly for every character. -/
lemma sameBound (H : S.Hierarchy) (hs : Steady V) (ho : P.Out) (hr : P.receives T i)
    (ht : T.Hierarchy) (Z : Chamber T timeAxis) (B : Spread Z) (h : Slab timeAxis d w) :
    ‖B.place d w‖ ≤ ‖A.place d w‖ := by
  obtain ⟨U,hU,hV⟩ := actual A H hs ho hr Z ht h
  have he : B.place d w=U := Z.GNS.by_bud (fun k => (B.reads h k).trans (hV k).symm)
  rw [he]; exact hU

open Next.BOUNDARY
open MeasureTheory Set Filter Spec Boundary Org
open scoped ContDiff

variable {f : Extraction.Order} (F : Final C f S)

/-- Book of contours and reflection constructions, indexed by characters of
precisely the compression algebra in Final. No exceptional set deletion; on
all of it we can use the existing Wightman construction through `FieldCore`
(which requires all of Realizes except vacuum uniqueness). Used below when
vacuum uniqueness isn't known yet.

Even choose the *same* spaces, contour, and fields as the old construction
at its selected point, so U at that point connects those actual two spaces.
All operators refer to S.Union. -/
structure Almanac where
  chambers (i : F.α.space.X) : Chamber (F.α.ensemble i) timeAxis
  spreads (i : F.α.space.X) : Spread (chambers i)
  pantries (i : F.α.space.X) : Bid.Pantry S _ _ F.sector.derivatives (spreads i)
  contours (i : F.α.space.X) : Contour S
  cards (i : F.α.space.X) : Compatible S (spreads i) F.sector F.action.spin F.room.kernel.spin (contours i)
  actors : F.α.space.X → Wightman S
  letters (i : F.α.space.X) : (actors i).J=F.action.J
  spins (i : F.α.space.X) : (actors i).spin=F.action.spin
  cores (i : F.α.space.X) : FieldCore (contours i).world F.sector.turns F.room.kernel.spin (actors i)
  J (i : F.α.space.X) : (actors i).operators.H →L[ℂ] (chambers i).H
  links (i : F.α.space.X) : Attachment (actors i) (chambers i) (J i)
  baseC : chambers F.α.atPoint=F.α.leaps
  baseS : HEq (spreads F.α.atPoint) F.α.slabs
  baseB : contours F.α.atPoint=F.A
  baseR : actors F.α.atPoint=F.action

lemma storeys (i : F.α.space.X) (M : Chamber (F.α.ensemble i) timeAxis) :
    ∃ B : Spread M, Spread.Laws B F.sector.derivatives := by
  classical
  let T := F.α.ensemble i
  have he (d : ℝ≥0) (w : C.book.Word) : ∃ U : M.H.Op, ∀ h : Slab timeAxis d w,
      ∀ v, U (M.GNS.plant v)=M.GNS.plant (entering h v) := by
    by_cases h : Slab timeAxis d w
    · obtain ⟨U, -, hU⟩ := actual F.α.unselected F.room.kernel F.phase.phase.still
        F.phase.phase.decomposition (F.phase.phase.chosen i) M (F.phase.phase.states i) h
      exact ⟨U, fun _ => hU⟩
    exact ⟨0,fun hp => (h hp).elim⟩
  choose U hU using he
  let B : Spread M := ⟨U, fun h => hU _ _ h⟩
  have hp := F.phase.phase.states i
  have hw : B.AllCopy := by
    intro D R
    obtain ⟨K,Q,hK,hQ⟩ := F.phase.phase.lengths.cap D R
    exact ⟨K,Q,hK,fun w d hc hx r hr hb hB => (sameBound F.α.unselected
      F.room.kernel F.phase.phase.still F.phase.phase.decomposition (F.phase.phase.chosen _)
      hp _ B hx).trans (hQ w d hc hx r hr hb hB)⟩
  exact ⟨B,Work.B02.answer S T _ M B F.room.kernel hp (fun d => (F.phase.phase.retains i d).symm.le)
    F.room.kernel.laws.toSymmetric hp.laws.toSymmetric (F.phase.phase.calculus i) hw⟩

lemma almanac : Nonempty (Almanac F) := by
  classical
  have hg := F.phase
  choose M he using (show ∀ i, ∃ M : Chamber (F.α.ensemble i) timeAxis, i=F.α.atPoint → HEq M F.α.leaps from by
    intro i; by_cases h : i=F.α.atPoint
    · subst i; exact ⟨_, fun _ => HEq.rfl⟩
    obtain ⟨M⟩ := OS.realization (hg.phase.states i) timeAxis
    exact ⟨M,fun hp => (h hp).elim⟩)
  have ht := eq_of_heq (he F.α.atPoint rfl)
  choose B hB hY using (show ∀ i, ∃ B : Spread (M i), Spread.Laws B F.sector.derivatives ∧ (i=F.α.atPoint → HEq B F.α.slabs) from by
    intro i; by_cases h : i=F.α.atPoint
    · subst i; rw [ht]
      exact ⟨_, hg.phase.goes, fun _ => HEq.rfl⟩
    obtain ⟨B,hB⟩ := storeys F i (M i)
    exact ⟨B,hB,fun hp => (h hp).elim⟩)
  have hp (i) : Bid.Pantry S _ _ _ (B i) :=
    ⟨F.room.kernel, hg.phase.states i, fun d => (hg.phase.retains i d).symm.le, hg.transport.injection,
      hg.phase.coordinates i, hg.phase.calculus i, hB i⟩
  have hv := F.realization.qt
  choose Y hA hF using (show ∀ i, ∃ Y : Contour S,
      Y.From (F.α.ensemble i) ∧ (i=F.α.atPoint → Y=F.A) from by
    intro i; by_cases h : i=F.α.atPoint
    · subst i; exact ⟨_,F.realization.chosen, fun _ => rfl⟩
    obtain ⟨A,hA⟩ := contour (hp i)
    exact ⟨A,hA, fun hp => (h hp).elim⟩)
  have hh (i) : Compatible S (B i) F.sector F.action.spin F.room.kernel.spin (Y i) :=
    compatible (hp i) hg.transport.rights (hg.phase.sym i) hg.transport.spots hv.letters
      (hg.phase.retains i) (hA i)
  choose R hr hm hu hl using (show ∀ i : F.α.space.X, ∃ R : Wightman S, R.J=F.action.J ∧ R.spin=F.action.spin ∧
    FieldCore (Y i).world F.sector.turns F.room.kernel.spin R ∧ (i=F.α.atPoint → R=F.action) from by
    intro i; by_cases h : i=F.α.atPoint
    · subst i; rw [hF F.α.atPoint rfl]
      exact ⟨_, rfl,rfl,FieldCore.of_realizes hv,fun _ => rfl⟩
    obtain ⟨r,h₁,h₂⟩ := (hh i).reveals
    obtain ⟨R,hr,hK,hR⟩ := establishing (hp i) hv.letters hv.induced (h₂ _ hv.induced).1
    exact ⟨R,hr,hK,hR,fun hp => (h hp).elim⟩)
  choose U hU using (fun i => ((hh i).attachments (R i) (hu i)).2.exists)
  exact ⟨M,B,hp,Y,hh,R,hr,hm,hu,U,hU,ht,hY _ rfl,hF _ rfl,hl _ rfl⟩

lemma Almanac.priced {F : Final C f S} (L : Almanac F) (i : F.α.space.X) (h : ℝ≥0) : ∀ (u : C.book.Word), Slab timeAxis h u →
    ‖(L.spreads i).place h u‖ ≤ ‖F.α.unselected.place h u‖ := fun _ hu =>
  sameBound F.α.unselected F.room.kernel F.phase.phase.still F.phase.phase.decomposition
    (F.phase.phase.chosen _) (F.phase.phase.states _) _ _ hu

/-- records the uniform-in-character arbitrary-copy bounds explicitly. -/
lemma Almanac.copy {F : Final C f S} (L : Almanac F) (D : ℕ) (R : ℝ) : ∃ C₀ : ℝ, ∃ Q : ℕ, 0 < C₀ ∧
    ∀ i, ∀ (w : C.book.Word) (d : ℝ≥0), constrained D R w → Slab timeAxis d w → ∀ r : ℝ,
    0 < r → r ≤ 1 → buffer timeAxis r d w → ‖(L.spreads i).place d w‖ ≤ Spread.radius C₀ Q w r := by
  obtain ⟨C₀,Q,hC,hQ⟩ := F.phase.phase.lengths.cap D R
  exact ⟨C₀,Q,hC, fun i w d hh ht r hr h hr' => (L.priced i d w ht).trans (hQ w d hh ht r hr h hr')⟩

lemma Almanac.almostEvery {F : Final C f S} (L : Almanac F) : ∀ᵐ i ∂F.α.space.μ, (L.chambers i).UniqueHeat := by
  obtain ⟨R,hR⟩ := Work.B14.universal C.book timeAxis
  let V := F.phase.phase
  exact Cluster.lifts _ R (fun i => hR _ (V.states i).laws.toSymmetric (V.states i).smooth _) F.room.kernel
    V.still V.states V.decomposition V.chosen

end YM.EveryPhase
