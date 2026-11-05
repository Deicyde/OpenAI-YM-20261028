import YM.Bid.Phase

/-!
# Operator bound in a chamber receiving character values

Instead of transporting an operator inequality through the character order, transport a train
estimate. `Ground.X` on the unselected vacuum subspace controls `QRead` in the character chamber:
standing beyond a train costs at most the product of the slab operator norms. A fixed continuous
character eats one more (fixed!) constant which disappears when invoking `OS.producer`, i.e. the
power argument on the word span.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B13
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

theorem answer : YM.Bid.B13 := by
  intro G C S V A P X H _ hs hA _ ho p hr i Z
  classical
  have he (d : ℝ≥0) (w : C.book.Word) : ∃ U : Z.GNS.H.Op, ∀ h : Slab timeAxis d w,
      ‖U‖ ≤ ‖A.place d w‖ ∧ ∀ v, U (Z.GNS.plant v) = Z.GNS.plant (entering h v) := by
    by_cases h : Slab timeAxis d w
    · obtain ⟨U,hU⟩ := actual A H hs ho (hr.reads i) Z (hr.loci i) h
      exact ⟨U,fun _ => hU⟩
    · exact ⟨0,fun hp => (h hp).elim⟩
  choose U hU using he
  let B : Spread Z := ⟨U,fun h => (hU _ _ h).2⟩
  refine ⟨B,fun D R => ?_⟩
  obtain ⟨K,J,hK,hJ⟩ := hA.cap D R
  exact ⟨K,J,hK,fun w d hc hw r hr hb hB =>
    le_trans (show ‖B.place d w‖ ≤ ‖A.place d w‖ from (hU d w hw).1) (hJ w d hc hw r hr hb hB)⟩
end YM.Work.B13
