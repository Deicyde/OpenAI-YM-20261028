import YM.Bid.Grow

/-!
# C28: from simultaneous covariance on absolute joint tests to word motion

Labels in the continuity argument are pinned *before* evaluating W. We use a
fixed finite basis expansion against fixed distributions, not continuity in
any colimit topology on Union or joint-continuity of a dual pairing.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.C28
open Function Boundary Mink Mink.Poincare
open scoped Topology BigOperators

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

/-- Read a sentence presented on fixed absolute slots. -/
lemma expect_ofFn (W : Surface S) (w : Fin n → Letter S) :
    W.expect (List.ofFn w) = W.W n (fun i => (w i).1) (Joint.materialize n (fun i => (w i).2)) := by
  unfold Surface.expect
  simp_rw [List.get_ofFn]
  -- only changes of arity along length_ofFn
  have aux (m : ℕ) (h : m = n) : W.W m (fun i => (w (Fin.cast h i)).1)
      (Joint.materialize m (fun i => (w (Fin.cast h i)).2)) = W.W n (fun i => (w i).1)
      (Joint.materialize n (fun i => (w i).2)) := by subst m; rfl
  exact aux _ List.length_ofFn

/-- The arity-one C08 orbit, in Test4 coordinates. -/
lemma continuous_push (H : Bid.C08) (f : Test4) :
    Continuous (fun p : Poincare => Joint.push p f) := by
  let E : Points 1 ≃L[ℝ] E4 := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => E4)
  have he (x : Points 1) : E x = x default := rfl
  let F := Probe.along E f
  have ht : (fun p : Poincare => Joint.push p f) = fun p => Probe.along E.symm (Joint.gpush 1 p F) := by
    funext p
    ext1 x
    rw [Joint.push_at, Probe.along_at, Joint.gpush_at]
    change _ = f (E _)
    rw [he, zusammen, points_apply, ← he, ContinuousLinearEquiv.apply_symm_apply]
  rw [ht]
  exact (Probe.along E.symm).continuous.comp (H.1 _ _)

/-- A moving finite set of pinned labels, tested on a simultaneously moving joint test. -/
lemma continuous_pinned {X : Type*} [TopologicalSpace X] (W : Surface S) (d : ℕ)
    (v : X → Fin n → S.Field d) (f : X → Joint n) (hv : ∀ i, Continuous (fun x => v x i)) (hf : Continuous f) :
    Continuous (fun x => W.W n (fun i => S.pin d (v x i)) (f x)) := by
  let B := Module.finBasis ℂ (S.Field d)
  let T : MultilinearMap ℂ (fun _ : Fin n => S.Field d) (Distn (Points n)) :=
    (W.W n).compLinearMap (fun _ => S.pin d)
  change Continuous (fun x => T (v x) (f x))
  let b (k : Fin n → Fin (Module.finrank ℂ (S.Field d))) (i : Fin n) := B (k i)
  let c (k : Fin n → Fin (Module.finrank ℂ (S.Field d))) (x : X) := ∏ i, B.repr (v x i) (k i)
  -- expand over *all* basis tuples (even if a coefficient crosses zero)
  have he (x : X) : T (v x) = ∑ k, c k x • T (b k) := by
    have hx : v x = fun i => ∑ j, B.repr (v x i) j • B j :=
      funext fun i => (B.sum_repr _).symm
    conv_lhs => rw [hx]
    rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun k _ => T.map_smul_univ (fun i => B.repr (v x i) (k i)) (b k)
  simp_rw [he, sum_apply, smul_apply]
  refine continuous_finsetSum _ fun k _ => (show Continuous (c k) from ?_).smul ((T (b k)).continuous.comp hf)
  exact continuous_finsetProd _ (fun i _ => ((B.coord (k i)).continuous_of_finiteDimensional.comp (hv i)))

/-- Even per-letter continuous motion gives a continuous scalar. -/
lemma continuous_reads {X : Type*} [TopologicalSpace X] (H : Bid.C08)
    (W : Surface S) {K : Spins S} {P : DiffPlan S} (hs : S.Symmetric) (hp : P.Inclusions S)
    {R h} (hk : K.Descends R h) (w : Fin n → Letter S)
    (g : Fin n → X → Poincare) (hg : ∀ i, Continuous (g i)) :
    Continuous fun x => W.expect (List.ofFn (fun i => Letter.read K (g i x) (w i))) := by
  obtain ⟨d, v, hv⟩ := P.joint hs hp (fun i => (w i).1)
  have he (i : Fin n) : (w i).1 = S.pin d (v i) := congr_fun hv i
  simp_rw [expect_ofFn, Letter.read, he, hk.ties]
  refine continuous_pinned W d (fun x i => K.shell d (g i x).Λ (v i)) _
    (fun i => (hk.spin _ _).comp (continuousL.comp (hg i))) ?_
  exact (Joint.jointCont n).comp (show Continuous (fun x => fun i => Joint.push (g i x) (w i).2) from
    continuous_pi (fun i => (continuous_push H _).comp (hg i)))

lemma po_ofFn_get (K : Spins S) (p : Poincare) (w : Sentence S) :
    K.po p w = List.ofFn (Letter.read K p ∘ w.get) := by
  rw [← List.map_ofFn, List.ofFn_get]
  rfl

lemma strong (H : Bid.C08) (W : Surface S) (J : StarOp S) {P : DiffPlan S}
    (hs : S.Symmetric) (hp : P.Inclusions S) {R h} {K : Spins S} (hk : K.Descends R h) :
    W.Strong J K := by
  intro i j
  let l := Sentence.rev J i
  let w := Fin.append l.get j.get
  let g : Fin (l.length+j.length) → Poincare → Poincare := Fin.append (fun _ : Fin l.length => fun _ => 1)
    (fun _ : Fin j.length => id)
  have hg (a) : Continuous (g a) := by
    refine Fin.addCases ?_ ?_ a
    · intro a; simp only [g, Fin.append_left]; exact continuous_const
    intro a; simp only [g, Fin.append_right]; exact continuous_id
  have hwords (p) : l ++ K.po p j = List.ofFn (fun a => Letter.read K (g a p) (w a)) := by
    rw [show (fun a => Letter.read K (g a p) (w a)) = Fin.append l.get (Letter.read K p ∘ j.get) from ?_,
      List.ofFn_fin_append, List.ofFn_get, po_ofFn_get]
    funext a; refine Fin.addCases ?_ ?_ a
    · intro a
      simp only [g, w, Fin.append_left]
      exact Letter.stays_read K _ hk
    intro a; simp only [g, w, Fin.append_right]; rfl
  change Continuous fun p => W.expect (l ++ K.po p j)
  simp_rw [hwords]
  exact continuous_reads H W hs hp hk w g hg

/-- Composition order matters: rotate then translate in the pushed test. -/
lemma gpush_split (p : Poincare) (f : Joint n) :
    Joint.gpush n p f = Joint.gpush n (translation p.b) (Probe.along (togetherL p.Λ n).symm f) := by
  ext1 x
  rw [Joint.gpush_at, Joint.gpush_at, Probe.along_at]
  congr 1
  ext1 i
  simp [zusammen, translation]

lemma expect_po (W : Surface S) {K : Spins S} (hu : Urs W K) (w : Sentence S) (p : Poincare) :
    W.expect (K.po p w) = W.expect w := by
  rw [po_ofFn_get, expect_ofFn]
  let v := fun i => (w.get i).1
  let f := fun i => (w.get i).2
  change W.W w.length (fun i => K.rail p.Λ (v i)) (Joint.materialize _ (fun i => Joint.push p (f i))) =
    W.W w.length v (Joint.materialize _ f)
  rw [← Joint.tests, gpush_split, hu.translation, hu.rotation]

lemma rev_po {P : DiffPlan S} (hs : S.Symmetric) (hp : P.Inclusions S)
    {K : Spins S} {R h} (hk : K.Descends R h) {J : StarOp S} (hj : starRead J h)
    (w : Sentence S) (p : Poincare) : Sentence.rev J (K.po p w) = K.po p (Sentence.rev J w) := by
  simp only [Sentence.rev, Spins.po, List.map_reverse, List.map_map]
  rw [show Letter.op J ∘ Letter.read K p = Letter.read K p ∘ Letter.op J from
    funext fun i => Letter.rewrites hs hp hj K hk i p]

theorem answer : YM.Bid.C28 := by
  intro H G L S W J K R P h hs hp hk hj hu
  refine ⟨strong H W J hs hp hk, ?_⟩
  intro i j p
  change W.expect (Sentence.rev J (K.po p i) ++ K.po p j) = _
  rw [rev_po hs hp hk hj]
  have hboth : K.po p (Sentence.rev J i) ++ K.po p j = K.po p (Sentence.rev J i ++ j) := by
    simp only [Spins.po, List.map_append]
  rw [hboth]
  exact expect_po W hu _ _

end YM.Work.C28
