import YM.Analysis.Polydisc
import YM.Bid.Corners

set_option autoImplicit false
noncomputable section
namespace YM.Work.C02
open Set Function OS OS.Ground OS.Semigroup Word Boundary Boundary.Small Bid
open scoped NNReal InnerProductSpace

variable {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber T timeAxis}
variable {A : Spread V} {P : DiffPlan S} {B : Small S V} {n : ℕ}

private lemma basis_time (t : ℝ) : t • basis timeAxis = position 0 t := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [show position (0 : Space3) t (Fin.last 3) = t from time_position _ _]
    change t * basis timeAxis timeAxis = t
    simp
  · rw [show position (0 : Space3) t j.castSucc = (0 : ℝ) from
      congrArg (fun x : Space3 => x j) (spatial_position (0 : Space3) t)]
    simp [show j.castSucc ≠ timeAxis from j.castSucc_ne_last]

private lemma pos_add (x x' : Space3) (t t' : ℝ) :
    position x t + position x' t' = position (x+x') (t+t') := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change time (position x t) + time (position x' t') = time (position (x+x') (t+t'))
    simp
  · simp [position]

private lemma neg_pos (x : Space3) (t : ℝ) : -position x t = position (-x) (-t) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change -time (position x t) = time (position (-x) (-t))
    simp
  · simp [position]

private def glyph (v : S.Tag) : L.Token := ⟨v.1, S.representative v.1 v.2⟩
private def born (p : ℝ≥0) (v : S.Tag) : L.Word := [(position 0 p, glyph v)]
private lemma cradle {p : ℝ≥0} (hp : 0 < p) (v : S.Tag) : Slab timeAxis (p+p) (born p v) := by
  refine ⟨add_pos hp hp, ⟨locations.mpr (by simp [born]), ?_⟩, ?_⟩ <;>
    (intro x hx; rw [born, List.mem_singleton] at hx; subst x)
  · change 0 < time (position 0 p)
    simpa using (show 0 < (p:ℝ) from hp)
  change time (position 0 p) < ((p+p:ℝ≥0):ℝ)
  simpa using (show 0 < (p:ℝ) from hp)

private def script (x : SpacePoints n) (y : Heights n) (v : Fin n → S.Tag) : L.Word :=
  realize (glyph ∘ v) (place x y)
private lemma script_cons (x : SpacePoints (n+1)) (y : Heights (n+1)) (v : Fin (n+1) → S.Tag) :
    script x y v = (position (x 0) (y 0), glyph (v 0)) :: script (Fin.tail x) (Fin.tail y) (Fin.tail v) :=
  List.ofFn_succ

private lemma enters {x : SpacePoints (n+1)} {y : Heights (n+1)} {v : Fin (n+1) → S.Tag}
    {p : ℝ≥0} (hp : 0<p) {f : Future L timeAxis}
    (hf : f.val = carry (script (Fin.tail x) (Fin.tail y) (Fin.tail v)) (-position (x 0) (y 0+p))) :
    (entering (cradle hp (v 0)) f).val = carry (script x y v) (-position (x 0) (y 0-p)) := by
  dsimp only [entering, linked, raised]
  rw [hf, paths, script_cons]
  simp only [born, carry, List.singleton_append, List.map_cons, basis_time, neg_pos, pos_add,
    NNReal.coe_add]
  rw [show -(y 0+(p:ℝ))+(p+p) = -(y 0-p) by ring, add_zero, add_neg_cancel,
      show y 0+-(y 0-(p:ℝ)) = p by ring]

private lemma enough_tail {p : ℝ≥0} {y : Heights (n+1)} (hy : enough y p) : enough (Fin.tail y) p :=
  ⟨hy.1, hy.2.1, fun i j hij => hy.2.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩

private lemma train_pure (hB : B.concretized A) {p : ℝ≥0}
    (x : SpacePoints n) (y : Heights n) (v : Fin n → S.Tag) (X : Space3) (Y : ℝ)
    (h : enough y p) (hp : ∀ i, 4*(p:ℝ)<y i-Y) :
    ∃ f : Future L timeAxis, f.val = carry (script x y v) (-position X (Y+p)) ∧
      B.trainB p n (fun i => (y i:ℂ)*Complex.I) x (fun i => S.pin (v i).1 (v i).2)
        ((Y:ℂ)*Complex.I) X = V.GNS.plant f := by
  induction n generalizing X Y with
  | zero => exact ⟨air timeAxis, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨f,hf,ht⟩ := ih (Fin.tail x) (Fin.tail y) (Fin.tail v) (x 0) (y 0)
      (enough_tail h) (fun j => h.2.2 0 j.succ j.succ_pos)
    have hpos : 0 < y 0-Y-(p+p : ℝ≥0) := by push_cast; linarith [hp 0, p.coe_nonneg]
    let t : ℝ≥0 := ⟨_, hpos.le⟩
    have he : interval ((y 0:ℂ)*Complex.I-(Y:ℂ)*Complex.I) (p+p) = duration t := by
      apply Complex.ext <;> simp [interval,duration,t]; rfl
    refine ⟨travel (over (entering (cradle h.1 (v 0)) f) (bufferF (x 0-X))) t, ?_, ?_⟩
    · change carry (carry _ _) _ = _
      rw [enters h.1 hf, paths, paths]
      congr 1
      change -position (x 0) (y 0-p) + (position (x 0-X) 0 + (t:ℝ) • basis _) = _
      rw [basis_time, neg_pos, neg_pos, pos_add, pos_add]
      congr 1
      · abel
      rw [show (t:ℝ)=y 0-Y-((p:ℝ)+p) from rfl]; ring
    rw [trainB]
    change rip _ _ _ (B.bar p _ (B.trainB p n _ _ _ _ _)) = _
    erw [show B.trainB p n _ _ _ _ _=V.GNS.plant f from ht,
        hB _ _ p h.1, A.reads (cradle h.1 (v 0)), V.atBirth, V.across, rip, he,
        V.flow.roots_heat (show 0<t from hpos)]
    rfl

private lemma root (H : T.Hierarchy) (hB : B.concretized A) {p : ℝ≥0}
    (x : SpacePoints n) (y : Heights n) (v : Fin n → S.Tag) (hy : y ∈ east n) (hp : enough y p) :
    B.matrix p n (fun i => ↑(y i)*Complex.I) x (fun i => S.pin (v i).1 (v i).2) = S.useAt T (place x y) v := by
  suffices B.matrix p n (fun i => ↑(y i)*Complex.I) x (fun i => S.pin (v i).1 (v i).2) = T.expect (script x y v) by
    rw [script,T.readAt] at this
    exact this
  cases n with
  | zero => exact V.GNS.measure (air _) (air _)
  | succ n =>
    obtain ⟨f,hf,ht⟩ := train_pure hB (Fin.tail x) (Fin.tail y) (Fin.tail v) (x 0) (y 0)
      (enough_tail hp) (fun j => hp.2.2 0 j.succ j.succ_pos)
    rw [Small.matrix]
    change inner ℂ V.omega (B.bar p _ (B.trainB p n _ _ _ _ _)) = _
    erw [show B.trainB p n _ _ _ _ _=V.GNS.plant f from ht,
        hB _ _ p hp.1,A.reads (cradle hp.1 (v 0)),Chamber.omega,V.GNS.measure]
    change T.expect (entering (cradle hp.1 (v 0)) f).val = _
    rw [enters hp.1 hf, invariance H.translations]
    exact (realized ..).mpr (clear hy x)

theorem pad_bar (H : Pantry S T V P A) (hB : Piece A B) {p : ℝ≥0}
    (hp : 0 < p) (u : ℝ≥0) (v : S.Union) :
    B.bar (p+u) v = ((V.flow.E u).comp (B.bar p v)).comp (V.flow.E u) := by
  obtain ⟨d,s,rfl⟩ := P.covered H.head.laws.toSymmetric H.rises v
  have hs := cradle hp (⟨d,s⟩ : S.Tag)
  have hb : born (p+u) (⟨d,s⟩ : S.Tag) = raised timeAxis u (born p (⟨d,s⟩ : S.Tag)) := by
    simp only [born, raised, carry, List.map_cons, List.map_nil, basis_time, pos_add,
      add_zero, NNReal.coe_add]
  have hr (k : ℝ≥0) (h : 0<k) : B.bar k (S.pin d s) = A.place (k+k) (born k ⟨d,s⟩) := hB.bits d s k h
  rw [hr p hp, hr (p+u) (add_pos_of_pos_of_nonneg hp zero_le), hb,
    show (p+u)+(p+u)=u+(p+p)+u by abel, stretches A (fills hs u), crossing A hs]

theorem pad_rip (V : Chamber T timeAxis) {z : ℂ} {p u : ℝ≥0} (hu : 0<u)
    (hz : 4*((p+u:ℝ≥0):ℝ) < z.im) (x : Space3) :
    rip (C:=V) z (p+p) x = ((V.flow.E u).comp (rip z ((p+u)+(p+u)) x)).comp (V.flow.E u) := by
  have ht := dur.mpr hu
  let w := interval z ((p+u)+(p+u))
  have hw : w ∈ inside := (down ..).mpr (by push_cast at *; linarith [p.coe_nonneg, u.coe_nonneg])
  have hsum : duration u + w ∈ inside := show 0<(duration u).re+w.re from add_pos ht hw
  have he : interval z (p+p) = duration u+w+duration u := by
    simp only [interval, duration, w, NNReal.coe_add, Complex.ofReal_add]; ring
  unfold rip
  rw [he, V.flow.pairs hsum ht,
    V.flow.pairs ht hw, V.flow.roots_heat hu, ContinuousLinearMap.comp_assoc,
    V.flow.independent, ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc (V.flow.E u) (V.flow.F w)]

private lemma train_pad (H : Pantry S T V P A) (hB : Piece A B) {p u : ℝ≥0}
    (hp : 0<p) (hu : 0<u) (z : Times n) (x : SpacePoints n) (v : Fin n → S.Union) (Z : ℂ) (X : Space3)
    (h : lit z (p+u)) (ht : ∀ i, 4*((p+u:ℝ≥0):ℝ)<(z i).im-Z.im) :
    V.flow.E u (B.trainB (p+u) n z x v Z X) = B.trainB p n z x v Z X := by
  induction n generalizing Z X with
  | zero => exact (V.flow.fixed _).1 V.omega0.property u
  | succ n ih =>
    rw [trainB, trainB, pad_bar H hB hp, pad_rip V (z:=z 0-Z) (p:=p) hu (ht 0)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ih (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0) (enough_tail h)
      (fun j => h.2.2 0 j.succ j.succ_pos)]

private lemma matrix_pad (H : Pantry S T V P A) (hB : Piece A B) {p u : ℝ≥0}
    (hp : 0<p) (hu : 0<u) (z : Times n) (x : SpacePoints n) (v : Fin n → S.Union)
    (hz : lit z (p+u)) : B.matrix (p+u) n z x v = B.matrix p n z x v := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [Small.matrix, Small.matrix, pad_bar H hB hp]
    simp only [ContinuousLinearMap.comp_apply]
    rw [train_pad H hB hp hu _ _ _ _ _ (show lit (Fin.tail z) _ from enough_tail hz)
      (fun j => hz.2.2 0 j.succ j.succ_pos), ← V.flow.swing,
      show V.flow.E u V.omega=V.omega from (V.flow.fixed _).1 V.omega0.property u]

theorem answer : YM.Bid.C02 := by
  intro G L S T V P A B H hB
  refine ⟨hB, fun p y x v hy hp => root H.adopted hB.bits x y v hy hp, ?_⟩
  intro n z x p q l _ hq hl
  obtain h|h|h := lt_trichotomy q l
  · obtain ⟨u,rfl⟩ := exists_add_of_le h.le
    exact (matrix_pad H hB hq.1 (by simpa using h) z x p hl).symm
  · rw [h]
  obtain ⟨u,rfl⟩ := exists_add_of_le h.le
  exact matrix_pad H hB hl.1 (by simpa using h) z x p hq

end YM.Work.C02
