import YM.Bid.Phase

/-!
# Theme on separated words

Work throughout with the very room/spread passed in (in the application,
those of the unselected hierarchy). Use the freedom to read `M` in any one
common strict slab (`Ground.overline`), with fixed shift and width for each
local, permutation, or label comparison. Prove the permutation, unit-label
and linearity identities *already before* compression by pairing against the
two dense word spans; in particular in such a pairing the distinguished
insertion is tested with genuine separated exterior data. This gives
dependence through the all-spectator field quotient, linearly in each slot.
No individual-character or commutativity premise.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.B03
open Set Filter Function OS OS.Ground Table Word
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff

variable {G : Gauge} {L : Register G} {S : Table L}
variable {V : Chamber S timeAxis} (A : Spread V)
variable {n : ℕ} {d : ℝ≥0}

/-! ## Slabs and testing on dense vectors -/

private lemma dist_perm {v w : L.Word} (h : List.Perm v w) (hv : distinct v) :
    distinct w :=
  locations.mpr ((h.map Prod.fst).nodup (locations.mp hv))

private lemma slab_perm {v w : L.Word} (h : List.Perm v w) (hv : Slab timeAxis d v) :
    Slab timeAxis d w :=
  ⟨hv.1, ⟨dist_perm h hv.2.1.1, fun i hi => hv.2.1.2 i (h.mem_iff.mpr hi)⟩,
    fun i hi => hv.2.2 i (h.mem_iff.mpr hi)⟩

private lemma matrix_ext {U W : V.H.Op}
    (h : ∀ p q : Future L timeAxis, inner ℂ (V.GNS.plant p) (U (V.GNS.plant q)) =
      inner ℂ (V.GNS.plant p) (W (V.GNS.plant q))) : U = W := by
  apply V.GNS.by_bud
  intro q
  apply V.GNS.whole.eq_of_inner_right ℂ
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add i j hi hj => simp only [map_add, inner_add_left, hi, hj]
  | single i c =>
    simp only [Kernel.Gram.stems, Finsupp.linearCombination_single,
      inner_smul_left, h]

private lemma read_matrix {w : L.Word} (h : Slab timeAxis d w) (p q : Future L timeAxis) :
    inner ℂ (V.GNS.plant p) (A.place d w (V.GNS.plant q)) =
      S.expect (reflect p.val timeAxis ++ linked timeAxis d w q.val) := by
  rw [A.reads h, V.GNS.measure]
  rfl

private lemma place_perm (hs : S.Hierarchy) {v w : L.Word}
    (hv : Slab timeAxis d v) (h : List.Perm v w) : A.place d v = A.place d w := by
  apply matrix_ext
  intro p q
  rw [read_matrix A hv, read_matrix A (slab_perm h hv)]
  symm
  apply S.order hs.laws.toSymmetric (twoSides p.property (entering hv q).property)
  apply List.Perm.append_left
  apply List.Perm.append_right _ h

/-- Compression as a bounded linear operation between operator spaces. -/
private def compressL (V : Chamber S timeAxis) : V.H.Op →L[ℂ] V.VacuumOp :=
  (ContinuousLinearMap.compL ℂ (↥V.D) V.H (↥V.D) V.D.orthogonalProjectionOnto).comp
    ((ContinuousLinearMap.compL ℂ (↥V.D) V.H V.H).flip V.D.subtypeL)

/-! ## The structural identities for `M` -/

private lemma perm_m (hs : S.Hierarchy) (hv : Steady V) {v w : L.Word}
    (h : List.Perm v w) (hp : distinct v) (hq : distinct w) :
    M A v hp = M A w hq := by
  obtain ⟨s,d,H⟩ := Spread.Resolution.place_exists hp
  have hperm : List.Perm (carry v s) (carry w s) := h.map _
  rw [overline A hv v hp s H, overline A hv w hq s (slab_perm hperm H)]
  apply Subtype.ext
  exact congr_arg (compressL V) (place_perm A hs H hperm)

private lemma offset_m (hv : Steady V) (x : E4) (v : L.Word) (h : distinct v) :
    M A v h = M A (carry v x) (still h x) := by
  obtain ⟨s,d,H⟩ := Spread.Resolution.place_exists (still h x)
  have hh : Slab timeAxis d (carry v (x+s)) := by rwa [paths] at H
  rw [overline A hv v h (x+s) hh, overline A hv (carry v x) (still h x) s H]
  apply Subtype.ext
  change A.atom _ d = A.atom _ d
  rw [paths]

private lemma vacant_m (hv : Steady V) : M A [] (locations.mpr (by simp)) = 1 := by
  rw [spots A hv (vacuum_width (d := 1) (by norm_num))]
  apply Subtype.ext
  change A.atom _ _ = ContinuousLinearMap.id ℂ _
  unfold Spread.atom
  rw [A.blank (by norm_num)]
  ext1 x
  change V.D.orthogonalProjectionOnto (V.flow.E _ x.val) = _
  rw [(V.flow.fixed _).1 x.property,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

private lemma opposite_m (hs : S.Hierarchy) (hv : Steady V) (w : L.Word)
    (h : distinct w) (h' : distinct (reflect w timeAxis)) :
    star (M A w h) = M A (reflect w timeAxis) h' := by
  obtain ⟨s,d,H⟩ := Spread.Resolution.place_exists h
  let u := Ortho.move (Signed.reflect timeAxis) s + (d:ℝ) • basis timeAxis
  have hp : opposite timeAxis d (carry w s) = carry (reflect w timeAxis) u := by
    unfold opposite raised
    rw [refl_over, paths]
  have ht := mirrorsSlab H
  rw [overline A hv _ h s H, overline A hv _ h' u (hp ▸ ht)]
  apply Subtype.ext
  change ContinuousLinearMap.adjoint (A.atom (carry w s) d) =
    A.atom (carry (reflect w timeAxis) u) d
  rw [← hp]
  unfold Spread.atom
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    A.adjoints H hs.translations, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto]
  rfl

/-! ## Head of a separated slab word, then of an arbitrary separated word -/

/-- First insertion paired against actual *both* exterior words. Move it to
the front of the combined word. Inner product linear on the right; no extra
stars on this head label. -/
private lemma front_matrix (hs : S.Hierarchy) (x : E4) (a : L.Token)
    (w : L.Word) (h : Slab timeAxis d ((x,a)::w)) (p q : Future L timeAxis) :
    let r := reflect p.val timeAxis ++ linked timeAxis d w q.val
    Points.cons x (positions r) ∈ conf _ ∧
    inner ℂ (V.GNS.plant p) (A.place d ((x,a)::w) (V.GNS.plant q)) =
      S.read (Points.cons x (positions r)) (Fin.cons a (tokens r)) := by
  intro r
  let W := reflect p.val timeAxis ++ linked timeAxis d ((x,a)::w) q.val
  have hW : distinct W := twoSides p.property (entering h q).property
  have he : List.Perm W ((x,a)::r) := List.perm_middle
  refine ⟨Ward.disjoint_table (dist_perm he hW), ?_⟩
  rw [read_matrix A h]
  exact (S.order hs.laws.toSymmetric hW he).symm.trans (Ward.resolve S)

private lemma slab_tail {w : L.Word} {p : L.Plant} (h : Slab timeAxis d (p::w)) :
    Slab timeAxis d w := by
  refine ⟨h.1, ⟨?_, fun i hi => h.2.1.2 i (List.mem_cons_of_mem _ hi)⟩,
    fun i hi => h.2.2 i (List.mem_cons_of_mem _ hi)⟩
  apply locations.mpr
  exact (List.nodup_cons.mp (locations.mp h.2.1.1)).2

private lemma place_one_cons (hs : S.Hierarchy) (x : E4) (k : ℕ)
    (w : L.Word) (h : Slab timeAxis d ((x,L.one k)::w)) :
    A.place d ((x,L.one k)::w) = A.place d w := by
  apply matrix_ext
  intro p q
  obtain ⟨hx,he⟩ := front_matrix A hs x _ w h p q
  rw [he, hs.laws.unital hx, read_matrix A (slab_tail h)]
  rfl

private lemma m_one_cons (hs : S.Hierarchy) (hv : Steady V) (x : E4) (k : ℕ)
    (w : L.Word) (h : distinct ((x,L.one k)::w)) (hp : distinct w) :
    M A ((x,L.one k)::w) h = M A w hp := by
  obtain ⟨s,d,H⟩ := Spread.Resolution.place_exists h
  have hh : Slab timeAxis d ((x+s,L.one k)::carry w s) := H
  rw [overline A hv _ h _ H, overline A hv w hp s (slab_tail hh)]
  apply Subtype.ext
  exact congr_arg (compressL V) (place_one_cons A hs _ _ _ hh)

/-- Linear dependence at fixed slab. In fact through `S.project`. -/
private lemma place_linear_front (hs : S.Hierarchy) (x : E4) (k : ℕ)
    (w : L.Word) (h : ∀ b : L.Ref k, Slab timeAxis d ((x,⟨k,b⟩)::w)) :
    ∃ B : S.Field k →ₗ[ℂ] V.H.Op, ∀ b : L.Ref k,
      A.place d ((x,⟨k,b⟩)::w) = B (S.project k b) := by
  let T (b : L.Ref k) := A.place d ((x,⟨k,b⟩)::w)
  have he (p q : Future L timeAxis) : ∃ z : Exterior L, ∀ b,
      inner ℂ (V.GNS.plant p) (T b (V.GNS.plant q)) = S.spectra k (S.project k b) z := by
    let r := reflect p.val timeAxis ++ linked timeAxis d w q.val
    exact ⟨⟨r.length, Points.cons x (positions r), tokens r,
      (front_matrix A hs x _ w (h 0) p q).1⟩,
      fun b => (front_matrix A hs x _ w (h b) p q).2⟩
  let f := fun z : S.Field k => T (S.representative k z)
  refine ⟨{ toFun := f
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro y y'
    apply matrix_ext
    intro p q
    obtain ⟨z,hz⟩ := he p q
    simp only [f, add_apply, inner_add_right, hz, rep,
      map_add, Pi.add_apply]
  · intro c y
    apply matrix_ext
    intro p q
    obtain ⟨z,hz⟩ := he p q
    simp only [f, RingHom.id_apply, smul_apply,
      inner_smul_right, hz, rep, map_smul, Pi.smul_apply, smul_eq_mul]
  intro b
  change T b = f (S.project k b)
  apply matrix_ext
  intro p q
  obtain ⟨z,hz⟩ := he p q
  simp only [f, hz, rep]

private lemma m_linear_front (hs : S.Hierarchy) (hv : Steady V)
    (x : E4) (k : ℕ) (w : L.Word)
    (h : ∀ b : L.Ref k, distinct ((x,⟨k,b⟩)::w)) :
    ∃ B : S.Field k →ₗ[ℂ] ↥A.algebra, ∀ b : L.Ref k,
      M A ((x,⟨k,b⟩)::w) (h b) = B (S.project k b) := by
  obtain ⟨s,d,H⟩ := Spread.Resolution.place_exists (h 0)
  have h0 : Slab timeAxis d ((x+s,⟨k,0⟩)::carry w s) := H
  have hh (b : L.Ref k) : Slab timeAxis d ((x+s,⟨k,b⟩)::carry w s) := by
    refine ⟨H.1, ⟨still (h b) s, ?_⟩, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hr
      · exact h0.2.1.2 (x+s,⟨k,0⟩) (List.mem_cons_self ..)
      exact h0.2.1.2 p (List.mem_cons_of_mem _ hr)
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hr
      · exact h0.2.2 (x+s,⟨k,0⟩) (List.mem_cons_self ..)
      exact h0.2.2 p (List.mem_cons_of_mem _ hr)
  obtain ⟨B,hB⟩ := place_linear_front A hs _ _ _ hh
  let f := (compressL V).toLinearMap.comp B
  have he (b : L.Ref k) : (M A _ (h b)).val = f (S.project k b) := by
    rw [overline A hv _ (h b) s (hh b)]
    exact congr_arg (compressL V) (hB b)
  refine ⟨f.codRestrict A.algebra.toSubalgebra.toSubmodule ?_,
    fun b => Subtype.ext (he b)⟩
  intro y
  obtain ⟨b,rfl⟩ := S.onto k y
  rw [← he]
  exact (M A _ (h b)).property

/-! ## Arity notation; arbitrary positions of the head label -/

open Bid

private lemma unital_m (hs : S.Hierarchy) (hv : Steady V)
    (k : ℕ) (x : Points (n+1)) (v : Fin n → L.Token) (hx : x ∈ conf _) :
    M A (realize (Fin.cons (α := fun _ => L.Token) (L.one k) v) x)
        ((realized _ _).2 hx) =
      M A (realize v (Points.tail x)) ((realized _ _).2 (Points.tail_in hx)) := by
  let w := realize (Fin.cons (α := fun _ => L.Token) (L.one k) v) x
  let u := realize v (Points.tail x)
  have he : w = (x 0,L.one k)::u := by
    dsimp only [w, u, realize]
    rw [List.ofFn_succ]
    simp only [Points.tail, points_apply, Fin.cons_zero, Fin.cons_succ]
  have hh : distinct w := (realized _ _).2 hx
  exact (perm_m A hs hv (show List.Perm w ((x 0,L.one k)::u) by rw [he]) hh
    (he ▸ hh)).trans (m_one_cons A hs hv _ _ _ _ ((realized _ _).2 (Points.tail_in hx)))

/-- Updating one arbitrary slot factors linearly through its projected field,
including (trivially) the depot convention off Conf. -/
private lemma depot_update [DecidableEq (Fin n)] (hs : S.Hierarchy) (hv : Steady V)
    (p : Caps n) (x : Points n) (t : L.Vector p) (i : Fin n) :
    ∃ B : S.Field (p i) →ₗ[ℂ] ↥A.algebra, ∀ b : L.Ref (p i),
      depot V A x p (update t i b) = B (S.project (p i) b) := by
  classical
  by_cases hx : x ∈ conf _
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      let σ := Equiv.swap 0 i
      let f (z : L.Vector p) (j : Fin (n+1)) : L.Plant := (x j,⟨p j,z j⟩)
      let T (b : L.Ref (p i)) :=
        realize (fun j => (f (update t i b) j).2) x
      let r : L.Word := List.ofFn fun j : Fin n => f t (σ j.succ)
      let W (b : L.Ref (p i)) := (x i,(⟨p i,b⟩ : L.Token))::r
      have hperm (b : L.Ref (p i)) : List.Perm (T b) (W b) := by
        have hz : σ 0 = i := Equiv.swap_apply_left 0 i
        have hh (j : Fin n) : σ j.succ ≠ i := by
          rw [← hz]
          exact σ.injective.ne (Fin.succ_ne_zero _)
        have he : List.ofFn (f (update t i b) ∘ σ) = W b := by
          rw [List.ofFn_succ]
          have hhead : f (update t i b) (σ 0) = (x i,⟨p i,b⟩) := by
            rw [hz]
            unfold f
            rw [update_self]
          have htail (j : Fin n) :
              f (update t i b) (σ j.succ) = f t (σ j.succ) := by
            unfold f
            rw [update_of_ne (hh j)]
          simp only [comp_apply, hhead, htail, W, r]
        rw [← he]
        exact (σ.ofFn_comp_perm _).symm
      have ht (b) : distinct (T b) := (realized _ _).2 hx
      have hh (b) : distinct (W b) := dist_perm (hperm b) (ht b)
      obtain ⟨B,hB⟩ := m_linear_front A hs hv (x i) (p i) r hh
      refine ⟨B, fun b => ?_⟩
      rw [depot, dif_pos hx]
      exact (perm_m A hs hv (hperm b) (ht b) (hh b)).trans (hB b)
  · exact ⟨0, by simp [depot, hx]⟩

private lemma array_m (hs : S.Hierarchy) (hv : Steady V)
    (p : Caps n) (x : Points n) :
    ∃ U : MultilinearMap ℂ (fun i => L.Ref (p i)) ↥A.algebra,
      ∀ t : L.Vector p, U t = depot V A x p t := by
  refine ⟨{ toFun := fun t => depot V A x p t
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun _ => rfl⟩
  · intro inst t i b c
    obtain ⟨B,hB⟩ := depot_update A hs hv p x t i
    simp only [hB, map_add]
  · intro inst t i c b
    obtain ⟨B,hB⟩ := depot_update A hs hv p x t i
    simp only [hB, map_smul]

private lemma pins_m (hs : S.Hierarchy) (hv : Steady V)
    (p : Caps n) (x : Points n) (v w : L.Vector p)
    (h : ∀ i, S.project (p i) (v i) = S.project (p i) (w i)) :
    depot V A x p v = depot V A x p w := by
  classical
  let t (s : Finset (Fin n)) (i : Fin n) := if i ∈ s then v i else w i
  have he (s : Finset (Fin n)) : depot V A x p (t s) = depot V A x p w := by
    induction s using Finset.induction_on with
    | empty => simp [t]
    | @insert i s hi ih =>
      obtain ⟨B,hB⟩ := depot_update A hs hv p x (t s) i
      have hh : t s = update (t s) i (w i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [t, hi]
        simp [update, hj]
      rw [← ih]
      conv_rhs => rw [hh]
      rw [show t (insert i s) = update (t s) i (v i) by
        funext j
        by_cases hj : j = i
        · subst j; simp [t]
        simp [update, hj, t]]
      rw [hB, hB, h]
  simpa [t] using he Finset.univ

/-! ## Smoothness: fix shift AND width on a neighborhood of each point -/

private lemma carried_realization (v : Fin n → L.Token) (x : Points n) (s : E4) :
    carry (realize v x) s = realize v (Points.across s x) := by
  unfold carry realize
  rw [List.map_ofFn]
  rfl

private lemma slab_open (v : Fin n → L.Token) (hd : 0 < d) :
    IsOpen {x : Points n | Slab timeAxis d (realize v x)} := by
  have he : {x : Points n | Slab timeAxis d (realize v x)} =
      conf n ∩ ⋂ i : Fin n, {x : Points n | x i timeAxis ∈ Ioo (0:ℝ) d} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, mem_Ioo]
    constructor
    · intro h
      refine ⟨(realized _ _).1 h.2.1.1, fun i => ?_⟩
      have hi : (x i,v i) ∈ realize v x := List.mem_ofFn.mpr ⟨i,rfl⟩
      exact ⟨h.2.1.2 _ hi, h.2.2 _ hi⟩
    rintro ⟨hx,hi⟩
    refine ⟨hd, ⟨(realized _ _).2 hx, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
      exact (hi i).1
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact (hi i).2
  rw [he]
  refine (conf_open _).inter (isOpen_iInter_of_finite fun i => ?_)
  exact isOpen_Ioo.preimage (show Continuous (fun x : Points n => x i timeAxis) by fun_prop)

private lemma steep_m {D : DiffPlan S} (hv : Steady V) (ha : A.Laws D)
    (v : Fin n → L.Token) :
    ContDiffOn ℝ ∞ (fun x : Points n =>
      (depot V A x (fun i => (v i).1) (fun i => (v i).2)).val) (conf n) := by
  intro x hx
  obtain ⟨s,d,H⟩ := Spread.Resolution.place_exists ((realized v x).2 hx)
  let tr : Points n → Points n := Points.across s
  have ht : ContDiff ℝ ∞ tr := by
    have he : tr = fun y : Points n => y + points (fun _ => s) := rfl
    rw [he]
    exact contDiff_id.add contDiff_const
  let e := {y : Points n | Slab timeAxis d (realize v y)}
  have he : e ∈ 𝓝 (tr x) := (slab_open v H.1).mem_nhds (by
    change Slab timeAxis d (realize v (Points.across s x))
    rwa [carried_realization] at H)
  have hb : tr x ∈ e := mem_of_mem_nhds he
  let f := fun y => compressL V (A.place d (realize v (tr y)))
  have hc : ContDiff ℝ ∞ (fun U : V.H.Op => compressL V U) := by
    have hu : ContDiff ℂ ∞ (fun U : V.H.Op => compressL V U) :=
      ContinuousLinearMap.contDiff (E := V.H.Op) (F := V.VacuumOp)
        (𝕜 := ℂ) (compressL V)
    exact hu.restrict_scalars ℝ
  have hf : ContDiffAt ℝ ∞ f x :=
    hc.contDiffAt.comp x
      ((((ha.regular d n v) (tr x) hb).contDiffAt he).comp x ht.contDiffAt)
  apply ContDiffAt.contDiffWithinAt
  apply hf.congr_of_eventuallyEq
  filter_upwards [(conf_open _).mem_nhds hx, ht.continuous.continuousAt he] with y hy hp
  change Slab timeAxis d (realize v (Points.across s y)) at hp
  have hh : Slab timeAxis d (carry (realize v y) s) := by
    rwa [carried_realization]
  rw [depot, dif_pos hy]
  change (M A (realize v y) _).val = _
  rw [overline A hv _ _ s hh]
  change compressL V (A.place d (carry (realize v y) s)) = f y
  rw [carried_realization]

/-- Shift into a slab locally, compress on the fixed subspace. -/
theorem answer : YM.Bid.B03 := by
  intro G L S hS D V A hV hA
  exact
    { vacant := vacant_m A hV
      array := fun _ p x => array_m A hS hV p x
      unital := fun d x v hx => unital_m A hS hV d x v hx
      changes := perm_m A hS hV
      offsets := offset_m A hV
      steep := fun _ v => steep_m A hV hA v
      opposite := opposite_m A hS hV
      pins := fun _ p x v w h => pins_m A hS hV p x v w h }

end YM.Work.B03
