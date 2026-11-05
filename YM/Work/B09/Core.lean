import YM.Phase.Mixture
import YM.Ward.Plants



/-!
# A common slab, and testing its operators

For the inheritance step B09. Extend one character by Hahn--Banach just as a
continuous *linear* functional (no order or multiplicativity assumed outside
the algebra). Work at the level before compression; test dense word matrix
elements, keeping track of the extra external positions this introduces.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.B09
open Set Filter Function Analysis OS Word
open scoped Topology ContDiff NNReal InnerProductSpace BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber S timeAxis} {A : Spread V}
variable {n : ℕ} {s : E4} {D : ℝ≥0}

def InsideTimes (s : E4) (D : ℝ≥0) (y : E4) :=
  0 < (y+s) timeAxis ∧ (y+s) timeAxis < (D:ℝ)

def Padded (s : E4) (D : ℝ≥0) (x : Points n) :=
  0 < D ∧ x ∈ conf n ∧ ∀ i, InsideTimes s D (x i)

theorem carry_realize (v : Fin n → L.Token) (x : Points n) :
    carry (realize v x) s = realize v (Points.across s x) := by
  unfold carry realize
  rw [List.map_ofFn]; rfl

lemma Padded.slab {x : Points n} (h : Padded s D x) (v : Fin n → L.Token) :
    Slab timeAxis D (carry (realize v x) s) := by
  rw [carry_realize]
  refine ⟨h.1, ⟨(realized ..).2 (Points.across_in s h.2.1), ?_⟩, ?_⟩ <;>
    (intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp)
  exact (h.2.2 i).1
  exact (h.2.2 i).2

/-- Can pack any given compact (will use the *whole window*) in addition
 to any finite configuration. -/
lemma exists_padded {x : Points n} (h : x ∈ conf n) {K : Set E4} (hK : IsCompact K) :
    ∃ (s : E4) (D : ℝ≥0), Padded s D x ∧ ∀ y ∈ K, InsideTimes s D y := by
  let J := K ∪ range x.ofLp
  let f := fun y : E4 => y timeAxis
  have hi : IsCompact (f '' J) :=
    (hK.union (finite_range x.ofLp).isCompact).image (show Continuous f by unfold f; fun_prop)
  obtain ⟨a, ha⟩ := hi.bddBelow
  obtain ⟨b, hb⟩ := hi.bddAbove
  let d := max 0 (b+1-a) + 1
  have hd : 0 < d := add_pos_of_nonneg_of_pos (le_max_left ..) zero_lt_one
  let D : ℝ≥0 := ⟨d, hd.le⟩
  let s := (1-a) • basis timeAxis
  have inside (y) (hy : y∈J) : InsideTimes s D y := by
    have hl : a ≤ y timeAxis := ha ⟨y, hy, rfl⟩
    have hr : y timeAxis ≤ b := hb ⟨y, hy, rfl⟩
    have hh := le_max_right 0 (b+1-a)
    simp only [InsideTimes, D, s, PiLp.add_apply, PiLp.smul_apply, basis_eq, if_true,
      smul_eq_mul, mul_one, d]
    constructor
    · linarith
    · change y timeAxis + (1-a) < max 0 (b+1-a) + 1
      linarith
  exact ⟨s, D, ⟨show 0 < D from hd, h, fun i => inside _ (Or.inr (mem_range_self i))⟩,
    fun y hy => inside y (Or.inl hy)⟩

lemma Padded.near {x : Points n} (h : Padded s D x) : ∀ᶠ y in 𝓝 x, Padded s D y := by
  have ht : ∀ᶠ y : Points n in 𝓝 x, ∀ i, InsideTimes s D (y i) := by
    refine eventually_all.mpr fun i => ?_
    have hc : Continuous (fun y : Points n => (y i+s) timeAxis) := by fun_prop
    exact hc.continuousAt (isOpen_Ioo.mem_nhds (show _ ∈ Ioo 0 (D:ℝ) from h.2.2 i))
  filter_upwards [ht, (conf_open _).mem_nhds h.2.1] with y hy hz
  exact ⟨h.1, hz, hy⟩

lemma slab_near (v : Fin n → L.Token) {x : Points n} (h : Slab timeAxis D (realize v x)) :
    ∀ᶠ y : Points n in 𝓝 x, Slab timeAxis D (realize v y) := by
  have hp : Padded 0 D x := by
    refine ⟨h.1, (realized ..).1 h.2.1.1, fun i => ?_⟩
    have hi : (x i,v i) ∈ realize v x := List.mem_ofFn.mpr ⟨i,rfl⟩
    rw [InsideTimes, add_zero]
    exact ⟨h.2.1.2 _ hi, h.2.2 _ hi⟩
  exact hp.near.mono fun y hy => by simpa using hy.slab v

/-- Raw insertion; evaluate only on padded configurations. -/
def middle (A : Spread V) (s : E4) (D : ℝ≥0) (v : Fin n → S.Tag) (x : Points n) : V.H.Op :=
  A.place D (carry (realize (Ward.expose ∘ v) x) s)

lemma middle_eq_comp (s : E4) (D : ℝ≥0) (v : Fin n → S.Tag) :
    middle A s D v = (fun y => A.place D (realize (Ward.expose ∘ v) y)) ∘ Points.across s := by
  funext y
  rw [middle, carry_realize]; rfl

lemma across_derivative (s : E4) (x : Points n) :
    HasFDerivAt (Points.across s) (ContinuousLinearMap.id ℝ _) x :=
  (hasFDerivAt_id x).add_const (points fun _ => s)

lemma middle_diff {x : Points n} (h : Padded s D x) (v : Fin n → S.Tag) {P : DiffPlan S}
    (hp : A.Laws P) : DifferentiableAt ℝ (middle A s D v) x := by
  rw [middle_eq_comp]
  let u := Ward.expose ∘ v
  have hk : Slab timeAxis D (realize u (Points.across s x)) := carry_realize u x ▸ h.slab u
  exact (((hp.regular D n u _ hk).contDiffAt (slab_near u hk)).differentiableAt (by simp)).comp x
    (across_derivative s x).differentiableAt

/-- Continuous evaluator already on the raw operator space. Agrees at all
 valid insertions with evaluating the class kernels in this character. -/
def Evaluates (T : Table L) (A : Spread V) (φ : V.H.Op →L[ℂ] ℂ) :=
  ∀ {s D n} {x : Points n}, Padded s D x → ∀ v : Fin n → S.Tag,
    S.useAt T x v = φ (middle A s D v x)

lemma has_evaluator {P : A.Resolution} {i : P.X} (hp : P.Out) (he : P.receives T i) :
    ∃ φ, Evaluates T A φ := by
  let B := A.algebra.toSubalgebra.toSubmodule
  let f : StrongDual ℂ B := { (P.character i).toAlgHom.toLinearMap with cont := hp.values i }
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (𝕜 := ℂ) (E := V.VacuumOp) B f
  let c : V.H.Op →L[ℂ] V.VacuumOp :=
    ((ContinuousLinearMap.compL ℂ V.D V.H V.D) V.D.orthogonalProjectionOnto).comp
      ((ContinuousLinearMap.compL ℂ V.D V.H V.H).flip V.D.subtypeL)
  refine ⟨g.comp c, ?_⟩
  intro s D n x hx v
  let w := realize (Ward.expose ∘ v) x
  have hs := hx.slab (Ward.expose ∘ v)
  calc
    S.useAt T x v = T.expect w := (T.readAt (Ward.expose ∘ v) x).symm
    _ = P.character i (A.slot _ _ hs) := he _ ((realized ..).2 hx.2.1) _ _ hs
    _ = _ := (hg (A.slot _ _ hs)).symm

/-- The linearly testing word-pair matrix element (note the op acts on
 the right ket). -/
def tester (V : Chamber S timeAxis) (l r : Future L timeAxis) : V.H.Op →L[ℂ] ℂ :=
  (innerSL ℂ (V.GNS.plant l)).comp (ContinuousLinearMap.apply ℂ V.H (V.GNS.plant r))

lemma tester_ext {X Y : V.H.Op} (he : ∀ l r, tester V l r X = tester V l r Y) : X = Y := by
  refine V.GNS.by_bud fun r => ?_
  refine V.GNS.whole.eq_of_inner_right ℂ fun f => ?_
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add i j hi hj => simp only [map_add, inner_add_left, hi, hj]
  | single i a =>
    simp only [Kernel.Gram.stems, Finsupp.linearCombination_single, inner_smul_left]
    exact congr_arg _ (show inner ℂ (V.GNS.plant i) (X (V.GNS.plant r)) =
      inner ℂ (V.GNS.plant i) (Y (V.GNS.plant r)) from he i r)

def exterior (s : E4) (D : ℝ≥0) (l r : Future L timeAxis) : L.Word :=
  carry (reflect l.val timeAxis ++ raised timeAxis D r.val) (-s)

/-- The extra test points from comparing operators sit strictly outside
 our entire slab (not just disjoint from the particular insertion). -/
lemma exterior_not_inside (l r : Future L timeAxis) {p} (h : p ∈ exterior s D l r) :
    ¬ InsideTimes s D p.1 := by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
  change ¬ InsideTimes s D (z.1 + -s)
  simp only [InsideTimes, neg_add_cancel_right]
  rcases List.mem_append.mp hz with hz|hz
  · exact fun w => (strictly l.property hz).not_gt w.1
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  intro H
  have hw := H.2
  have hy := r.property.2 t ht
  simp at hw; linarith

lemma matrix_of_placed (A : Spread V) (H : S.Hierarchy) {w : L.Word}
    (h : Slab timeAxis D (carry w s)) (l r : Future L timeAxis) :
    distinct (w ++ exterior s D l r) ∧
    tester V l r (A.place D (carry w s)) = S.expect (w ++ exterior s D l r) := by
  let z := reflect l.val timeAxis ++ (entering h r).val
  have hz : distinct z := twoSides l.property (entering h r).property
  have hp : List.Perm z (carry (w ++ exterior s D l r) s) := by
    dsimp only [z]
    rw [distribute, exterior, paths, neg_add_cancel, rest]
    change List.Perm (_ ++ (_ ++ _)) (_ ++ (_ ++ _))
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  have hd : distinct (w ++ exterior s D l r) := by
    have h' := locations.mpr ((hp.map Prod.fst).nodup (locations.mp hz))
    simpa using still h' (-s)
  refine ⟨hd, ?_⟩
  change inner ℂ _ (A.place _ _ _) = _
  rw [A.reads h, V.GNS.measure]
  change S.expect z = _
  rw [← Table.order S H.laws.toSymmetric hz hp, invariance H.translations hd]

/-- Tail of the word in a matrix-element test, expressed in unshifted
 coordinates, with the distinguished head removed. -/
def spectators (s : E4) (D : ℝ≥0) (x : Points (n+1)) (q : Fin n → S.Tag)
    (l r : Future L timeAxis) : L.Word :=
  realize (Ward.expose ∘ q) (Points.tail x) ++ exterior s D l r

lemma realize_head (x : Points (n+1)) (q : Fin n → S.Tag) (t : S.Tag) :
    realize (Ward.expose ∘ Fin.cons t q) x =
    (x 0, Ward.expose t) :: realize (Ward.expose ∘ q) (Points.tail x) := by
  simp only [realize, List.ofFn_succ, comp_apply, Fin.cons_zero, Fin.cons_succ]; rfl

lemma matrix_at_center (H : S.Hierarchy) {x : Points (n+1)} (hx : Padded s D x)
    (q : Fin n → S.Tag) (l r : Future L timeAxis) (t : S.Tag) :
    let v := spectators s D x q l r
    Points.cons (x 0) (positions v) ∈ conf (v.length+1) ∧
    tester V l r (middle A s D (Fin.cons t q) x) =
      S.useAt S (Points.cons (x 0) (positions v)) (Fin.cons t (S.classTokens ∘ tokens v)) := by
  dsimp only
  let v := spectators s D x q l r
  have hw := matrix_of_placed A H (hx.slab (Ward.expose ∘ Fin.cons t q)) l r
  change distinct _ ∧ tester _ _ _ (middle _ _ _ _ _) = S.expect _ at hw
  rw [realize_head] at hw
  have hv : distinct ((x 0, Ward.expose t)::v) := hw.1
  refine ⟨Ward.disjoint_table hv, hw.2.trans ?_⟩
  change S.expect ((x 0, Ward.expose t)::v) = _
  rw [Ward.exact_table hv H]
  simp only [Ward.sends_back]; rfl

end YM.Work.B09
