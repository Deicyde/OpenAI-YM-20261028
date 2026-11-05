import YM.OS.Halves
import YM.Work.B02.Analysis


/-!
# Differentiating true spreads

1. Slab interior is open and admits local uniform bounds on placements.
2. The same Gram reads, with arbitrary exterior plants, realize the scalar
   derivatives as exactly the change of label prescribed in Laws. The
   derivative uses the quotient of S, even when the chamber is for T.
3. All placements (including placements with these differentiated labels)
   are therefore operator-norm continuous, then norm differentiable with
   the prescribed derivative. Bootstrap to all finite orders on this open set.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.B02
open OS Word Function Filter Set
open scoped Topology ContDiff NNReal InnerProductSpace BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L}
variable {a : Axis} {V : Chamber T a}
variable {n : ℕ}

section Region

/-- A common open domain for the placements (independent of their labels). -/
def region (a : Axis) (d : ℝ≥0) (n : ℕ) : Set (Points n) :=
  {x | 0 < d ∧ x ∈ conf n ∧ ∀ i, 0 < x i a ∧ x i a < (d : ℝ)}

theorem in_region (d : ℝ≥0) (v : Fin n → L.Token) (x : Points n) :
    Slab a d (realize v x) ↔ x ∈ region a d n := by
  constructor
  · intro h
    refine ⟨h.1, (realized v x).1 h.2.1.1, fun i => ?_⟩
    have hi : (x i, v i) ∈ realize v x := List.mem_ofFn.mpr ⟨i, rfl⟩
    exact ⟨h.2.1.2 _ hi, h.2.2 _ hi⟩
  rintro ⟨hd,hx,ht⟩
  refine ⟨hd, ⟨(realized v x).2 hx, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    rw [← hi]
    exact (ht i).1
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
  rw [← hi]
  exact (ht i).2

theorem region_open (d : ℝ≥0) (n : ℕ) : IsOpen (region a d n) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨hd,hx,ht⟩
  have hi i : ∀ᶠ y : Points n in 𝓝 x, 0 < y i a ∧ y i a < (d : ℝ) := by
    have hc : ContinuousAt (fun y : Points n => y i a) x := by fun_prop
    exact hc (Ioo_mem_nhds (ht i).1 (ht i).2)
  filter_upwards [(conf_open n).mem_nhds hx, eventually_all.mpr hi] with y hy hiy
  exact ⟨hd,hy,hiy⟩

private theorem realize_spaced (r : ℝ) (v : Fin n → L.Token) (x : Points n) :
    spaced r (positions (realize v x)) ↔ spaced r x := by
  let e : Fin (realize v x).length ≃ Fin n := finCongr (by simp [realize])
  have he i : positions (realize v x) i = x (e i) := by
    simp [positions, realize, e, finCongr]
    rfl
  constructor
  · intro h i j hne
    have ht := h (e.symm i) (e.symm j) (e.symm.injective.ne hne)
    simpa only [he, Equiv.apply_symm_apply] using ht
  intro h i j hne
  rw [he, he]
  exact h _ _ (e.injective.ne hne)

private theorem buffer_near (d : ℝ≥0) (r : ℝ) (v : Fin n → L.Token)
    {x : Points n} (hr : 0 < r) (hx : buffer a r d (realize v x)) :
    ∀ᶠ y : Points n in 𝓝 x, buffer a (r/2) d (realize v y) := by
  have hf : r / 2 < r := by linarith
  have ht i : ∀ᶠ y : Points n in 𝓝 x, r/2 ≤ y i a ∧ y i a ≤ (d : ℝ) - r/2 := by
    have hi : (x i, v i) ∈ realize v x := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hc : ContinuousAt (fun y : Points n => y i a) x := by fun_prop
    have hh : ∀ᶠ y : Points n in 𝓝 x, y i a ∈ Ioo (r/2) ((d : ℝ) - r/2) :=
      hc (Ioo_mem_nhds (hf.trans_le (hx.2 _ hi).1)
        ((show x i a ≤ (d : ℝ) - r from (hx.2 _ hi).2).trans_lt (sub_lt_sub_left hf _)))
    exact hh.mono fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hh : spaced r x := (realize_spaced r v x).1 hx.1
  have hs i j : ∀ᶠ y : Points n in 𝓝 x, i ≠ j → r / 2 ≤ cubedist (y i) (y j) := by
    by_cases he : i = j
    · exact Eventually.of_forall fun _ hn => (hn he).elim
    have hc : ContinuousAt (fun y : Points n => cubedist (y i) (y j)) x := by fun_prop
    have he' : ∀ᶠ y : Points n in 𝓝 x, r / 2 < cubedist (y i) (y j) :=
      hc (lt_mem_nhds (hf.trans_le (hh i j he)))
    exact he'.mono fun _ hz _ => hz.le
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (hs i)),
    eventually_all.mpr ht] with y hy hty
  refine ⟨(realize_spaced _ v y).2 hy, fun p hp => ?_⟩
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
  rw [← hi]
  exact hty i

/-- The constant here may depend on the whole array of labels. At fixed width,
arity and labels, valid in a neighborhood of the given slab configuration. -/
theorem place_bound (A : Spread V) (hb : A.AllCopy) (d : ℝ≥0) (v : Fin n → L.Token)
    {x : Points n} (hx : x ∈ region a d n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y : Points n in 𝓝 x, ‖A.place d (realize v y)‖ ≤ C := by
  obtain ⟨D, R, hl, r, hr, h1, hbuf⟩ := affordable ((in_region d v x).2 hx)
  obtain ⟨C, k, hC, hh⟩ := hb D R
  have hva (y : Points n) : constrained D R (realize v y) := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    have he : (x i, v i) ∈ realize v x := List.mem_ofFn.mpr ⟨i,rfl⟩
    rw [← hi]
    exact hl (x i, v i) he
  refine ⟨C ^ n * ((n : ℝ) / (r/2)) ^ (k*n), by positivity, ?_⟩
  filter_upwards [buffer_near d r v hr hbuf, (region_open d n).mem_nhds hx] with y ht hy
  simpa only [Spread.radius, realize, List.length_ofFn] using
    hh _ d (hva y) ((in_region d v y).2 hy) (r/2) (by positivity) (by linarith) ht

end Region

variable (P : DiffPlan S) (A : Spread V) (d : ℝ≥0)

/-- Raw token after differentiating. Uses the original quotient S
(not the possibly further collapsed quotient T of the later chamber). -/
def nextToken (p : L.Token) (j : Axis) : L.Token :=
  ⟨p.1 + 1, S.representative _ (P.deriv p.1 j (S.project p.1 p.2))⟩

def nextLabels (v : Fin n → L.Token) (b : Fin n × Axis) :=
  update v b.1 (nextToken P (v b.1) b.2)

/-- In the true real Euclidean norm on Points, the finite directions
used to test kernels exhaust a basis. -/
def columns (n : ℕ) : OrthonormalBasis (Fin n × Axis) ℝ (Points n) :=
  OrthonormalBasis.ofRepr Points.flatten

theorem columns_eq (b : Fin n × Axis) :
    columns n b = Points.direction b.1 b.2 := by
  rcases b with ⟨p,a⟩
  apply Points.flatten.injective
  rw [columns, OrthonormalBasis.coe_ofRepr, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  rintro ⟨q,j⟩
  by_cases hp : q = p
  · subst q
    simp [Points.direction, PiLp.single_apply, eq_comm]
  simp [Points.direction, hp]

/-- Operator-norm derivative candidate. -/
def columnD (v : Fin n → L.Token) (x : Points n) : Points n →L[ℝ] V.GNS.H.Op :=
  ∑ b : Fin n × Axis,
    ContinuousLinearMap.smulRightL ℝ (Points n) V.GNS.H.Op (innerSL ℝ (columns n b))
      (A.place d (realize (nextLabels P v b) x))

theorem columnD_column (v : Fin n → L.Token) (x : Points n) (b : Fin n × Axis) :
    columnD P A d v x (Points.direction b.1 b.2) =
      A.place d (realize (nextLabels P v b) x) := by
  rw [← columns_eq b]
  simp [columnD, (columns n).inner_eq_ite, ite_smul]

/-- Finite local operator bound after one change of label. -/
theorem columnD_bound (hb : A.AllCopy) (v : Fin n → L.Token)
    {x : Points n} (hx : x ∈ region a d n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y : Points n in 𝓝 x, ‖columnD P A d v y‖ ≤ C := by
  have hp (b : Fin n × Axis) := place_bound A hb d (nextLabels P v b) hx
  choose k hk h using hp
  let l (b : Fin n × Axis) := ContinuousLinearMap.smulRightL ℝ (Points n) V.GNS.H.Op
    (innerSL ℝ (columns n b))
  refine ⟨∑ b : Fin n × Axis, ‖l b‖ * k b, Finset.sum_nonneg
    (fun b _ => mul_nonneg (norm_nonneg (l b)) (hk b)), ?_⟩
  filter_upwards [eventually_all.mpr h] with y hy
  let f (b : Fin n × Axis) := A.place d (realize (nextLabels P v b) y)
  calc
    ‖∑ b, l b (f b)‖ ≤ ∑ b, ‖l b (f b)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun b _ =>
      ((l b).le_opNorm (f b)).trans (mul_le_mul_of_nonneg_left (hy b) (norm_nonneg (l b)))

/-- Unpack the quotient derivative formula into one for T on raw labels. -/
theorem raw_slot (hT : T.Symmetric) (hsm : T.Smooth) (hr : T.respects S) (hder : P.Derivatives T)
    (v : Fin n → L.Token) (b : Fin n × Axis) {x : Points n} (hx : x ∈ conf n) :
    Analysis.D (Points.direction b.1 b.2) (fun y => T.read y v) x =
      T.read x (nextLabels P v b) := by
  let w := S.classTokens ∘ v
  let p := b.1
  have hs := P.derivative_slot hder hT hsm hx p w (S.project (v p).1 (v p).2) b.2
  have he : update w p (⟨(v p).1, S.project _ (v p).2⟩ : S.Tag) = w :=
    update_eq_self p w
  have ht : update w p
      (⟨(v p).1 + 1, P.deriv (v p).1 b.2 (S.project _ (v p).2)⟩ : S.Tag) =
      S.classTokens ∘ nextLabels P v b := by
    funext i
    by_cases hi : i = b.1
    · subst i
      simp only [nextLabels, Function.comp_apply, p, Function.update_self]
      change _ = (⟨(v b.1).1 + 1, S.project _ (S.representative _ _)⟩ : S.Tag)
      rw [S.rep]
    simp [w, nextLabels, p, hi]
  rw [ht, S.at_project T hT hr hx _, he] at hs
  rw [hs]
  apply Analysis.GermD
  filter_upwards [(conf_open _).mem_nhds hx] with y hy
  exact (S.at_project T hT hr hy v).symm

section Insert

variable {m : ℕ}

private def headPoints (x : Points n) (y : Points m) : Points (n + m) :=
  points (Fin.append x.ofLp y.ofLp)

private theorem realize_headPoints (v : Fin n → L.Token) (u : Fin m → L.Token)
    (x : Points n) (y : Points m) :
    realize (Fin.append v u) (headPoints x y) = realize v x ++ realize u y := by
  unfold realize
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints]

private def headL (n m : ℕ) : Points n →L[ℝ] Points (n + m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => headPoints x 0
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints]
      map_smul' := by
        intro c x
        apply PiLp.ext
        intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints] }

private theorem headPoints_deriv (x : Points n) (y : Points m) :
    HasFDerivAt (fun z : Points n => headPoints z y) (headL n m) x := by
  rw [show (fun z : Points n => headPoints z y) =
    fun z => headL n m z + headPoints (0 : Points n) y from ?eq]
  · exact (headL n m).hasFDerivAt.add_const _
  case eq =>
    funext z
    apply PiLp.ext
    intro i
    change headPoints z y i = (headPoints z (0 : Points m) + headPoints (0 : Points n) y) i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [headPoints]

private theorem headL_column (m : ℕ) (b : Fin n × Axis) :
    headL n m (Points.direction b.1 b.2) = Points.direction (Fin.castAdd m b.1) b.2 := by
  apply PiLp.ext
  intro i
  change headPoints (Points.direction b.1 b.2) (0 : Points m) i = _
  refine Fin.addCases ?_ ?_ i
  · intro j
    by_cases hj : j = b.1 <;> simp [headPoints, Points.direction, hj]
  intro j
  have h : Fin.natAdd n j ≠ Fin.castAdd m b.1 := by
    intro e
    have hv : n + j.val = b.1.val := congrArg Fin.val e
    have hb := b.1.isLt
    omega
  simp [headPoints, Points.direction, h]

private theorem nextLabels_append (v : Fin n → L.Token) (u : Fin m → L.Token) (b : Fin n × Axis) :
    nextLabels P (Fin.append v u) (Fin.castAdd m b.1, b.2) = Fin.append (nextLabels P v b) u := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    by_cases hj : j = b.1
    · subst j
      simp [nextLabels]
    simp [nextLabels, hj]
  intro j
  have h : Fin.natAdd n j ≠ Fin.castAdd m b.1 := by
    intro e
    have hv : n + j.val = b.1.val := congrArg Fin.val e
    have hb := b.1.isLt
    omega
  simp [nextLabels, h]

/-- The exterior word stays fixed as we vary the placement's positions. -/
private def exteriorWord (p q : Future L a) :=
  reflect p.val a ++ raised a d q.val

private theorem observed_placement (hT : T.Symmetric)
    (v : Fin n → L.Token) (x : Points n) (hx : x ∈ region a d n) (p q : Future L a) :
    headPoints x (positions (exteriorWord d p q)) ∈ conf _ ∧
    observe (V.GNS.plant p) (V.GNS.plant q) (A.place d (realize v x)) =
      T.read (headPoints x (positions (exteriorWord d p q))) (Fin.append v (tokens (exteriorWord d p q))) := by
  let w := exteriorWord d p q
  have hw := (in_region d v x).2 hx
  have hP : List.Perm (reflect p.val a ++ (realize v x ++ raised a d q.val)) (realize v x ++ w) := by
    dsimp only [w, exteriorWord]
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  have h := twoSides p.property (entering hw q).property
  have hz : realize (Fin.append v (tokens w)) (headPoints x (positions w)) = realize v x ++ w := by
    rw [realize_headPoints, rebuilt]
  constructor
  · apply (realized (Fin.append v (tokens w)) _).1
    change distinct (realize (Fin.append v (tokens w)) (headPoints x (positions w)))
    rw [hz, locations]
    exact (hP.map Prod.fst).nodup (locations.mp h)
  rw [observe_apply, A.reads hw, V.GNS.measure]
  change T.expect (reflect p.val a ++ (entering hw q).val) = _
  calc
    _ = T.expect (realize v x ++ w) := (T.order hT h hP).symm
    _ = _ := by rw [← hz, T.readAt]

/-- Matrix-element derivative against every pair of plants. -/
theorem plant_deriv (hT : T.Symmetric) (hsm : T.Smooth) (hr : T.respects S) (hder : P.Derivatives T)
    (v : Fin n → L.Token) (x : Points n) (hx : x ∈ region a d n) (p q : Future L a) :
    HasFDerivAt (fun y => observe (V.GNS.plant p) (V.GNS.plant q) (A.place d (realize v y)))
      ((observe (V.GNS.plant p) (V.GNS.plant q)).comp (columnD P A d v x)) x := by
  let Z := observe (V.GNS.plant p) (V.GNS.plant q)
  let w := exteriorWord d p q
  let t := Fin.append v (tokens w)
  let put (x : Points n) := headPoints x (positions w)
  let TY := fun y => T.read y t
  have hput : put x ∈ conf _ := (observed_placement A d hT v x hx p q).1
  have hs := (T.smooth_read hsm t (put x) hput).contDiffAt ((conf_open _).mem_nhds hput)
  let B := (fderiv ℝ TY (put x)).comp (headL n w.length)
  have he : HasFDerivAt (fun y : Points n => TY (put y)) B x :=
    (hs.differentiableAt (by simp)).hasFDerivAt.comp x (headPoints_deriv x (positions w))
  have hcols (b : Fin n × Axis) : B (columns n b) = Z (columnD P A d v x (columns n b)) := by
    rw [columns_eq, columnD_column]
    dsimp only [B, ContinuousLinearMap.comp_apply]
    rw [headL_column]
    have hy := raw_slot P hT hsm hr hder t (Fin.castAdd w.length b.1, b.2) hput
    change Analysis.D (Points.direction _ _) TY _ = _
    calc
      _ = T.read (put x) (nextLabels P t (Fin.castAdd w.length b.1, b.2)) := hy
      _ = T.read (put x) (Fin.append (nextLabels P v b) (tokens w)) := by
        dsimp only [t]
        rw [nextLabels_append]
      _ = _ := (observed_placement A d hT (nextLabels P v b) x hx p q).2.symm
  have hB : B = Z.comp (columnD P A d v x) := by
    ext1 y
    have heq (b : Fin n × Axis) : B (columns n b) = (Z.comp (columnD P A d v x)) (columns n b) := hcols b
    rw [← (columns n).sum_repr y, map_sum, map_sum]
    simp only [map_smul, heq]
  rw [hB] at he
  apply he.congr_of_eventuallyEq
  filter_upwards [(region_open d n).mem_nhds hx] with y hy
  exact (observed_placement A d hT v y hy p q).2

end Insert

section Regularity

private theorem columnD_contDiff {k : ℕ} (v : Fin n → L.Token)
    (h : ∀ w : Fin n → L.Token,
      ContDiffOn ℝ k (fun y => A.place d (realize w y)) (region a d n)) :
    ContDiffOn ℝ k (columnD P A d v) (region a d n) := by
  apply ContDiffOn.sum
  intro b _
  let Lb := ContinuousLinearMap.smulRightL ℝ (Points n) V.GNS.H.Op (innerSL ℝ (columns n b))
  have hc : ContDiff ℝ k Lb := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := k)
    (E := V.GNS.H.Op) (F := Points n →L[ℝ] V.GNS.H.Op) Lb
  exact hc.comp_contDiffOn (h _)

variable (ht : T.Symmetric) (hs : T.Smooth) (hr : T.respects S) (hD : P.Derivatives T)
variable (hb : A.AllCopy)
include P ht hs hr hD hb

theorem cont_place (v : Fin n → L.Token) {x : Points n} (hx : x ∈ region a d n) :
    ContinuousAt (fun y => A.place d (realize v y)) x := by
  obtain ⟨C, hC, hc⟩ := columnD_bound P A d hb v hx
  apply continuousAt_of_plant_derivs V.GNS _ hC hc
  filter_upwards [(region_open d n).mem_nhds hx] with z hz
  exact plant_deriv P A d ht hs hr hD v z hz

theorem deriv_place (v : Fin n → L.Token) {x : Points n} (hx : x ∈ region a d n) :
    HasFDerivAt (fun y => A.place d (realize v y)) (columnD P A d v x) x := by
  have hc : ContinuousOn (columnD P A d v) (region a d n) := by
    have hh := columnD_contDiff P A d (k := 0) v fun w =>
      contDiffOn_zero.mpr fun y hy => (cont_place P A d ht hs hr hD hb w hy).continuousWithinAt
    exact hh.continuousOn
  apply hasFDerivAt_of_plant_derivs V.GNS _ (hc.continuousAt ((region_open d n).mem_nhds hx))
  filter_upwards [(region_open d n).mem_nhds hx] with z hz
  exact plant_deriv P A d ht hs hr hD v z hz

theorem smooth_place (v : Fin n → L.Token) :
    ContDiffOn ℝ ∞ (fun y => A.place d (realize v y)) (region a d n) := by
  apply contDiffOn_infty.mpr
  intro k
  induction k generalizing v with
  | zero =>
    exact contDiffOn_zero.mpr fun x hx =>
      (cont_place P A d ht hs hr hD hb v hx).continuousWithinAt
  | succ k ih =>
    push_cast
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (region_open d n)).mpr
    have he (x : Points n) (hx : x ∈ region a d n) := deriv_place P A d ht hs hr hD hb v hx
    exact ⟨fun x hx => (he x hx).differentiableAt.differentiableWithinAt, by simp,
      (columnD_contDiff P A d v ih).congr (fun x hx => (he x hx).fderiv)⟩

end Regularity
end YM.Work.B02
