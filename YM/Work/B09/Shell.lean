import YM.Work.B09.Core

/-!
# Stress laws through character evaluation

Use the fixed width and position even for integrated shell operators. The
operator comparison with arbitrary word spectators is translated back to the
actual window; in this comparison there are extra spectators both below and
above the slab. Keep them outside the whole χ, not just outside the support
of its derivative. As in `YM/Euclid/Window` for the number kernels, check
integrability also for the operators -- points near potential collisions
are actually killed by the shell weight.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.B09
open Set Filter Function Analysis OS Word MeasureTheory
open scoped Topology ContDiff NNReal InnerProductSpace BigOperators

variable {G : Gauge} {L : Register G} {S T : Table L} {V : Chamber S timeAxis} {A : Spread V}
variable {P : DiffPlan S} {φ : V.H.Op →L[ℂ] ℂ}
variable {s : E4} {D : ℝ≥0} {χ : E4 → ℝ}

section
variable {n : ℕ} {x : Points (n+1)} (l r : Future L timeAxis) (q : Fin n → S.Tag)

lemma window_extends (hw : Table.Window x χ) (ht : ∀ y ∈ tsupport χ, InsideTimes s D y) :
    Table.Window (Points.cons (x 0) (positions (spectators s D x q l r))) χ := by
  let v := spectators s D x q l r
  have hv (p) (hp : p∈v) : p.1 ∉ tsupport χ := by
    rcases List.mem_append.mp hp with h|h
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
      exact hw.2.2.2 i
    exact fun hy => exterior_not_inside l r h (ht _ hy)
  exact ⟨hw.1, hw.2.1, hw.2.2.1, fun i => hv (v.get i) (List.get_mem ..)⟩

lemma matrix_on_shell (H : S.Hierarchy) (u t : S.Tag) (y : E4) (h : Padded s D (Points.cons y x)) :
    let v := spectators s D x q l r
    tester V l r (middle A s D (Fin.cons u (Fin.cons t q)) (Points.cons y x)) =
    S.useAt S (Points.cons y (Points.cons (x 0) (positions v)))
      (Fin.cons u (Fin.cons t (S.classTokens ∘ tokens v))) := by
  let v := spectators s D x q l r
  have hh := (matrix_at_center (A := A) H h (Fin.cons t q) l r u).2
  have hs : Points.tail (Points.cons y x) = x := by ext1 i; simp [Points.tail, Points.cons]
  have he : spectators s D (Points.cons y x) (Fin.cons t q) l r = (x 0,Ward.expose t)::v := by
    rw [spectators, hs, realize_head]; rfl
  rw [he, show positions ((x 0,Ward.expose t)::v) = Points.cons (x 0) (positions v) by
    ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons, positions]] at hh
  have hu : S.classTokens ∘ tokens ((x 0,Ward.expose t)::v) =
      Fin.cons t (S.classTokens ∘ tokens v) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Ward.sends_back t
    simp [tokens]
  rw [hu] at hh
  exact hh

end

section
variable {n : ℕ} {x : Points (n+1)} {y : E4} {u : E4 → ℂ} {a : Axis}

def weight (χ : E4 → ℝ) (a : Axis) (u : E4 → ℂ) (y : E4) : ℂ :=
  ((Analysis.D (basis a) χ y : ℝ) : ℂ) * u y

lemma weight_vanish {p : ℝ} (h : χ =ᶠ[𝓝 y] fun _ => p) : y ∉ tsupport (weight χ a u) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [h.fderiv (𝕜 := ℝ)] with i hi
  simp [weight, Analysis.D, hi]

lemma weight_within : tsupport (weight χ a u) ⊆ tsupport χ := by
  intro y hy
  by_contra he
  exact weight_vanish (u := u)
    (show χ =ᶠ[𝓝 y] fun _ => 0 from notMem_tsupport_iff_eventuallyEq.mp he) hy

lemma padded_shell (h : Table.Window x χ) (hx : Padded s D x)
    (hh : ∀ y ∈ tsupport χ, InsideTimes s D y) (hy : y ∈ tsupport (weight χ a u)) :
    Padded s D (Points.cons y x) := by
  have hd (i : Fin (n+1)) : y ≠ x i := by
    intro hi
    rw [hi] at hy
    refine Fin.cases ?_ (fun j => ?_) i hy
    · exact weight_vanish h.2.2.1
    exact fun hp => h.2.2.2 j (weight_within hp)
  refine ⟨hx.1, ?_, fun i => Fin.cases (hh y (weight_within hy)) (fun j => ?_) i⟩
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases (fun _ => rfl) (fun k => ?_) j
      simp [Points.cons, hd]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [Points.cons, Ne.symm (hd i)]
    simp only [Points.cons, points_apply, Fin.cons_succ]
    exact fun H => congr_arg Fin.succ ((show Injective x.ofLp from hx.2.1) H)
  · simpa only [Points.cons, points_apply, Fin.cons_succ] using hx.2.2 j

lemma shell_integrable (h : Table.Window x χ) (hc : Continuous u) (a : Axis) (hx : Padded s D x)
    (hh : ∀ y ∈ tsupport χ, InsideTimes s D y) (q : Fin (n+2) → S.Tag) (hp : A.Laws P) :
    Integrable (fun y => weight χ a u y • middle A s D q (Points.cons y x)) := by
  let f (y : E4) := weight χ a u y • middle A s D q (Points.cons y x)
  change Integrable f
  have hK : HasCompactSupport f := by
    apply HasCompactSupport.intro h.2.1
    intro y hy
    have he : y ∉ tsupport (weight χ a u) := fun w => hy (weight_within w)
    dsimp only [f]
    rw [image_eq_zero_of_notMem_tsupport he, zero_smul]
  refine Continuous.integrable_of_hasCompactSupport ?_ hK
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases he : y ∈ tsupport (weight χ a u)
  · have hd := middle_diff (padded_shell h hx hh he) q hp
    have hc' : Continuous (fun w : E4 => Points.cons w x) := by
      have H1 : Continuous (fun w : E4 => (Fin.cons (α := fun _ : Fin (n+2) => E4) w x.ofLp)) :=
        continuous_pi fun k => Fin.cases (by simp; exact continuous_id) (fun j => by simp; exact continuous_const) k
      exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.comp H1
    have hD := (dSmooth (h.1.contDiffAt (x := y)) (basis a) (m := ∞) (by simp)).continuousAt
    exact ((Complex.continuous_ofReal.continuousAt.comp hD).mul hc.continuousAt).smul
      (hd.continuousAt.comp (f := fun w : E4 => Points.cons w x) hc'.continuousAt)
  · exact continuousAt_const.congr (show (fun _ : E4 => (0:V.H.Op)) =ᶠ[𝓝 y] f from by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp he] with i hi
      simp [f, hi])

/-- Move a fixed evaluation (matrix-element, or character evaluator) through
 the integrated operator-valued insertion. Need agreement with the proposed
 numerical kernel only on valid shifted configurations. -/
def integrated (A : Spread V) (χ : E4 → ℝ) (a : Axis) (u : E4 → ℂ) (s : E4) (D : ℝ≥0)
    (q : Fin (n+2) → S.Tag) (x : Points (n+1)) : V.H.Op :=
  ∫ y : E4, weight χ a u y • middle A s D q (Points.cons y x)

lemma pushed (h : Table.Window x χ) (hc : Continuous u) (hx : Padded s D x)
    (hh : ∀ y ∈ tsupport χ, InsideTimes s D y) (q : Fin (n+2) → S.Tag) (hp : A.Laws P)
    (f : V.H.Op →L[ℂ] ℂ) {k : E4 → ℂ} (he : ∀ y, Padded s D (Points.cons y x) →
      f (middle A s D q (Points.cons y x)) = k y) :
    f (integrated A χ a u s D q x) = ∫ y, weight χ a u y * k y := by
  rw [integrated, ← f.integral_comp_comm (shell_integrable h hc a hx hh q hp)]
  apply integral_congr_ae
  filter_upwards with y
  rw [map_smul, smul_eq_mul]
  by_cases ht : y ∈ tsupport (weight χ a u)
  · rw [he y (padded_shell h hx hh ht)]
  simp [image_eq_zero_of_notMem_tsupport ht]

end

theorem Evaluates.flux (he : Evaluates T A φ) (hp : A.Laws P) (H : S.Hierarchy)
    {J : S.Stress} {Y Z} (hs : Table.StressLaws S J Y Z) : Table.StressLaws T J Y Z := by
  constructor
  · intro n x hx q χ hw b d B
    obtain ⟨s, D, ht, hχ⟩ := exists_padded hx hw.2.1
    let t : S.Tag := ⟨d,B⟩
    let v : S.Tag := ⟨d+1, Y d b B⟩
    let U (a : Axis) := integrated A χ a (fun _ => 1) s D
      (Fin.cons ⟨4,J a b⟩ (Fin.cons t q)) x
    have hOp : - (∑ a : Axis, U a) = middle A s D (Fin.cons v q) x := by
      apply tester_ext
      intro l r
      let E := spectators s D x q l r
      let x' := Points.cons (x 0) (positions E)
      let q' := S.classTokens ∘ tokens E
      have hU (a : Axis) : tester V l r (U a) = ∫ y,
          ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
            S.useAt S (Points.cons y x') (Fin.cons ⟨4,J a b⟩ (Fin.cons t q')) := by
        have ha := pushed (a := a) (A := A) (u := fun _ => 1) hw continuous_const ht hχ _ hp
          (tester V l r) (k := fun y => S.useAt S (Points.cons y x') (Fin.cons ⟨4,J a b⟩ (Fin.cons t q')))
          (matrix_on_shell l r q H ⟨4,J a b⟩ t)
        simpa only [weight, mul_one] using ha
      have hh := matrix_at_center (A := A) H ht q l r v
      rw [map_neg, map_sum, hh.2]
      simp_rw [hU]
      exact hs.translation hh.1 q' (window_extends l r q hw hχ) b d B
    have hU (a : Axis) : φ (U a) = ∫ y, ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
        S.useAt T (Points.cons y x) (Fin.cons ⟨4,J a b⟩ (Fin.cons t q)) := by
      simpa only [weight, mul_one] using
        (pushed (a := a) (u := fun _ => 1) hw continuous_const ht hχ
          (Fin.cons ⟨4,J a b⟩ (Fin.cons t q)) hp φ (fun _ h => (he h _).symm))
    rw [he ht, ← hOp, map_neg, map_sum]
    simp_rw [hU]; rfl
  · intro n x hx q χ hw g d B
    obtain ⟨s, D, ht, hχ⟩ := exists_padded hx hw.2.1
    let t : S.Tag := ⟨d,B⟩
    let v : S.Tag := ⟨d, Z d g B⟩
    let u (b : Axis) (y : E4) := ((M4.move g.val (y - x 0) b : ℝ) : ℂ)
    have hc (b) : Continuous (u b) := by
      unfold u
      simp_rw [M4.at_coord]
      fun_prop
    let U (a b : Axis) := integrated A χ a (u b) s D
      (Fin.cons ⟨4,J a b⟩ (Fin.cons t q)) x
    have hOp : - (∑ a : Axis, ∑ b : Axis, U a b) = middle A s D (Fin.cons v q) x := by
      apply tester_ext
      intro l r
      let E := spectators s D x q l r
      let x' := Points.cons (x 0) (positions E)
      let q' := S.classTokens ∘ tokens E
      have hU (a b : Axis) : tester V l r (U a b) = ∫ y,
          ((Analysis.D (basis a) χ y * M4.move g.val (y - x 0) b : ℝ) : ℂ) *
            S.useAt S (Points.cons y x') (Fin.cons ⟨4,J a b⟩ (Fin.cons t q')) := by
        have ha := pushed (a := a) (A := A) hw (hc b) ht hχ _ hp
          (tester V l r) (k := fun y => S.useAt S (Points.cons y x') (Fin.cons ⟨4,J a b⟩ (Fin.cons t q')))
          (matrix_on_shell l r q H ⟨4,J a b⟩ t)
        simpa only [weight, u, U, Complex.ofReal_mul] using ha
      have hh := matrix_at_center (A := A) H ht q l r v
      rw [hh.2]
      simp_rw [map_neg, map_sum, hU]
      exact hs.rotation hh.1 q' (window_extends l r q hw hχ) g d B
    have hU (a b : Axis) : φ (U a b) = ∫ y,
        ((Analysis.D (basis a) χ y * M4.move g.val (y - x 0) b : ℝ) : ℂ) *
          S.useAt T (Points.cons y x) (Fin.cons ⟨4,J a b⟩ (Fin.cons t q)) := by
      simpa only [weight, u, U, Complex.ofReal_mul] using
        (pushed (a := a) hw (hc b) ht hχ (Fin.cons ⟨4,J a b⟩ (Fin.cons t q)) hp φ
          (fun _ h => (he h _).symm))
    rw [he ht, ← hOp]
    simp_rw [map_neg, map_sum, hU]; rfl

end YM.Work.B09
