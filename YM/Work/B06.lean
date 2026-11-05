import YM.Bid.Phase

/-!
# Individual invariance of M, with phase reflection as input

Use long-train *pairs* (Ground.same_up, coming from S covariance and time order).
With individual time reflection, simultaneous pair invariance holds on full O.
It lets us conjugate individual time reflection to individual invariance under
any reflection, first in pair stages, then as operators using the adjoint tests
and separation by omega. Thus no need for the power/bounded-extension argument
to handle time-space rotations separately.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.B06
open OS OS.Ground Org Bid Table Word
open scoped Topology NNReal InnerProductSpace ContDiff

section geometry
open Submodule

-- reflection in a hyperplane normal to v (identity when v = 0)
private def hyper (v : E4) : E4 ≃ₗᵢ[ℝ] E4 := (ℝ ∙ v)ᗮ.reflection
private abbrev theta := Signed.reflect timeAxis

private lemma theta_move (x : E4) : Ortho.move theta x = hyper (basis timeAxis) x := by
  rw [hyper, reflection_orthogonal_apply, reflection_singleton_apply]
  ext i
  by_cases h : i = timeAxis
  · subst i
    simp [theta, two_smul]
  simp [theta, h, two_smul]

private lemma conj_hyper (v : E4) (hv : v ≠ 0) :
    ∃ J : Ortho, ∀ x, Ortho.move (J * theta * J⁻¹) x = hyper v x := by
  let b := basis timeAxis
  let u := ‖v‖⁻¹ • v
  have hu : ‖b‖ = ‖u‖ := by simp [b, u, norm_smul, hv]
  obtain ⟨J, hJ⟩ := Ground.columns (hyper (b-u))
  let f := Ortho.motion J
  have hf : f b = u := by change Ortho.move J b = _; rw [hJ]; exact reflection_sub hu
  have hmap : (ℝ ∙ b)ᗮ.map (f.toLinearEquiv : E4 →ₗ[ℝ] E4) = (ℝ ∙ v)ᗮ := by
    rw [map_orthogonal_equiv, Submodule.map_span, Set.image_singleton]
    change (ℝ ∙ f b)ᗮ = _
    rw [hf, show ℝ ∙ u = ℝ ∙ v from span_singleton_smul_eq (by simp [hv]) _]
  refine ⟨J, fun x => ?_⟩
  simp only [Ortho.move_mul, theta_move]
  change f (hyper b (f.symm x)) = _
  rw [hyper, ← reflection_map_apply f]
  exact congr_arg (fun W : Submodule ℝ E4 => W.reflection x) hmap

private lemma theta_generates (W : Ortho → Prop) (hi : W 1)
    (hm : ∀ j k, W j → W k → W (j*k)) (hc : ∀ j : Ortho, W (j * theta * j⁻¹)) (k : Ortho) : W k := by
  have single (v : E4) : ∃ J : Ortho, W J ∧ ∀ x, Ortho.move J x = hyper v x := by
    rcases eq_or_ne v 0 with e|e
    · subst v
      exact ⟨1, hi, fun x => by rw [Ortho.move_one, hyper, reflection_orthogonal_apply,
        reflection_singleton_apply]; simp⟩
    obtain ⟨J,hJ⟩ := conj_hyper v e
    exact ⟨_, hc J, hJ⟩
  have chain (l : List E4) : ∃ J : Ortho, W J ∧ ∀ x, Ortho.move J x = (l.map hyper).prod x := by
    induction l with
    | nil => exact ⟨1,hi,fun x => (Ortho.move_one x)⟩
    | cons v l ih =>
      obtain ⟨A,hA,ha⟩ := single v
      obtain ⟨B,hB,hb⟩ := ih
      exact ⟨A*B, hm A B hA hB, fun x => by rw [Ortho.move_mul, hb, ha]; rfl⟩
  obtain ⟨l, -, hl⟩ := (Ortho.motion k).reflections_generate_dim
  obtain ⟨J, hJ, hf⟩ := chain l
  have e : k = J := Ortho.ext _ _ (fun x => by rw [hf]; exact congr_arg (fun f : E4 ≃ₗᵢ[ℝ] E4 => f x) hl)
  exact e.symm ▸ hJ
end geometry

section stages
variable {G : Gauge} {C : Family G} {S : Table C.book}
    {V : Chamber S timeAxis} (A : Spread V) (T : Rotation S)
    {P : DiffPlan S} (H : S.Hierarchy) (o : T.Oriented S) (law : T.Laws P H.spin)
    (B : Theme V A) (st : Steady V) (hr : Phase.reflects (C:=C) V A)

private abbrev m (x : Row.Core C.book) : A.algebra := M A x.val x.property
private def individually (k : Ortho) := ∀ x : Row.Core C.book, m A x = m A (orbit H T o k x)

-- Composition works exactly (projection of the chosen representative gives the tag).
-- The identity need not act by the identity before projecting labels.
include law in
private lemma orbit_comp (j k : Ortho) (x : Row.Core C.book) :
    orbit H T o j (orbit H T o k x) = orbit H T o (j*k) x := by
  apply Subtype.ext
  change Ground.rotate (Ground.rotate _ T k) T j = _
  unfold orbit Ground.rotate
  dsimp only
  rw [List.map_map]
  have h (p : S.Tag) : T.label j (T.label k p) = T.label (j*k) p := by
    unfold Rotation.label; rw [law.group]
  simp only [Function.comp_def, Ward.sends_back, h, Ortho.move_mul]

include law B in
private lemma raw_signed (s : Signed) (w : Row.Core C.book) (ha : distinct (Word.act s w.val)) :
    M A (Word.act s w.val) ha = m A (orbit H T o s.ortho w) := by
  let v := Word.tokens w.val
  let p : Caps w.val.length := fun i => (v i).1
  let x := Points.move s.ortho (positions w.val)
  have hx : x ∈ conf _ := Points.move_in _ w.property
  let a : C.book.Vector p := fun i => C.book.mirrorGroup _ s (v i).2
  let b : C.book.Vector p := fun i => S.representative _ (T.act _ s.ortho (S.project _ (v i).2))
  have h (i : Fin w.val.length) : S.project _ (a i) = S.project _ (b i) := by
    dsimp only [a, b]
    rw [S.rep, law.signed, S.mirror_project]
  let fitted (u : C.book.Vector p) : Row.Core C.book :=
    ⟨realize (fun i => ⟨p i,u i⟩) x, (realized _ _).mpr hx⟩
  have he : m A (fitted a) = m A (fitted b) := by
    have he := B.pins w.val.length p x a b h
    unfold depot at he
    rw [dif_pos hx,dif_pos hx] at he
    exact he
  have e₁ : fitted a = (⟨_,ha⟩ : Row.Core _) := by
    apply Subtype.ext; change Word.realize _ x = List.map _ w.val
    conv_rhs => rhs; rw [← List.ofFn_get w.val]
    rw [List.map_ofFn]; rfl
  have e₂ : fitted b = orbit H T o s.ortho w := by
    apply Subtype.ext; change Word.realize _ x = List.map _ w.val
    conv_rhs => rhs; rw [← List.ofFn_get w.val]
    rw [List.map_ofFn]; rfl
  rw [e₁, e₂] at he
  exact he

include law in
private lemma product_individual (j k : Ortho) (hj : individually A T H o j)
    (hk : individually A T H o k) : individually A T H o (j*k) := by
  intro x
  exact (hk x).trans ((hj _).trans (congr_arg (m A) (orbit_comp T H o law j k x)))

include law B hr in
private lemma theta_individual : individually A T H o theta := by
  intro w
  have h := hr w.val w.property
  exact h.trans (raw_signed A T H o law B (Signed.mirror timeAxis) w _)

include law B hr in
private lemma one_individual : individually A T H o 1 := by
  have hh := theta_individual A T H o law B hr
  have hθ : theta * theta = 1 := Ortho.ext _ _ (fun x => by
    rw [Ortho.move_one, Ortho.move_mul]; ext i; by_cases e : i = timeAxis <;> simp [theta, e])
  exact hθ ▸ product_individual A T H o law theta theta hh hh

private lemma pair_form (x y : Row.Core C.book) : stage A [x,y] =
    inner ℂ V.omega0 ((m A x).val ((m A y).val V.omega0)) := by
  simp only [stage, starU, List.prod_cons, List.map_cons, List.map_nil, List.prod_nil, mul_one]
  rfl

private lemma pair_congr {p q x y : Row.Core C.book} (he : m A p = m A q) (hf : m A x = m A y) :
    stage A [p,x] = stage A [q,y] := by rw [pair_form, pair_form, he, hf]

include law B st hr in
private lemma pair_orbit (k : Ortho) (p x : Row.Core C.book) :
    stage A [p,x] = stage A [orbit H T o k p, orbit H T o k x] := by
  let t := timeAxis
  let b := basis t
  have hb : 0 < b t := by simp [b]
  -- Need a common increasing time direction for same_up. Include equator;
  -- when time coefficient is negative first compose with theta.
  rcases lt_trichotomy 0 (Ortho.move k b t) with h|e|h
  · exact same_up A st H T o k b hb h [p,x]
  · let u := Ortho.move k⁻¹ b
    have hu : u t = 0 := by
      have h₁ := (Ortho.motion k).inner_map_map u b
      change inner ℝ (Ortho.move k (Ortho.move k⁻¹ b)) (Ortho.move k b) = inner ℝ u b at h₁
      rw [Ortho.move_inv, ← real_inner_comm u b] at h₁
      change inner ℝ (basis t) _ = inner ℝ (basis t) _ at h₁
      rw [basis_inner, basis_inner] at h₁
      exact h₁.symm.trans e.symm
    have he : 0 < (b+u) t := by simp [hu, hb]
    have hv : 0 < Ortho.move k (b+u) t := by
      rw [(show Ortho.move k (b+u) = Ortho.move k b + Ortho.move k u from
        (Ortho.motion k).map_add ..)]
      simp [u, e.symm, hb]
    exact same_up A st H T o k (b+u) he hv [p,x]
  have hv : 0 < Ortho.move (theta*k) b t := by
    simp only [Ortho.move_mul, theta, Signed.mirrored, show timeAxis = t from rfl, if_true]
    exact neg_pos.mpr h
  have hf (x : Row.Core C.book) : m A (orbit H T o (theta*k) x) = m A (orbit H T o k x) := by
    rw [← orbit_comp T H o law]
    exact (theta_individual A T H o law B hr _).symm
  calc
    _ = stage A [orbit H T o (theta*k) p, orbit H T o (theta*k) x] :=
      same_up A st H T o (theta*k) b hb hv [p,x]
    _ = _ := pair_congr A (hf p) (hf x)

-- Rotate a pair back; apply theta invariance to the second factor ONLY;
-- rotate forward again. Avoid an auxiliary operator representing rotations.
include law B st hr in
private lemma second_conjugate (j : Ortho) (p x : Row.Core C.book) :
    stage A [p,x] = stage A [p, orbit H T o (j*theta*j⁻¹) x] := by
  let a := orbit H T o j⁻¹ p
  let b := orbit H T o j⁻¹ x
  let c := orbit H T o theta b
  have ha : orbit H T o j a = orbit H T o 1 p := by
    dsimp only [a]; rw [orbit_comp T H o law, mul_inv_cancel]
  have hc : orbit H T o j c = orbit H T o (j*theta*j⁻¹) x := by
    dsimp only [c, b]
    rw [orbit_comp T H o law, orbit_comp T H o law]
  calc
    _ = stage A [a,b] := pair_orbit A T H o law B st hr j⁻¹ p x
    _ = stage A [a,c] := pair_congr A rfl (theta_individual A T H o law B hr b)
    _ = stage A [orbit H T o j a, orbit H T o j c] :=
      pair_orbit A T H o law B st hr j a c
    _ = _ := pair_congr A ((congr_arg (m A) ha).trans
      (one_individual A T H o law B hr p).symm) (congr_arg (m A) hc)

-- Pair stages separate individual M's. For the left test Word.reflect (not theta alone)
-- is the adjoint test. Omega is separating by Ground.adjunction + Ground.attains.
include B st T H o in
private lemma by_pairs (x y : Row.Core C.book) (h : ∀ p : Row.Core C.book, stage A [p,x] = stage A [p,y]) :
    m A x = m A y := by
  let v := fun p : Row.Core C.book => (m A p).val V.omega0
  let ref := fun p : Row.Core C.book =>
    (⟨reflect p.val timeAxis, Word.reflects timeAxis p.property⟩ : Row.Core C.book)
  have hf (p q : Row.Core C.book) : stage A [ref p,q] = inner ℂ (v p) (v q) := by
    have hr : m A (ref p) = star (m A p) := (B.opposite p.val p.property _).symm
    rw [pair_form, hr]
    exact ContinuousLinearMap.adjoint_inner_right (m A p).val V.omega0 (v q)
  have he (p : Row.Core C.book) : inner ℂ (v p) (v x - v y) = 0 := by
    rw [inner_sub_right, ← hf, ← hf, h, sub_self]
  have hh : v x - v y = 0 := inner_self_eq_zero (𝕜:=ℂ) |>.mp (by rw [inner_sub_left, he, he, sub_self])
  apply sub_eq_zero.mp
  apply attains A (adjunction A st H T o) st
  exact hh

include law B st hr in
private lemma conjugate_individual (j : Ortho) : individually A T H o (j*theta*j⁻¹) := by
  intro x
  apply by_pairs A T H o B st
  exact fun p => second_conjugate A T H o law B st hr j p x
end stages

theorem answer : YM.Bid.B06 := by
  intro G C S V A T P H o law B st hr k w h p
  have hk := theta_generates (individually A T H o) (one_individual A T H o law B hr)
    (product_individual A T H o law) (conjugate_individual A T H o law B st hr) k
  exact hk (⟨w,h⟩ : Row.Core _)

end YM.Work.B06
