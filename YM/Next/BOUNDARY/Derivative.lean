import YM.EveryPhase.DerivativeHelpers

/-!
# Don't lose the differential system at Wick rotation

Compatibility consumer, using the common input and the *actual*
realizations. Establish analytic continuation of the Euclidean derivative
identities to the full tube, distribution derivative identity on the
Schwartz boundary, and operator identity on the field-word domain. In
particular the stated adjoint and spacelike commutation laws for the fields on
the word domain can be used coherently even when using a known `DiffPlan`
(raising the degree), and there is a conservation identity on that domain. No
claim of commutation on extended domains (adjoints etc.). This is not an assumption of Ward identities
on the Lorentz side. Do not infer Euclidean contact identities *on*
coincidence sets.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY
open Set Filter Function MeasureTheory Complex Analysis
open Boundary OS Spec Org
open Work.C20
open scoped Topology InnerProductSpace BigOperators ContDiff LineDeriv

variable {G : Gauge} {L : Register G} {n : ℕ}

/-- Euclidean time derivative analytically rotates with **plus** i on
field correlations. Will put **minus i** on test functions. -/
def wick (a : Axis) : ℂ := if a=timeAxis then I else 1
lemma wick_ne_zero (a : Axis) : wick a≠0 := by unfold wick; split <;> simp

def realPartL (n : ℕ) : Points n →L[ℝ] Full n := LinearMap.toContinuousLinearMap
  { toFun := fun x => glow x 0
    map_add' := fun x y => by ext1 i; simp [glow]
    map_smul' := fun c x => by ext1 i; simp [glow, real_smul] }

theorem wick_dir (i : Fin n) (a : Axis) :
    wickSlice n (Points.direction i a) = wick a • realPartL n (Points.direction i a) := by
  ext1 j
  rcases j with ⟨j,b⟩
  change (wickSlice n _ : Full n) (j,b) = wick a * glow _ 0 (j,b)
  rw [wick_apply]
  by_cases h : j=i
  · subst j
    by_cases hb : b=a <;> simp [Points.direction, glow, wick, hb]
  simp [Points.direction, glow, h]

private theorem real_movement (x y : Points n) :
    HasFDerivAt (fun x => glow x y) (realPartL n) x := by
  have hp : (fun x : Points n => glow x y) = fun x => realPartL n x + glow 0 y := by
    funext z
    ext1 i
    change glow z y i=glow z 0 i + glow 0 y i
    simp [glow]
  rw [hp]
  exact (realPartL n).hasFDerivAt.add_const _

private lemma inside_convex : Convex ℝ Mink.inside := by
  intro x hx y hy c d hc hd h
  change ‖spatial _‖<time _
  simp only [Mink.clock_add, Mink.rest_add, Mink.clock_mul, Mink.rest_mul]
  refine lt_of_le_of_lt (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hd]
  rcases hc.eq_or_lt with e|e
  · have hh : 0<d := by linarith
    rw [← e, zero_mul, zero_mul, zero_add, zero_add]; exact mul_lt_mul_of_pos_left hy hh
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx e) (mul_le_mul_of_nonneg_left hy.le hd)

private def shadeL (n : ℕ) : Full n →ₗ[ℝ] Points n where
  toFun := shade
  map_add' := by intro x y; ext i j; change ((x+y) (i,j)).im=(x (i,j)).im+(y (i,j)).im; simp
  map_smul' := by
    intro c x
    ext i j
    change ((c • x) (i,j)).im=c*(x (i,j)).im
    simp [real_smul]

private theorem tube_connected (n : ℕ) : IsPreconnected (tube n) := by
  have h : Convex ℝ (fields n) := by
    apply convex_iInter
    intro i
    refine convex_iInter fun j => convex_iInter fun _ => ?_
    exact inside_convex.linear_preimage
      ((PiLp.projₗ (𝕜:=ℝ) 2 (fun _ : Fin n => E4) j)-(PiLp.projₗ (𝕜:=ℝ) 2 (fun _ : Fin n => E4) i))
  exact (h.linear_preimage (shadeL n)).isPreconnected

theorem emit_root {S T : Table L} {F : Waves S} {Y : Surface S}
    {D : ∀ n, Blanket n} {Z : Y.Aurora D} (hT : F.Region T) (hF : Z.FullBody F)
    (w : Fin n → S.Tag) {q : Points n} (h : q∈Work.C20.ordered n) :
    Z.emit (Bid.ink w) (wickSlice n q)=S.useAt T q w := by
  let t := Boundary.trace q
  have hy : readings q ∈ east n := h
  have hspace : Boundary.trace (place t 0) = t := by funext i; simp [Boundary.trace, place, t]
  have htime : shift (place t 0) (readings q) = (fun i => (readings q i : ℂ)*I) := by
    funext i
    simp [shift, place]
  rw [wick_glow, hF.pure n _ _ _ hy, Waves.restricted, htime, hspace, show F.F n _ _ (Bid.ink w) = _ from
    hT.roots n w _ _ hy]
  congr 1
  exact place_same _

variable {S T : Table L}
variable {D : ∀ n, Blanket n} {W : Surface S} {F : Waves S} {Z : W.Aurora D}

/-- Full-tube identity for a derivative in one slot, with common labels. -/
theorem field_jet (P : DiffPlan S) (ht : T.Hierarchy) (hs : S.Symmetric)
    (hv : P.Inclusions S) (hu : P.Derivatives T) (hF : F.Region T) (hZ : Z.FullBody F)
    (v : Fin n → S.Union) (i : Fin n) (a : Axis) (d : ℕ) (t : S.Field d) :
    EqOn (Z.emit (update v i (S.pin (d+1) (P.deriv d a t))))
      (fun p => fderiv ℂ (Z.emit (update v i (S.pin d t))) p (wickSlice n (Points.direction i a)))
      (tube n) := by
  obtain ⟨e, E, he⟩ := P.joint hs hv v
  let w : Fin n → S.Tag := fun j => ⟨e,E j⟩
  let u := update v i (S.pin d t)
  let r := update v i (S.pin (d+1) (P.deriv d a t))
  let x : Fin n → S.Tag := update w i ⟨d,t⟩
  let y : Fin n → S.Tag := update w i ⟨d+1,P.deriv d a t⟩
  have h (t : S.Tag) : Bid.ink (update w i t) = update v i (S.pin t.1 t.2) := by
    funext j
    by_cases e : j=i
    · subst j
      unfold Bid.ink
      rw [update_self, update_self]
    unfold Bid.ink
    rw [update_of_ne e, update_of_ne e, he]
    rfl
  let A := wickSlice n
  let g (p : Full n) := fderiv ℂ (Z.emit u) p (A (Points.direction i a))
  have hp (q) (hq : q∈ordered n) : Z.emit r (A q)=g (A q) := by
    have hf : Z.emit u ∘ A =ᶠ[𝓝 q] (fun b => S.useAt T b x) := by
      filter_upwards [(ordered_open n).mem_nhds hq] with j hj
      change Z.emit u _=_
      rw [show u=Bid.ink x from (h (⟨d,t⟩ : S.Tag)).symm]
      exact emit_root hF hZ _ hj
    rw [show r=Bid.ink y from (h (⟨d+1,P.deriv d a t⟩ : S.Tag)).symm, emit_root hF hZ y hq]
    have heq : q∈conf n := place_same q ▸ clear (show readings q∈east n from hq) (Boundary.trace q)
    rw [show S.useAt T q y=_ from P.derivative_slot hu ht.laws.toSymmetric ht.smooth heq i w t a]
    change Analysis.D (Points.direction i a) (fun b => S.useAt T b x) q=g _
    rw [GermD _ hf.symm]
    have hh := hZ.hol n u (A q) (wick_tube hq)
    rw [Analysis.D, ((hh.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp _ A.hasFDerivAt).fderiv]
    rfl
  have ha : AnalyticOnNhd ℂ g (tube n) := fun p hq =>
    ((ContinuousLinearMap.apply ℂ ℂ (A (Points.direction i a))).analyticAt _).comp ((hZ.hol n u p hq).fderiv)
  have hb := hZ.hol n r
  let q := place 0 (rate n)
  have hQ : q∈ordered n := by
    change readings q∈east n
    unfold q; rw [readings_place]
    intro i j hij
    unfold rate
    exact_mod_cast hij
  have hm : A q∈tube n := wick_tube hQ
  apply hb.eqOn_of_preconnected_of_eventuallyEq ha (tube_connected n) hm
  apply Work.C20.complex_germ (M:=A) (hb _ hm) (ha _ hm) (Work.C20.wick_span n)
  intro j
  have heq : Z.emit r ∘ A =ᶠ[𝓝 q] g ∘ A := by
    filter_upwards [(ordered_open n).mem_nhds hQ] with p h using hp p h
  exact (heq.iteratedFDeriv ℝ j).eq_of_nhds

def testAxis (i : Fin n) (a : Axis) (f : Joint n) : Joint n :=
    (-wick a) • (∂_{Points.direction i a} f)

/-- Distribution identity even at all fixed strictly interior shifts. -/
theorem inserted_jet (P : DiffPlan S) (ht : T.Hierarchy) (hs : S.Symmetric)
    (hv : P.Inclusions S) (hu : P.Derivatives T) (hF : F.Region T) (hZ : Z.FullBody F)
    (v : Fin n → S.Union) (i : Fin n) (a : Axis) (d : ℕ) (t : S.Field d)
    (f : Joint n) (y : Points n) (hy : y∈fields n) :
    (∫ x, Z.emit (update v i (S.pin (d+1) (P.deriv d a t))) (glow x y)*f x) =
      ∫ x, Z.emit (update v i (S.pin d t)) (glow x y)*testAxis i a f x := by
  let A := Z.emit (update v i (S.pin d t))
  let B (x : Points n) := A (glow x y)
  let e := Points.direction i a
  let c := wick a
  have hw (x : Points n) : glow x y ∈ tube n := by change shade _ ∈ fields n; rwa [im_glow]
  have h (x : Points n) : HasFDerivAt B (((fderiv ℂ A (glow x y)).restrictScalars ℝ).comp (realPartL n)) x := by
    have hp : HasFDerivAt A ((fderiv ℂ A (glow x y)).restrictScalars ℝ) ((fun x => glow x y) x) :=
      (hZ.hol n (update v i (S.pin d t)) (glow x y) (hw x)).differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact hp.comp x (real_movement x y)
  have hc (x : Points n) : Z.emit (update v i (S.pin (d+1) (P.deriv d a t))) (glow x y)=
      c*fderiv ℝ B x e := by
    rw [field_jet P ht hs hv hu hF hZ v i a d t (hw x), wick_dir]
    dsimp only
    rw [map_smul, (h x).fderiv]
    rfl
  have hd (x : Points n) : testAxis i a f x=-c*fderiv ℝ f x e := by
    unfold testAxis
    rw [_root_.smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rfl
  have hI : Integrable (fun x => c*(fderiv ℝ B x e*f x)) := by
    have he := hZ.leaned _ (update v i (S.pin (d+1) (P.deriv d a t))) y hy f
    simpa only [hc, mul_assoc] using he
  have hk : Integrable (fun x => fderiv ℝ B x e*f x) := by
    have he := hI.const_mul (c⁻¹)
    simpa only [← mul_assoc c⁻¹, inv_mul_cancel₀ (wick_ne_zero a), one_mul, c] using he
  have hl : Integrable (fun x => B x*fderiv ℝ f x e) := by
    have he : Integrable (fun x => B x * (∂_{e} f : Joint n) x) := hZ.leaned n (update v i (S.pin d t)) y hy _
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using he
  have hr := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hk hl
    (show Integrable (fun x => B x * f x) from hZ.leaned n (update v i (S.pin d t)) y hy f)
    (fun x _ => (h x).differentiableAt) (fun _ _ => f.differentiableAt)
  simp_rw [hc, hd]
  change (∫ x, (c*_*_ : ℂ))=(∫ x, B x*(-c*fderiv ℝ f x e))
  simp_rw [mul_assoc, show ∀ x : Points n, B x*(-c*fderiv ℝ f x e)=-c*(B x*fderiv ℝ f x e) from fun x => mul_left_comm ..]
  rw [integral_const_mul, integral_const_mul, hr, neg_mul_neg]

open Distribution in
theorem distribution_jet (P : DiffPlan S) (ht : T.Hierarchy) (hs : S.Symmetric)
    (hv : P.Inclusions S) (hu : P.Derivatives T) (hF : F.Region T) (hZ : Z.FullBody F)
    (v : Fin n → S.Union) (i : Fin n) (a : Axis) (d : ℕ) (t : S.Field d)
    (f : Joint n) (y : Points n) (hy : y∈shores n) :
    (D n).partialD (W.W n (update v i (S.pin (d+1) (P.deriv d a t)))) y f =
      (D n).partialD (W.W n (update v i (S.pin d t))) y (testAxis i a f) := by
  haveI := towards_shore hy
  exact tendsto_nhds_unique_of_eventuallyEq (Z.sees hZ _ y hy (blankets D n) _)
    (Z.sees hZ _ y hy (blankets D n) _) (Eventually.mono self_mem_nhdsWithin
      (fun x hx => inserted_jet P ht hs hv hu hF hZ v i a d t f x hx))

theorem boundary_derivative (P : DiffPlan S) (ht : T.Hierarchy) (hs : S.Symmetric)
    (hv : P.Inclusions S) (hu : P.Derivatives T) (hF : F.Region T) (hZ : Z.FullBody F)
    (hc : Bid.cones W) (v : Fin n → S.Union) (i : Fin n) (a : Axis) (d : ℕ) (t : S.Field d)
    (f : Joint n) :
    W.W n (update v i (S.pin (d+1) (P.deriv d a t))) f =
      W.W n (update v i (S.pin d t)) (testAxis i a f) := by
  have he := distribution_jet P ht hs hv hu hF hZ v i a d t f 0 (flat n)
  rwa [Blanket.flatD _ (blankets D n) (hc n _), Blanket.flatD _ (blankets D n) (hc n _)] at he

def probeAxis (a : Axis) (f : Test4) : Test4 := (-wick a) • (∂_{basis a} f)

theorem testAxis_product (i : Fin n) (a : Axis) (g : Fin n → Test4) (f : Test4) :
    testAxis i a (Joint.materialize n (update g i f)) =
      Joint.materialize n (update g i (probeAxis a f)) := by
  let p := Points.direction i a
  let F (x : Points n) := ∏ j ∈ Finset.univ.erase i, g j (x j)
  have hp (f : Test4) (x : Points n) : Joint.materialize n (update g i f) x=f (x i)*F x := by
    rw [Joint.material_at, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.mem_erase.mp hj).1]
  have h (x : Points n) : lineDeriv ℝ (Joint.materialize n (update g i f)) x p =
      lineDeriv ℝ f (x i) (basis a) * F x := by
    have H (t : ℝ) : F (x+t • p) = F x := by
      exact Finset.prod_congr rfl fun j hj => by
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [p, Points.direction, hji]
    rw [lineDeriv]
    simp_rw [hp, H]
    have he : (fun t : ℝ => f ((x+t • p) i)) = fun t => f (x i+t • basis a) := by
      funext t
      simp [p, Points.direction]
    change deriv (fun t => (fun t : ℝ => f ((x+t • p) i)) t * F x) 0 = _
    rw [he]
    exact ((f.differentiableAt.lineDifferentiableAt.hasLineDerivAt).mul_const (F x)).deriv
  ext1 x
  unfold testAxis
  rw [_root_.smul_apply, hp, probeAxis, _root_.smul_apply, SchwartzMap.lineDerivOp_apply,
    SchwartzMap.lineDerivOp_apply, h]
  simp [mul_assoc]

-- Shift `testAxis_product` to the slot *between* A and B. Fin.append
-- construction as in Work.C29.
private lemma expect_jet (P : DiffPlan S) (ht : T.Hierarchy) (hs : S.Symmetric)
    (hv : P.Inclusions S) (hu : P.Derivatives T) (hF : F.Region T) (hZ : Z.FullBody F) (hc : Bid.cones W)
    (A B : Sentence S) (a : Axis) (d : ℕ) (t : S.Field d) (f : Test4) :
    W.expect (A++(S.pin (d+1) (P.deriv d a t),f)::B)=W.expect (A++(S.pin d t,probeAxis a f)::B) := by
  let n := A.length+(B.length+1)
  let s (x : Letter S) : Fin n → Letter S := Fin.append A.get (Fin.cons x B.get)
  let i : Fin n := Fin.natAdd A.length (0:Fin (B.length+1))
  have h (x y : Letter S) : s x = update (s y) i x := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have he : Fin.castAdd (B.length+1) j ≠ i := fun h => by
        have hj : j.val=A.length+0 := congr_arg (fun u : Fin n => u.val) h
        omega
      simp [he, s]
    induction j using Fin.cases with
    | zero => simp [s, i]
    | succ j =>
      rw [update_of_ne (show Fin.natAdd A.length j.succ ≠ i from
        fun e => by
          have hj : A.length+(j.val+1)=A.length+0 := congr_arg Fin.val e
          omega)]; simp [s]
  have e (x : S.Union) (f : Test4) :
      W.expect (A++(x,f)::B)=W.W n (update (Prod.fst ∘ s (0,0)) i x)
        (Joint.materialize n (update (Prod.snd ∘ s (0,0)) i f)) := by
    rw [show A++(x,f)::B=List.ofFn (s (x,f)) by
        dsimp only [s, n]; rw [List.ofFn_fin_append, List.ofFn_cons, List.ofFn_get, List.ofFn_get], Work.C29.expectOfFn, h (x,f) (0,0),
      Function.comp_update, Function.comp_update]
  rw [e, e, boundary_derivative P ht hs hv hu hF hZ hc _ i a d t, testAxis_product]

-- A general usage rule on the common unbounded field domain
lemma on_domain {T : Wightman S} {R : S.Rotation} {h : S.RealSpin} (H : FieldCore W R h T)
    (A B : T.operators.domain →ₗ[ℂ] T.operators.domain)
    (p : ∀ i j, inner ℂ (T.operators.vector i) (A (T.operators.evaluates j)).val=
      inner ℂ (T.operators.vector i) (B (T.operators.evaluates j)).val) : A=B := by
  let Q := T.operators
  have he j : A (Q.evaluates j)=B (Q.evaluates j) := by
    apply Subtype.ext
    refine (Kernel.Gram.whole H.soil).eq_of_inner_right ℂ fun f => ?_
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
    | single k w =>
      simp only [Kernel.Gram.stems, Finsupp.linearCombination_single, inner_smul_left]
      rw [p k j]
  have hv : Q.domain=Submodule.span ℂ (Set.range Q.vector) := H.total.cyclic
  have hs (x : Q.H) (hx : x∈Submodule.span ℂ (Set.range Q.vector)) :
      A ⟨x, hv.symm ▸ hx⟩=B ⟨x, hv.symm ▸ hx⟩ := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact he j
    | zero => exact (map_zero A).trans (map_zero B).symm
    | add x y hx hy hp hq =>
      change A ((⟨x, hv.symm ▸ hx⟩:Q.domain)+⟨y,hv.symm ▸ hy⟩) = B (⟨x,hv.symm ▸ hx⟩+⟨y,hv.symm ▸ hy⟩)
      rw [map_add, map_add, hp, hq]
    | smul c x hx h =>
      change A (c • (⟨x,hv.symm ▸ hx⟩:Q.domain))=B (c • (⟨x,hv.symm ▸ hx⟩:Q.domain))
      rw [map_smul, map_smul, h]
  exact LinearMap.ext fun v => hs v.val (hv ▸ v.property)

theorem derivative_domain (P : DiffPlan S) (ht : T.Hierarchy) (hs : S.Symmetric)
    (hv : P.Inclusions S) (hu : P.Derivatives T) (hF : F.Region T) (hZ : Z.FullBody F)
    (hc : Bid.cones W) {Q : Wightman S} {R : S.Rotation} {h : S.RealSpin} (H : FieldCore W R h Q)
    (a : Axis) (d : ℕ) (t : S.Field d) (f : Test4) :
    Q.operators.field (S.pin (d+1) (P.deriv d a t)) f = Q.operators.field (S.pin d t) (probeAxis a f) := by
  refine on_domain H _ _ fun i j => ?_
  change
    inner ℂ (Q.operators.vector i) (Q.operators.vector ((S.pin (d+1) (P.deriv d a t),f)::j)) =
      inner ℂ (Q.operators.vector i) (Q.operators.vector ((S.pin d t,probeAxis a f)::j))
  rw [Q.operators.general W H.meets Q.J H.adj, Q.operators.general W H.meets Q.J H.adj]
  exact expect_jet P ht hs hv hu hF hZ hc (Sentence.rev Q.J i) j a d t f

section consumer
variable {C : Family G} {S T : Table C.book} {V : Chamber T timeAxis}
  {A : Spread V} {B : Contour S} {X : Algebra S} {Q : Wightman S} {f : Extraction.Order}

lemma reads_derivative (H : Bid.Pantry S T V X.derivatives A)
    (c : Compatible S A X Q.spin H.head.spin B) (hc : FieldCore B.world X.turns H.head.spin Q)
    (a : Axis) (d : ℕ) (v : S.Field d) (z : Test4) : Q.operators.field
      (S.pin (d+1) (X.derivatives.deriv d a v)) z = Q.operators.field (S.pin d v) (probeAxis a z) := by
  obtain ⟨Y, -, hY⟩ := c.reveals
  have u := (hY Q.J hc.induced).1
  obtain ⟨D, F, hm⟩ := u.visible
  exact derivative_domain X.derivatives H.adopted H.head.laws.toSymmetric H.rises
    H.Der Y.birth hm.2 (spectra u.I) hc a d v z

theorem final_derivative (F : Final C f S) (a : Axis) (d : ℕ) (x : C.book.Ref d) (t : Test4) :
    F.action.operators.field
      (S.pin (d+1) (F.sector.derivatives.deriv d a (S.project d x))) t =
        F.action.operators.field (S.pin d (S.project d x)) (probeAxis a t) :=
  reads_derivative (selected_pantry (s:=F.room) F.phase) (onFinal F).2
    (FieldCore.of_realizes F.realization.qt) a d _ t

/-- A conservation test in this convention (in SMEARING signs).
The labels are *Euclidean-normalized components*; we haven't absorbed
Wick factors into the labels or made any self-adjointness claim. -/
theorem conserves (F : Final C f S) (a : Axis) (t : Test4) :
    (∑ b : Axis, F.action.operators.field (S.pin 4 (F.sector.energy b a)) (probeAxis b t)) = 0 := by
  let P := F.action.operators
  let V := F.sector.derivatives
  have he (b : Axis) : P.field (S.pin 4 (F.sector.energy b a)) (probeAxis b t) =
      P.field (S.pin 5 (V.deriv 4 b (F.sector.energy b a))) t :=
    (reads_derivative (selected_pantry (s:=F.room) F.phase) (onFinal F).2
      (FieldCore.of_realizes F.realization.qt) b 4 _ t).symm
  change (∑ b : Axis, P.field _ _)=0
  simp_rw [he]
  have H := F.phase.transport.conserved.divergence a
  rw [← LinearMap.sum_apply, ← map_sum, ← map_sum, H]; simp
end consumer
end YM.Next.BOUNDARY
