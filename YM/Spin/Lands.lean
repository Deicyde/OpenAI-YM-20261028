import YM.Spin.Sheets

/-!
# Descent with base Θ. Concrete Eta. Prove cohesion consumer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spin
open Filter Function Set Table Ward Maxwell
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {L : Register G} {S : Table L}
structure Port (P : Rotation S) (H : RealSpin S) : Prop where
  spin d (x : S.Field d) : Continuous (fun k => P.act d k x)
  fixes d x : P.act d 1 x=x
  sends d g k s : P.act d (g*k) s=P.act d g (P.act d k s)
  signed d (g : Signed) s : P.act d g.ortho s = S.mirror H d g s
  real d s x : S.conj H d (P.act d s x)=P.act d s (S.conj H d x)
  spinAt d (g : Ortho.Skew) x : HasDerivAt (fun t => P.act d (Ortho.oneParameter g t) x) (P.lie d g x) 0

variable (P : Rotation (comparator L))
def morph (D : SpinRows S) (V : ∀ d, change S d) : Rotation S where
  act d k := (V d).symm.trans ((P.act d k).trans (V d))
  lie := D

theorem produces {A : S.RealSpin} {a : (comparator L).RealSpin} (D : SpinRows S) (h : ∀ d, ∃ U z, Tilt P A a D d U z)
    (he : Port P a) :
    ∃ V : ∀ d, change S d, (∀ d, realH A a (V d)) ∧ Port (morph P D V) A := by
  choose U z hv using h
  choose V hw hz using fun d => meet P _ (hv d)
  refine ⟨V,hw,fun_prop_rest V hw hz⟩
where
 fun_prop_rest (V : ∀ d, change S d) (hp : ∀ d, realH A a (V d)) (ht : ∀ d k x, D d k (V d x)=V d (P.lie d k x)) :
    Port (morph P D V) A := {
    spin := fun d x => (V d).toLinearMap.continuous_of_finiteDimensional.comp (he.spin d ((V d).symm x))
    fixes := fun d x => by simp [morph,he.fixes]
    sends := fun d v x p => by simp [morph,he.sends]
    signed := fun d v x => by
      simp only [morph,LinearEquiv.trans_apply,he.signed,(hp d).1, LinearEquiv.apply_symm_apply]
    real := fun d s x => by
      obtain ⟨u,rfl⟩ := (V d).surjective x
      simp only [morph,LinearEquiv.trans_apply,← (hp d).2, LinearEquiv.symm_apply_apply,he.real]
    spinAt := fun d g x => by
      obtain ⟨u,rfl⟩ := (V d).surjective x
      let L := (V d).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
      simp only [morph,LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,ht]
      exact L.hasFDerivAt.comp_hasDerivAt 0 (he.spinAt d g u) }

/-- For ANY morph or other rotation. Fill cohesions by all-spectator, from `Motion` consumers. -/
lemma team (X : Rotation S) (H : S.Hierarchy) (B : Port X H.spin)
    (h : X.Oriented S) (W : DiffPlan S) (hw : W.Inclusions S) {d e : ℕ} (w : d≤e) (g : Ortho)
    (p : S.Field d) : X.act e g (W.rise w p)=W.rise w (X.act d g p) := by
  apply S.field_ext H.laws.toSymmetric
  intro n q x hx
  rw [hw.kernels w _ hx]
  let f := X.label g
  let y := Points.move g⁻¹ x
  have hy : y∈ conf _ := Points.move_in _ hx
  let r := X.label g⁻¹ ∘ q
  have he d (v : S.Field d) : f (X.label g⁻¹ ⟨d,v⟩)=⟨d,v⟩ := by simp only [f,Rotation.label,← B.sends,mul_inv_cancel,B.fixes]
  have ht (b : ℕ) (z : S.Field b) : S.useAt S x (Fin.cons ⟨b,X.act b g z⟩ q) = S.useAt S y (Fin.cons ⟨b,z⟩ r) := by
    have hp (w : S.Tag) : f (X.label g⁻¹ w)=w := by cases w; apply he
    have hm : Fin.cons (α := fun _ => S.Tag) ⟨b,X.act b g z⟩ q = X.label g ∘ (Fin.cons (α := fun _ => S.Tag) ⟨b,z⟩ r) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
      · rfl
      exact (hp _).symm
    have he' := h _ (Fin.cons ⟨b,z⟩ r) y hy g
    rw [show Points.move g y=x from by ext j; simp [y],← hm] at he'; exact he'
  rw [ht, ht]; exact hw.kernels w _ hy _
end YM.Spin
