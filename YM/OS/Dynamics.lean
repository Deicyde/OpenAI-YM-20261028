import YM.OS.Flow

/-!
# Existence of the coordinate OS semigroups

Unconditional from Table hierarchy. These will support either
PVM work or analytic-vector approaches to rotation. Completion applies
any cardinal size of register/plants in Type, no separability baked in.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Function Set Filter Analysis Word
open scoped Topology BigOperators InnerProductSpace NNReal ComplexOrder ComplexConjugate
variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis}

lemma ketC {D : Hilbert} {Y : Type*} [TopologicalSpace Y] (f : Y → D) (u : Y)
    (hp : ContinuousAt (fun t => inner ℂ (f t) (f t)) u)
    (hh : ContinuousAt (fun t => inner ℂ (f u) (f t)) u) : ContinuousAt f u := by
  -- take norm-square of difference from u
  have he : ContinuousAt (fun y => inner ℂ (f y) (f u)) u := by
    rw [show (fun y => inner ℂ (f y) (f u)) = star ∘ fun y => inner ℂ (f u) (f y) from funext fun i => (inner_conj_symm _ _).symm]
    exact (continuous_star (R := ℂ)).continuousAt.comp hh
  have ht : ContinuousAt (fun y => dist (f y) (f u)) u := by
    simp_rw [dist_eq_norm,@norm_eq_sqrt_re_inner ℂ,inner_sub_right,inner_sub_left]
    exact Real.continuous_sqrt.continuousAt.comp (Complex.continuous_re.continuousAt.comp
      ((hp.sub hh).sub (he.sub (continuousAt_const (y := inner ℂ (f u) (f u))))))
  apply tendsto_iff_dist_tendsto_zero.mpr; simpa only [ContinuousAt,dist_self] using ht

variable (X : Schwinger S a)
lemma contE (h : S.Hierarchy) (i : Future L a) : Continuous fun (t : ℝ≥0) => X.plant (travel i t) := by
  have he : Continuous fun (t : ℝ≥0) => S.gram a i.val (travel i t).val := by
    let c : E4 → ℂ := fun x => S.expect (reflect i.val a ++ carry i.val x)
    let f : ℝ≥0 → E4 := fun t => (t:ℝ) • basis a
    have h₁ : Continuous f := continuous_subtype_val.smul continuous_const
    have hu := (correl h a i i).1.comp_continuous h₁ (fun t => show 0 ≤ f t a by simp [f])
    exact hu
  apply continuous_iff_continuousAt.mpr
  intro t
  apply ketC (D := X.H)
  · simp_rw [X.measure, sym_time h.translations, advances]
    exact (he.comp (show Continuous (fun x : ℝ≥0 => x+x) from continuous_id.add continuous_id)).continuousAt
  simp_rw [X.measure,sym_time h.translations a i, advances]
  exact (he.comp (show Continuous (fun x : ℝ≥0 => x+t) from continuous_id.add continuous_const)).continuousAt

lemma contU (h : S.Hierarchy) (i : Future L a) : Continuous fun (x : Cross a) => X.plant (over i x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply ketC (D := X.H)
  · simp_rw [X.measure,sym_space h.translations]; exact continuousAt_const
  simp_rw [X.measure]
  let F (x : Cross a) := (x.val : E4)
  have he : Continuous F := continuous_subtype_val
  have H := (correl h a (over i t) i).1.comp_continuous he (fun x => show _ from (le_of_eq x.property.symm))
  exact H.continuousAt

structure Chamber (S : Table L) (a : Axis) where
  GNS : Schwinger S a
  flow : Semigroup GNS.H a
  atBirth t (v : Future L a) : GNS.plant (travel v t) = flow.E t (GNS.plant v)
  across t (v : Future L a) : GNS.plant (over v t) = flow.U t (GNS.plant v)

lemma implement (H : S.Hierarchy) : ∃ C : Chamber S a, C.GNS = X := by
  choose E hE hP using fun (t : ℝ≥0) => X.by_bound (fun v => X.plant (travel v t)) 1 zero_le_one (by
    intro g; rw [one_mul]; exact contract X H t g)
  choose U hU hW using fun (x : Cross a) => X.by_bound (fun v => X.plant (over v x)) 1 zero_le_one (by
    intro g; rw [one_mul]; exact (safe X x H g).le)
  have es t : (E t).adjoint=E t := by
    apply X.by_bud; intro v
    refine X.whole.eq_of_inner_left ℂ fun f => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    -- linearity on all sums; compare singles
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => -- extract v form after adj rewrite
      simp only [map_add, inner_add_right,hf,hg]
    | single i c =>
      simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul,
        inner_smul_right,hP,X.measure,sym_time H.translations]
  have hu : U 0=ContinuousLinearMap.id ℂ X.H := X.by_bud fun i => by rw [hW,pause]; rfl
  have hv (x y) : U (x+y)=(U x).comp (U y) := by
    apply X.by_bud; intro i; simp [hW, parallel, add_comm x y]
  let B : Semigroup X.H a := {
    E := E
    U := U
    eZero := X.by_bud fun i => by rw [hP,done]; rfl
    sym := es
    uZero := hu
    space := hv
    shrinks := hE
    time := fun x y => X.by_bud fun i => by simp [hP,add_comm x y]
    independent := fun t y => X.by_bud fun i => by simp [hP,hW]
    unitary := by
      intro t p
      have ht (t : Cross a) (p) : ‖U t p‖ ≤ ‖p‖ := ((U t).le_opNorm p).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hU _))
      refine le_antisymm (ht _ _) ?_
      have he := ht (-t) (U t p)
      rw [← ContinuousLinearMap.comp_apply,← hv,neg_add_cancel,hu] at he
      exact he
    continuousE := strong X (D := X.H) hE fun i => by simp_rw [hP]; exact contE X H i
    continuousU := strong X (D := X.H) hU fun i => by simp_rw [hW]; exact contU X H i
  }
  exact ⟨⟨X,B,fun t v => (hP t v).symm,fun x v => (hW x v).symm⟩,rfl⟩

lemma realization (H : S.Hierarchy) (a : Axis) : Nonempty (Chamber S a) :=
  ⟨(implement (Classical.choice (schwinger_ready (a := a) H)) H).choose⟩
end YM.OS
