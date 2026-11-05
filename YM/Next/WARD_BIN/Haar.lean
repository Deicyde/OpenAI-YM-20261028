import Mathlib.Analysis.Calculus.ParametricIntegral
import YM.Next.WARD_BIN.Energy
import YM.RG.Bounded




/-!
# Integration by parts on the Wilson law

All covectors in the divergence are functions of the *whole* configuration and the
color at the start of a positive bond (use the actual stencil in applications).
The formulas are ℂ-valued but use derivatives over ℝ. `X U : Covector` is evaluated
on a **real** color; this way we can take complex-linear combinations without
any dagger ambiguity. No complexification of the Haar integral over the group!
Ordinary `moment_formula` supplies the full probability normalization. No small-field,
connectedness, simplicity, or perturbative hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Lattice Wilson RG
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

section
variable {R : Type*} [DecidableEq R]

/-- Flow at one positive edge. -/
def slide (e : Edge (Four R)) (U : Links R G.El) (v : G.Color) := Function.update U e (G.lieExp v * U e)

@[simp] lemma slide_zero (e : Edge (Four R)) (U : Links R G.El) : slide e U 0 = U := by simp [slide]

lemma slide_single (e : Edge (Four R)) (U : Links R G.El) (A : G.Color) (t : ℝ) (i : Edge (Four R)) :
    slide e U (t • A) i = G.lieExp (t • (Pi.single e A : Edge (Four R) → G.Color) i) * U i := by
  by_cases h : i=e
  · subst i; simp [slide]
  simp [slide,h]

lemma slide_add (e : Edge (Four R)) (U : Links R G.El) (A : G.Color) (s t : ℝ) :
    slide e (slide e U (t • A)) (s • A) = slide e U ((s+t) • A) := by
  funext i; simp_rw [slide_single]; exact left_add _ _ _ _

end

variable {n : Side}

lemma slide_increments (e : Edge (Site n)) (U : Config G n) (A : G.Color) (t : ℝ) :
    slide e U (t • A) = increment U (t • Pi.single e A) := by funext i; exact slide_single ..

/-- Each time map preserves *prior*, not in general law. -/
theorem slide_invariant (e : Edge (Site n)) (a : G.Color) (t : ℝ) :
    MeasurePreserving (fun U => slide e U (t • a)) (prior G n) (prior G n) := by
  simp_rw [slide_increments]
  let L (i : Edge (Site n)) (v : G.El) := G.lieExp ((t • (Pi.single e a : Directions G n)) i) * v
  exact measurePreserving_pi (fun _ : Edge (Site n) => G.probHaar) (fun _ => G.probHaar)
    (f:=L) (fun _ => measurePreserving_mul_left G.probHaar _)

theorem slide_energy (e : Edge (Site n)) (U : Config G n) (a : G.Color) :
    HasDerivAt (fun t : ℝ => energy (slide e U (t • a))) (inner ℝ a (euler U e)) 0 := by
  simp_rw [slide_increments]
  apply (derivative_energy U (Pi.single e a)).congr_deriv
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb; simp [hb]
  simp

section Bounded
variable {u v : Config G n → ℂ}

lemma bound_sum (hu : Envelope u) (hv : Envelope v) : Envelope fun U => u U+v U := by
  obtain ⟨M,hM⟩ := hu.cost; obtain ⟨N,hN⟩ := hv.cost
  exact ⟨hu.meas.add hv.meas,M+N,fun U => (norm_add_le ..).trans (add_le_add (hM _) (hN _))⟩
lemma bound_sub (hu : Envelope u) (hv : Envelope v) : Envelope fun U => u U-v U := by
  obtain ⟨M,hM⟩ := hu.cost; obtain ⟨N,hN⟩ := hv.cost
  exact ⟨hu.meas.sub hv.meas,M+N,fun U => (norm_sub_le ..).trans (add_le_add (hM _) (hN _))⟩
lemma bound_product (hu : Envelope u) (hv : Envelope v) : Envelope fun U => u U*v U := by
  obtain ⟨M,hM⟩ := hu.cost; obtain ⟨N,hN⟩ := hv.cost
  exact ⟨hu.meas.mul hv.meas,M*N,fun U => (norm_mul_le ..).trans (mul_le_mul (hM _) (hN _)
    (norm_nonneg _) ((norm_nonneg _).trans (hM U)))⟩
lemma envelope_continuous (h : Continuous u) : Envelope u :=
  ⟨h.measurable, h.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
lemma envelope_sums {ι : Type*} (s : Finset ι) (f : ι → Config G n → ℂ)
    (h : ∀ i ∈ s, Envelope (f i)) : Envelope (fun U => ∑ i∈s, f i U) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact envelope_continuous continuous_const
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]; exact bound_sum (h i (Finset.mem_insert_self ..))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
lemma bound_int (hu : Envelope u) (μ : Measure (Config G n)) [IsFiniteMeasure μ] : Integrable u μ := by
  obtain ⟨M,hM⟩ := hu.cost
  exact Integrable.of_bound hu.meas.aestronglyMeasurable M (Eventually.of_forall hM)

/-- Lattice Haar identity. Call with `v` the *complete* left derivative of
one observable (no configuration-dependence frozen), even in the presence
of multiplying spectator terms. -/
theorem haar_eq (e : Edge (Site n)) (a : G.Color)
    (hu : Envelope u) (hv : Envelope v)
    (h : ∀ U, HasDerivAt (fun t : ℝ => u (slide e U (t • a))) (v U) 0) :
    (∫ U, v U ∂prior G n) = 0 := by
  let f := fun t : ℝ => fun U => u (slide e U (t • a))
  let k := fun t : ℝ => fun U => v (slide e U (t • a))
  have H (t : ℝ) (U : Config G n) : HasDerivAt (fun s : ℝ => f s U) (k t U) t := by
    have hx : HasDerivAt (fun s : ℝ => u (slide e (slide e U (t • a)) (s • a))) (k t U) (t-t) := by
      rw [sub_self]; exact h _
    have ht := hx.comp_sub_const t t
    simp_rw [slide_add, sub_add_cancel] at ht
    exact ht
  obtain ⟨M,hM⟩ := hv.cost
  let μ := prior G n
  have he t : (∫ U, f t U ∂μ) = ∫ U, u U ∂μ := by
    have hh := slide_invariant (G:=G) e a t
    have ht := integral_map (μ := prior G n) hh.aemeasurable
      (f := u) (by rw [hh.map_eq]; exact hu.meas.aestronglyMeasurable)
    rw [hh.map_eq] at ht
    exact ht.symm
  have hh t : Integrable (f t) μ := (slide_invariant e a t).integrable_comp_of_integrable (bound_int hu (prior G n))
  have hx := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=Set.univ) (F':=k) (x₀:=0) (F:=f) (μ:=μ)
    univ_mem (Eventually.of_forall fun t => (hh t).aestronglyMeasurable) (hh 0)
      (by simpa [k] using hv.meas.aestronglyMeasurable (μ:=μ))
      (bound:=fun _ => M) (Eventually.of_forall fun U t _ => hM _) (integrable_const _) (Eventually.of_forall fun U t _ => H t U)
  obtain ⟨-,hx⟩:=hx; simp_rw [he] at hx
  simpa [k,μ] using hx.unique (hasDerivAt_const ..)

/-- The nondiscounted (`β`-multiplied) form works at every coupling, even
`β = 0`. The truth of `moment` here is under the normalized Wilson law. -/
theorem moment_eq (e : Edge (Site n)) (a : G.Color) (β : ℝ)
    (hu : Envelope u) (hv : Envelope v)
    (h : ∀ U, HasDerivAt (fun t : ℝ => u (slide e U (t • a))) (v U) 0) :
    moment β (fun U => v U - (↑(β * inner ℝ a (euler U e)):ℂ) * u U) = 0 := by
  let b (U : Config G n) := (↑(bare β U):ℂ)
  let f (U : Config G n) := (↑(β * inner ℝ a (euler U e)):ℂ)
  have H : Envelope (fun U => v U - f U*u U) := by
    apply bound_sub hv
    exact bound_product (envelope_continuous (show Continuous f by unfold f; fun_prop)) hu
  have hb : Envelope b := by apply envelope_continuous; unfold b; fun_prop
  have hd (U : Config G n) : HasDerivAt (fun t : ℝ => b (slide e U (t • a))) (- f U * b U) 0 := by
    have hg := ((slide_energy e U a).const_mul (-β)).exp
    apply (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hg).congr_deriv
    change (↑(Real.exp _ * (-β * inner ℝ a (euler U e))):ℂ)= -f U * b U
    simp only [zero_smul,slide_zero,f,b,bare,Complex.ofReal_mul,Complex.ofReal_neg, mul_comm,
      neg_mul,mul_neg]
  have he (U : Config G n) : HasDerivAt (fun t : ℝ => b (slide e U (t • a))*u (slide e U (t • a)))
      (b U * (v U-f U*u U)) 0 := by
    apply ((hd U).mul (h U)).congr_deriv
    simp only [zero_smul,slide_zero]; ring
  have hi := haar_eq e a (bound_product hb hu) (bound_product hb H) he
  rw [moment_formula _ _ (bound_int H (law G n β))]
  change _ * (∫ U, b U * (v U-f U*u U) ∂prior G n) = _
  rw [hi,mul_zero]
end Bounded

abbrev Covector (G : Gauge) := G.Color →L[ℝ] ℂ

def dirs (G : Gauge) := EuclideanSpace.basisFun G.ColorIndex ℝ

/-- Lattice left derivative, also used on actual finite stencils (Cover).
Use with differentiability proved! -/
def slope {R : Type*} [DecidableEq R] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : Edge (Four R)) (a : G.Color) (f : Links R G.El → F) (U : Links R G.El) :=
  deriv (fun t : ℝ => f (slide e U (t • a))) 0

def divergence {R : Type*} [DecidableEq R] (e : Edge (Four R)) (X : Links R G.El → Covector G)
    (U : Links R G.El) := ∑ i, slope e (dirs G i) (fun V => X V (dirs G i)) U

/-- The unscaled equation cylinder component at a positive edge. Use with
`β ≠ 0`. -/
def equation {R : Type*} [DecidableEq R] [AddCommGroup R] [One R] (β : ℝ)
    (e : Edge (Four R)) (X : Links R G.El → Covector G) (U : Links R G.El) :=
  X U (euler U e) - (β:ℂ)⁻¹ * divergence e X U

lemma covector_sum (a : G.Color) (L : Covector G) :
    ∑ i, (↑(inner ℝ (dirs G i) a):ℂ) * L (dirs G i) = L a := by
  conv_rhs => rw [← (dirs G).sum_repr a]
  rw [map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [map_smul, Complex.real_smul, OrthonormalBasis.repr_apply_apply]

/-- Regularity needed in the sampled direction only. -/
def HasFlow (e : Edge (Site n)) (a : G.Color) (f : Config G n → ℂ) :=
  Envelope f ∧ Envelope (slope e a f) ∧ ∀ U,
    DifferentiableAt ℝ (fun t : ℝ => f (slide e U (t • a))) 0

section
variable {e : Edge (Site n)} {X : Config G n → Covector G} {F : Config G n → ℂ}
  (hx : ∀ i, HasFlow e (dirs G i) fun U => X U (dirs G i))

include hx
lemma driven : Envelope fun U => X U (euler U e) := by
  simp_rw [← covector_sum (euler _ _) (X _)]
  exact envelope_sums _ _ fun i _ => bound_product (envelope_continuous (show Continuous _ from
    Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_euler))) (hx _).1

lemma equation_bounded (β : ℝ) : Envelope (equation β e X) := by
  apply bound_sub (driven hx)
  apply bound_product (envelope_continuous continuous_const)
  exact envelope_sums _ _ fun i _ => (hx i).2.1

/-- Integration by parts under the **normalized** Wilson law. No derivative
of a normalization or bound based only on one marginal. For coupling zero
use `moment_eq`, not this divided equation. -/
theorem ward_identity (β : ℝ) (hb : β ≠ 0) (hF : Envelope F)
    (h : ∀ i, HasFlow e (dirs G i) F) :
    moment β (fun U => equation β e X U * F U) =
      (β:ℂ)⁻¹ * ∑ i, moment β fun U => X U (dirs G i) * slope e (dirs G i) F U := by
  have hm := bound_int (bound_product (equation_bounded hx β) hF) (law G n β)
  let x := fun i (U : Config G n) => X U (dirs G i)
  let z (i : G.ColorIndex) := slope e (dirs G i) F
  let W (i) := fun U => x i U * z i U
  let b : ℂ := (β:ℂ)
  let p (i : G.ColorIndex) (U : Config G n) := (↑(inner ℝ (dirs G i) (euler U e)):ℂ) * x i U - b⁻¹ * slope e (dirs G i) (x i) U
  have hβ : b ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hW i : Envelope (W i) := bound_product (hx _).1 (h _).2.1
  have hp i : Envelope (p i) := by
    apply bound_sub _ (bound_product (envelope_continuous continuous_const) (hx i).2.1)
    apply bound_product _ (hx i).1
    exact envelope_continuous (show Continuous _ from
      Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_euler))
  have he (i : G.ColorIndex) : moment β (fun U => p i U * F U) = b⁻¹ * moment β (W i) := by
    obtain ⟨hxi,hD,hX⟩ := hx i
    let D := fun (U : Config G n) => slope e (dirs G i) (x i) U*F U + x i U*z i U
    have hd (U : Config G n) := (hX U).hasDerivAt.mul ((h i).2.2 U).hasDerivAt
    have HD (U : Config G n) : HasDerivAt
        (fun t : ℝ => x i (slide e U (t • dirs G i))*F (slide e U (t • dirs G i))) (D U) 0 := by
      apply (hd U).congr_deriv; change _=slope _ _ _ U * F U + X U _ * _
      rw [zero_smul,slide_zero]; rfl
    have ht := moment_eq e (dirs G i) β (bound_product (u:=x i) hxi hF)
      (show Envelope D from bound_sum (bound_product hD hF) (hW i)) HD
    have hi : moment β (fun U => W i U - b*(p i U*F U)) = 0 := by
      rw [← ht]; apply congrArg (moment β); funext U
      dsimp only [p,W,D]; rw [Complex.ofReal_mul]; dsimp only [b] at *
      field_simp; ring
    unfold moment at hi ⊢
    rw [integral_sub (bound_int (hW _) _) ((bound_int (bound_product (hp i) hF) _).const_mul _),
      integral_const_mul] at hi
    exact ((inv_mul_eq_iff_eq_mul₀ hβ).2 (sub_eq_zero.mp hi)).symm
  have hh : (fun U => equation β e X U * F U) = fun U => ∑ i, p i U * F U := by
    funext U
    rw [← Finset.sum_mul]
    apply congrArg (· * F U)
    simp only [equation,p,Finset.sum_sub_distrib]; rw [← Finset.mul_sum]
    exact congrArg (fun c : ℂ => c-_) (covector_sum _ _).symm
  rw [hh, Finset.mul_sum]
  unfold moment; rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => he i)
  intro i _; exact bound_int (bound_product (hp i) hF) _

/-- Disjoint-support null (one edge component). No differentiability of
spectators in other links is required. -/
theorem ward_null (β : ℝ) (hb : β ≠ 0) (hF : Envelope F)
    (hf : ∀ (a) (U : Config G n), F (slide e U a) = F U) :
    moment β (fun U => equation β e X U * F U) = 0 := by
  have hs (i : G.ColorIndex) : slope e (dirs G i) F = 0 := by
    funext U; unfold slope; simp_rw [hf]; exact deriv_const ..
  have he (i) : HasFlow e (dirs G i) F := by
    refine ⟨hF,?_, fun U => ?_⟩
    · rw [hs]; exact envelope_continuous continuous_const
    simp_rw [hf]; exact differentiableAt_const _
  rw [ward_identity hx β hb hF he]; simp only [hs,Pi.zero_apply,mul_zero,moment]; simp
end

/-! Gauge covariance also for the divergence (a trace over the actual Lie algebra,
not a frozen coefficient). -/
lemma adjoint_inv_left (u : G.El) (A : G.Color) : G.adjoint u (G.adjoint u⁻¹ A) = A := by
  rw [← G.adjoint_mul]; simp

def adjointGauge (u : G.El) : G.Color ≃ₗᵢ[ℝ] G.Color := LinearIsometryEquiv.ofSurjective
    ({ G.adjoint u with norm_map' := G.norm_adjoint u } : G.Color →ₗᵢ[ℝ] G.Color)
    (fun x => ⟨G.adjoint u⁻¹ x, adjoint_inv_left ..⟩)



lemma expAdjoint (u : G.El) (a : G.Color) : u * G.lieExp a * u⁻¹ = G.lieExp (G.adjoint u a) := by
  apply G.mat_injective
  simp only [G.mat_mul,G.mat_inv,G.mat_adjoint,G.mat_lieExp]
  rw [G.exp_conjugate]; rfl

section cover
variable {R : Type*} [DecidableEq R] [AddCommGroup R] [One R]
  {e : Edge (Four R)}

lemma slide_gauge (T : Four R → G.El) (U : Links R G.El) (a : G.Color) :
    slide e (Lattice.gauge T U) (G.adjoint (T e.1) a) = Lattice.gauge T (slide e U a) := by
  funext i; by_cases h : i=e
  · subst i; simp only [slide,Lattice.gauge,Function.update_self]
    rw [← expAdjoint]; simp only [mul_assoc,inv_mul_cancel_left]
  simp [slide,h,Lattice.gauge]

/-- A co-vector version: evaluate on color (real). -/
def Covariant (e : Edge (Four R)) (X : Links R G.El → Covector G) : Prop :=
    ∀ (a : G.Color) T U, X (Lattice.gauge T U) (G.adjoint (T e.1) a) = X U a

private lemma trace_both (W : G.Color →L[ℝ] Covector G)
    (a b : OrthonormalBasis G.ColorIndex ℝ G.Color) :
    ∑ i, W (a i) (a i) = ∑ j,W (b j) (b j) := by
  have he (p : OrthonormalBasis G.ColorIndex ℝ G.Color) (v : G.Color) :
      ∑ i, inner ℝ (p i) v • p i = v := by simpa only [← OrthonormalBasis.repr_apply_apply] using p.sum_repr v
  have hx (i) : W (a i) (a i) = ∑ j, inner ℝ (b j) (a i) • W (b j) (a i) := by
    nth_rw 1 [← he b (a i)]; rw [map_sum,sum_apply]; simp
  have ht (j) : ∑ i, inner ℝ (b j) (a i) • W (b j) (a i) = W (b j) (b j) := by
    simp_rw [← map_smul, show ∀ i, inner ℝ (b j) (a i) = inner ℝ (a i) (b j) from fun _ => (real_inner_comm _ _)]; rw [← map_sum, he]
  simp_rw [hx, Finset.sum_comm (f:=fun i j => inner ℝ (b j) (a i) • W (b j) (a i)), ht]

/-- Assumes Fréchet derivatives at that positive edge only. -/
lemma divergence_gauge (X : Links R G.El → Covector G) (hX : Covariant e X)
    (hx : ∀ U : Links R G.El, DifferentiableAt ℝ (fun a => X (slide e U a)) 0) :
    GaugeInvariant (divergence e X) := by
  intro T U
  let V := Lattice.gauge T U
  let W (U : Links R G.El) := fderiv ℝ (fun a => X (slide e U a)) 0
  have h (A : G.Color) (U : Links R G.El) : HasDerivAt (fun t : ℝ => X (slide e U (t • A)) A) (W U A A) 0 := by
    let L := ContinuousLinearMap.apply ℝ ℂ A
    have ht : HasDerivAt (fun t : ℝ => X (slide e U (t • A))) (W U A) 0 := (hx _).hasFDerivAt.comp_hasDerivAt_of_eq 0
      (show HasDerivAt (fun t : ℝ => t • A) A 0 by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const A) (by simp)
    exact L.hasFDerivAt.comp_hasDerivAt 0 ht
  let b := (dirs G).map (adjointGauge (T e.1))
  have hb (i) : b i = G.adjoint (T e.1) (dirs G i) := by rw [OrthonormalBasis.map_apply]; rfl
  have hp (i) : W V (b i) (b i) = W U (dirs G i) (dirs G i) := by
    apply (h (b i) V).unique
    simp_rw [hb, ← map_smul, V, slide_gauge, hX _ T]; exact h _ _
  unfold divergence
  have hd (a : G.Color) (U : Links R G.El) := (h a U).deriv
  simp only [slope]; simp_rw [hd]
  change ∑ i,W V _ _ = _
  rw [trace_both (W V) (dirs G) b]; simp_rw [hp]


end cover
end YM.WardBin
