import YM.Next.MULTISOURCE.Ends
import YM.Next.MULTISOURCE.LevelD

/-! extension from already qualified (lower) tangent prices -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice MeasureTheory Marker Function Filter Finset Work.G07
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} {P : BudgetPoint} {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

lemma FitsPurse.sub {F H : Config G n → ℂ} {a b : ℝ} (h : FitsPurse a F) (he : FitsPurse b H) :
    FitsPurse (a+b) (fun x => F x-H x) :=
  ⟨add_nonneg h.nonneg he.nonneg,fun i U => by rw [h.symmetry,he.symmetry],h.borel.sub he.borel,
    fun U => (norm_sub_le ..).trans (add_le_add (h.all _) (he.all _))⟩
lemma FitsPurse.sum {J : Type*} (s : Finset J) (f : J → Config G n→ℂ) (g : J→ℝ) (h : ∀ i,FitsPurse (g i) (f i)) :
    FitsPurse (∑ i∈s,g i) (fun x => ∑ i∈s,f i x) :=
  ⟨sum_nonneg (fun i _ => (h i).nonneg),fun t U => sum_congr rfl fun i _ => (h i).symmetry t U,
    Finset.measurable_fun_sum _ (fun i _ => (h i).borel), fun U => (norm_sum_le ..).trans (sum_le_sum fun i _ => (h i).all U)⟩

omit [Fintype V] in
lemma at_step (θ : ℝ) (_hθ : 0 ≤ θ) (Q : Rep G n) {σ C Λ r w : ℝ} (h : Q.Lawful σ C Λ r w) (hp : GaugeInvariant Q.exponent)
    (b K : ℝ) (i : Hot R) : ∃ B m : ℝ,∀ X : Hot R → Support n,∀ D : Hot R → Pulse G n,
      (∀ j,Credit Q.p 0 K (X j) (D j) b ∧ ∃ f,SimpleBound Q.p θ b f ∧ recept Q.p (D j).1 f) →
      FitsPurse m (ProperSum Q D i) ∧ ∃ f,SimpleBound Q.p θ B f ∧
        recept Q.p (ProperSum Q D i) (fun U => (Q.eval U:ℂ)*f U) := by
  choose g hg using fun j => jet_bounded (parts R) b K Q h hp j
  choose k hk using fun s : (parts R).Mode => prods Q.p θ (G:=G) (n:=n) b s.val
  let I := (shards R i.val).erase ((parts R).fire i)
  refine ⟨∑ s∈I,k s, ∑ s∈I,g s, fun X D H => ⟨FitsPurse.sum _ _ _ (fun i => hg i _ _ fun j => (H j).1),?_⟩⟩
  choose f Hf hx using fun j => (H j).2
  refine ⟨_, sums Q.p θ I _ fun s => hk s f Hf,fun U hU => ?_⟩
  unfold ProperSum; simp only [mul_sum]; apply sum_congr rfl; intro j hj; rw [simple_all _ _ _ _ hU]
  simp_rw [hx _ _ hU]

section

lemma kernelized (H : History G) (j p N : ℕ) (he : j<N) (h : H.Selected) {θ : ℝ} (hh : 0 ≤ θ)
    (C : ℝ) :
    let A := H.rep N p j
    let Q := H.rep N p (j+1)
    let S := H.levels.clock.op j p
    ∃ r t : ℝ, ∀ F : Config G _ → ℂ, FitsPurse C F →
      FitsPurse t (S.push Q.beta F) ∧ SimpleBound A.p θ r (clean A (S.push Q.beta F)) := by
  intro A Q S
  have hx : S.patch.Branches S.kernel G := (H.levels.blocks ..).branches
  have hk : A.eval=S.push Q.beta Q.eval := (h.steps N p j he).1
  obtain ⟨B,hB,hP⟩ := smooth_price A hx (Q.envelope (h.represents N p _ he).good) (fun U =>
    AxisShift.chosen_positive h he U) hk hh
  obtain ⟨v,hv⟩ := (S.isKernel hx Q.beta).bound
  have hu := A.envelope (h.represents N p j he.le).good
  refine ⟨C*B,|v| * |C|,fun F hh => ?_⟩
  let G' := S.push Q.beta F
  have hz (x) : (A.eval x:ℂ)*clean A G' x=G' x := cleaned A G' x (AxisShift.chosen_positive h he.le x)
  obtain ⟨hs,hh'⟩ := hP F hh.integral _ hh.all
  have hi : GaugeInvariant G' := push_gauge H.levels j p F hh.integral hh.symmetry _
  refine ⟨⟨by positivity,hi, ?_,fun U => ?_⟩,hs,?_,hh'⟩
  · change Measurable G'; rw [← funext hz]; exact
      (Complex.continuous_ofReal.measurable.comp hu.meas).mul hs.measurable
  · have he (i) : ‖(S.density Q.beta i U) • F i‖ ≤ |v| * |C| := by
      rw [norm_smul,Real.norm_of_nonneg (S.density_positive ..)]
      exact mul_le_mul ((hv i U).trans (le_abs_self _)) ((hh.all _).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
    apply le_trans (norm_integral_le_of_norm_le_const (Eventually.of_forall he)); simp
  intro i U
  change (A.eval (gauge i U))⁻¹ • G' (gauge i U)= _
  rw [show A.eval (gauge i U)=_ from path_gauge _ h N p j he.le i U, hi i U]; rfl
end
end YM.Multi.Step
