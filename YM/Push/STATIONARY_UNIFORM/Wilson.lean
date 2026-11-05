import YM.Push.STATIONARY_UNIFORM.Paths

/-!
# Instance check on a genuine unmasked Wilson integral

E.g., start *these* estimates directly on the actual Wilson and the
normalized kernel, even without BB-path input suppliers. This uses our
weaker (L powers) implicit estimate independent of crafting Floor and roots.
There is no assertion that these will be coordinates of a funded
trajectory (even `clip.direct` may need to be chosen smaller in actual path
induction!). Doesn't assert any estimates on large fields or the full
integrals. Includes actual score equality on the analytic ball, with likelihood
a sum over the stated finite tags, so in particular the path branch on this
ball can start there. Does **not** estimate any beta reset.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {μ C Λ : ℝ} {p : Clip} {n j : ℕ}

/-- Special direct-only representative used here *only* for the unmasked-score
example. Cubic/quartic calculations elsewhere can/will need a different W. -/
def wil (G : Gauge) : PathData G :=
  let a : Slot := ⟨[],⟨(0,1),by decide⟩⟩
  let k (n : ℕ) : Atom G n := ⟨fun _ => a,0⟩
  ⟨fun _ _ => (0,a),fun _ => k 2,fun _ => k 3,fun _ => k 4⟩

def firstClip : Clip := ⟨1,1/32,1,by norm_num,by norm_num,by norm_num,by norm_num⟩
lemma initial_bounds (G : Gauge) (hm : 0<μ) (hC : 0≤C) (hL : 0≤Λ) (he : p.direct=1) :
    (wil G).Bounds p μ C Λ := by
  refine ⟨hm,fun i => ?_, ?_,?_,?_,fun i => ?_,fun i j => ?_,?_,fun i x => ?_,?_⟩
  · simp [SumBudget,wil,hC]
  · simp [wil,Atom.budget,Atom.magnitude,SumBudget,hL]
  · simp [wil,Atom.budget,Atom.magnitude,SumBudget,hC]
  · simp [wil,Atom.budget,Atom.magnitude,SumBudget,hC]
  · simp [wil,Atom.Invariant,Atom.poly]
  · simp [wil]
  · simp [PathData.metric_zero,PathData.symbol0,wil,he]
  · unfold PathData.loop_coeff; simp [wil]
  simp [PathData.loop_jets,PathData.loop_coeff,wil]

lemma initial_main (he : p.direct=1) (V : Config G f) : mainTerm p (wil G) V=Wilson.energy V := by
  have hh (s : Signed) : quadratic p (wil G) (pull s 0 V)=Wilson.energy V := by
    rw [← energy_pull V s 0]; simp [quadratic,PathData.ell,PathData.ellTerms,wil,he,Wilson.energy]
  have hu : 0 < (Fintype.card Signed:ℝ) := by positivity
  simp_rw [mainTerm, Patch.average,hh]
  simp only [wil, uncut, Atom.unmasked, Atom.poly, Pi.zero_apply,zero_mul,Finset.sum_const_zero, tsum_zero,
    add_zero, Finset.sum_const,Finset.card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ hu.ne']

variable (B : Forest S.ratio)

/-- Join to physical joint density on the horizon. `density` is w.r.t.
probability Haar on the coarse links, `bare` unnormalized on fine links
against probability Haar; works as pointwise identity for any real β. -/
lemma normal_identity {Q : KernelChoices} (he : p.direct=1) (A : Before G μ C j Q n)
    (hS : S.patch.Branches S.kernel G) (hj : S.patch.J=j) (hq : S.kernel=Q) (t : S.Choices) (β : ℝ)
    (x : Positions (Joint B G)) (hx : x∈ball 0 (A.tables p S.patch).initial) :
    let U := fine G B x
    let V := outer G B x
    bare β U * S.density β U V = (S.penaltyZ β G)⁻¹ ^ Fintype.card (Bond c) * Real.exp (-β * priced B t p (wil G) x) := by
  subst j; subst Q
  intro U V
  have ht (u) : S.prediction U u=S.prediction U t := picked_tags S (fine_supply B A.labels) (le_trans (by norm_num) A.n_ok)
    A.exp A.log x hx u t
  rw [show S.density β U V=S.noise β (S.prediction U t) V from ?_]
  · unfold bare StepData.noise StepData.penaltyWeight priced tested
    simp only [Function.comp_apply,Function.uncurry]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, initial_main he]
    change _=_ * Real.exp (-β*(Wilson.energy U + noiseTaylor S V U t)); unfold noiseTaylor
    rw [← Finset.mul_sum, mul_add, ← mul_assoc (-β) S.kernel.penalty,Real.exp_add]; ring
  unfold StepData.density
  conv_lhs => arg 2; ext u; rw [ht u]
  rw [← Finset.sum_mul,S.chosen hS,one_mul]

-- instantiate estimates universally in J,L, not just on chosen `Levels`

end YM.Push.Uniform
