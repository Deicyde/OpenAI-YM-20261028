import YM.Push.LOOP_COEFFICIENT.Block.Spend
import YM.Push.LOOP_COEFFICIENT.Frame.Rollout

/-!
# Local coefficient charts counted after L with pre-L strip
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Matrix Set Filter Lattice Laurent Bloch Complex Block Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d e : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype e] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] [DecidableEq e]
  {η C D A : ℝ}

structure Banner (M : Momentum → Matrix a b ℂ) (η C : ℝ) : Prop where
  nonneg : 0≤C
  smooth q : q∈Tube η → ContDiffAt ℂ ω M q
  periodic q : q∈Tube η → ∀ x, M (q+reciprocal x) = M q
  bound q : q∈Tube η → ‖M q‖≤C
namespace Banner
variable {M : Momentum → Matrix a b ℂ} (h : Banner M η C)
include h
omit [DecidableEq a] [Fintype d] [DecidableEq d] in lemma grows : Grows (Vertex.const (d:=d) M) η := StripLaw.const fun q hq => ⟨h.smooth q hq,h.periodic q hq⟩
omit [DecidableEq a] [DecidableEq d] in lemma charge : Quanta (Vertex.const (d:=d) M) (Tube η) (Tube η) 1 C := .const one_pos h.nonneg h.bound
omit [DecidableEq a] in lemma norm_acts (q) (hq : q∈Tube η) (x : CSpace b) (hx : ‖x‖≤1) : ‖M q *ᵥ x‖ ≤ Fintype.card b * C := alias_sup _ ⟨h.nonneg, fun _ _ => (component_norm ..).trans (h.bound q hq)⟩ hx
end Banner
variable {M : Momentum → Matrix c d ℂ} {P : Momentum → Matrix b e ℂ}
omit [DecidableEq a] [DecidableEq c] in lemma atom_fixed (X : Jet c (Matrix a b ℂ)) (hC : 0≤C) : ∃ A>0,∀ {M : Momentum → Matrix c d ℂ}, Banner M η C → Grows (atom M X) η ∧ Quanta (atom M X) (Tube η) (Tube η) 1 A := by
  let L := X.lin.toContinuousLinearMap
  let Q (i : a) (j : b) := (LinearMap.toContinuousLinearMap.toLinearMap.comp (X.quad.compr₂ (entryLinearMap ℂ ℂ i j))).toContinuousLinearMap
  let K := ∑ i,∑ j, ‖Q i j‖
  let H := matrixCost a b
  have hK : 0≤K := by unfold K; positivity
  have hH : 0≤H := matrixCost_nonneg ..
  have hQ (i j) : ‖Q i j‖ ≤ K := (Finset.single_le_sum (fun j _ => norm_nonneg (Q i j)) (Finset.mem_univ j) (f:=fun j => ‖Q i j‖)).trans (Finset.single_le_sum (f:=fun i => ∑ j, ‖Q i j‖) (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (Q i j))) (Finset.mem_univ i))
  let d := (Fintype.card d : ℝ)*C
  have hd : 0≤d := by unfold d; positivity
  refine ⟨1+‖X.base‖+‖L‖*d+H*(K*d*d),by positivity,fun {M} hm => ?_⟩
  have he (q) (v : CSpace _) (hq : q ∈ Tube η) : ContDiffAt ℂ ω (fun q => M q *ᵥ v) q := contDiffAt_pi.mpr fun i => ContDiffAt.sum fun j _ => (analyticComponent (hm.smooth _ hq) i j).mul contDiffAt_const
  have ht : 0≤H*(K*d*d) := by positivity
  refine ⟨⟨fun _ _ => ⟨contDiffAt_const,fun _ => rfl⟩,fun q p v _ hp => ⟨L.contDiff.contDiffAt.comp (f:=fun z => M z.2 *ᵥ v) (q,p) ((he p v hp).comp (q,p) contDiffAt_snd), fun x y => by simp [atom,hm.periodic _ hp]⟩,fun q p s v w _ hp hs => ⟨analyticMatrix (fun i j => ((Q i j).contDiff.contDiffAt.comp (f:=fun z : Momentum×Momentum×Momentum => M z.2.1 *ᵥ v) (q,p,s) ((he p v hp).comp (q,p,s) contDiffAt_snd.fst)).clm_apply ((he s w hs).comp (q,p,s) contDiffAt_snd.snd)),fun x y z => by simp [atom,hm.periodic _ hp,hm.periodic _ hs]⟩⟩,⟨by positivity,fun _ _ => by change ‖X.base‖ ≤ _; have h₁ := mul_nonneg (norm_nonneg L) hd; linarith,
    fun q p v _ hp hv => (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hm.norm_acts p hp v hv) (norm_nonneg L)).trans (by change ‖L‖*d ≤ _; rw [div_one]; linarith [norm_nonneg X.base])), fun q p s v w _ hp hs hv hw => (matrix_norm (Q:=K*d*d) (by positivity) (fun i j => ((Q i j).le_opNorm₂ ..).trans ?_)).trans ?_⟩⟩
  · exact mul_le_mul (mul_le_mul (hQ i j) (hm.norm_acts p hp v hv) (norm_nonneg _) hK) (hm.norm_acts s hs w hw) (norm_nonneg _) (by positivity)
  rw [one_pow,div_one]; exact le_add_of_nonneg_left (by positivity)
omit [DecidableEq a] in
lemma cost_pair (f : (c → ℝ) → Matrix a b ℝ) (hC : 0≤C) (hD : 0≤D) : ∃ A>0,∀ {M : Momentum → Matrix c d ℂ} {P : Momentum → Matrix b e ℂ}, Banner M η C → Banner P η D → Grows (row M P f) η ∧ Quanta (row M P f) (Tube η) (Tube η) 1 A := by
  -- actualMatrix has Frobenius instance
  let X : Jet c (Matrix a b ℂ) := actualMatrix f
  obtain ⟨A,hA,H⟩ := atom_fixed (d:=d) (η:=η) (X) hC
  refine ⟨1+4*A*D,by positivity,fun hm hp => ⟨(H hm).1.mul hp.grows,((H hm).2.mul hp.charge one_pos).mono (le_add_of_nonneg_left zero_le_one) zero_le_one⟩⟩

end YM.Push.Loops.Frames
