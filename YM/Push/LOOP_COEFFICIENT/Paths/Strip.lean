import YM.Push.LOOP_COEFFICIENT.Paths.Hessian
import YM.Push.LOOP_COEFFICIENT.Paths.Reader
import YM.Push.LOOP_COEFFICIENT.Tubes

/-!
# Frequency analyticity and counting bounds from anchored bills alone
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Matrix Lattice Laurent Bloch Exterior RG Complex Metric
open scoped Topology Matrix.Norms.L2Operator ContDiff BigOperators
variable {a b d ι : Type} [Fintype a] [Fintype b] [Fintype d] [DecidableEq a] [DecidableEq b]

/-- Bounds on the unscaled vertices at flat on a common frequency tube;
background inputs with unit sup norm, internal legs in type-counting L². -/
structure Packet (U : Vertex d a b) (η C : ℝ) : Prop extends Lit U η where
  width : 0<η
  nonneg : 0≤C
  zeroBound q : q∈Tube η → ‖U.base q‖≤C
  oneBound q p v : q∈Tube η → p∈Tube η → ‖v‖≤1 → ‖U.one q p v‖≤C
  twoBound q p s v w : q∈Tube η → p∈ Tube η → s∈Tube η → ‖v‖≤1 → ‖w‖≤1 → ‖U.two q p s v w‖≤C

def matrixCost (a b : Type) [Fintype a] [Fintype b] [DecidableEq b] := ‖(ofLinearEquiv ℂ (m:=a) (n:=b) (α:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap‖
lemma matrixCost_nonneg (a b : Type) [Fintype a] [Fintype b] [DecidableEq b] : 0 ≤ matrixCost a b := by unfold matrixCost; positivity

omit [DecidableEq a] in
lemma matrix_norm {Q : ℝ} {T : Matrix a b ℂ} (h : 0≤Q) (he : ∀ i j, ‖T i j‖≤Q) : ‖T‖ ≤ matrixCost a b * Q :=
  ((ofLinearEquiv ℂ).toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm (fun i j => T i j)).trans (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg h).mpr fun i => (pi_norm_le_iff_of_nonneg h).mpr (he i)) (norm_nonneg _))

namespace Paths
variable {M : ι → Reader a} {d k : ℕ} {η C : ℝ}

def Emission (M : ι → Reader a) (η C : ℝ) (d : ℕ) := ∃ g : ι → ℝ, SumBudget g C ∧ ∀ {k}, k≤d → ∀ p : Fin k → Momentum, (∀ j,p j ∈ Tube η) → ∀ i, ‖(M i).monomial p‖ ≤ g i

variable (a) in
omit [DecidableEq a] in
lemma emission {η ρ : ℝ} (hη : 0<η) (hρ : 0<ρ) (d) : ∃ e D : ℝ,0<e ∧ e≤η ∧ 0<D ∧ ∀ {ι : Type} {M : ι → Reader a} {C}, Damped M η ρ C → Emission M e (D*C) d := by
  obtain ⟨e,D,he,hE,hD,H⟩ := Damped.freq_budget (a:=a) hη hρ d
  refine ⟨e,D,he,hE,hD, fun {ι M C} h => ?_⟩; obtain ⟨g,hg,H⟩ := H h
  exact ⟨g,hg,fun hk p hp => H hk p fun i j => (hp i j).le⟩

namespace Emission
variable (h : Emission M η C d) (hk : k≤d) {p : Fin k → Momentum} (hp : ∀ i,p i ∈ Tube η)
include h hk hp
omit [DecidableEq a] in
lemma summable : Summable (fun i => (M i).monomial p) := by obtain ⟨g,hg,H⟩ := h; exact .of_norm_bounded hg.2.1 (H hk p hp)
omit [DecidableEq a] in
lemma bound (v : Fin k → CSpace a) : ‖source M p v‖ ≤ C * ∏ i, ‖v i‖ := by
  obtain ⟨g,hg,H⟩ := h; exact ((source M p).le_opNorm v).trans (mul_le_mul_of_nonneg_right ((tsum_of_norm_bounded hg.2.1.hasSum (H hk p hp)).trans hg.2.2) (by positivity))
omit [DecidableEq a] in
lemma smooth (v : Fin k → CSpace a) : ContDiffAt ℂ ω (fun p => source M p v) p := by
  have he : ∀ᶠ z : Fin k → Momentum in 𝓝 p, ∀ i,z i∈Tube η := eventually_all.mpr fun i => ((continuous_apply i).tendsto p).eventually ((Work.F07.stripOpen _).mem_nhds (hp i))
  obtain ⟨r,hr,H⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨g,hg,hB⟩ := h
  refine (Work.F02.analytic_series (fun i p => (M i).monomial p v) hr (fun i => ((M i).monomial_diff v).differentiable (by simp)) (hg.2.1.mul_right (∏ i, ‖v i‖)) (fun i z hz => ?_)).contDiffAt.congr_of_eventuallyEq (he.mono fun z hz => ContinuousMultilinearMap.tsum_eval (Emission.summable ⟨g,hg,hB⟩ hk hz) v)
  exact ((M i).monomial z |>.le_opNorm v).trans (by gcongr; exact hB hk z (H hz) i)
omit [Fintype a] [DecidableEq a] hp h hk in
lemma periodic (p : Fin k → Momentum) (w : Fin k → Cover) : source M (fun i => p i + reciprocal (w i)) = source M p := by simp only [source,Reader.monomial_period]
end Emission

private lemma args {η : ℝ} (h : 0<η) {p q s : Momentum} (hq : q∈Tube (η/3)) (hp : p∈Tube (η/3)) (hs : s∈Tube (η/3)) : q∈Tube η ∧ p∈Tube η ∧ s∈Tube η ∧ -q∈Tube η ∧ -(q+p)∈Tube η ∧ -(q+p+s)∈Tube η := ⟨tube_mono (by linarith) hq,tube_mono (by linarith) hp,tube_mono (by linarith) hs,tube_neg (tube_mono (by linarith) hq),tube_neg (tube_mono (by linarith) (tube_add hq hp)),tube_neg (tube_mono (by linarith) (tube_add (tube_add hq hp) hs))⟩

variable {U V : Matrix a b ℂ} (h : Emission M η C 4) (hη : 0<η)
include h hη
omit [DecidableEq a] in
lemma split_lit : Lit (splitVertex U V (fun _ => source M)) (η/3) := by
  constructor
  · intro q hq; obtain ⟨h₁,-,-,h₂,-⟩ := args hη hq hq hq
    refine ⟨analyticMatrix fun i j => (h.smooth (p:= ![-q,q]) (by decide) (by intro i; fin_cases i <;> assumption) ![U.col i, U.col j]).comp (f:=fun z => ![-z,z]) q (contDiffAt_pi.mpr (fun i => by fin_cases i <;> simp <;> fun_prop)), fun x => ?_⟩
    apply congr_arg (formMap U); convert Emission.periodic ![-q,q] ![-x,x] using 2; ext1 i; fin_cases i <;> simp [reciprocal_neg, add_comm]
  · intro q p v hq hp; obtain ⟨h₁,h₂,-,-,h₃,-⟩ := args hη hq hp hp
    refine ⟨analyticMatrix fun i j => (h.smooth (p:= ![p,-(q+p),q]) (by decide) (by intro i; fin_cases i <;> assumption) ![V *ᵥ v,U.col i,U.col j]).comp (f:=fun z => ![z.2,-(z.1+z.2),z.1]) (q,p) (contDiffAt_pi.mpr fun l => by fin_cases l <;> simp <;> fun_prop),fun x y => ?_⟩
    have ht : source M ![p+reciprocal y,-(q+reciprocal x+(p+reciprocal y)),q+reciprocal x] = source M ![p,-(q+p),q] := by
      convert Emission.periodic ![p,-(q+p),q] ![y,-(x+y),x] using 2; ext1 i; fin_cases i <;> simp [reciprocal_neg,reciprocal_add]; abel
    exact congr_arg (fun f : Roll a 3 => formMap U (f.curryLeft (V *ᵥ v))) ht
  intro q p s v w hq hp hs; obtain ⟨h₁,h₂,h₃,-,-,h₄⟩ := args hη hq hp hs
  refine ⟨analyticMatrix fun i j => (h.smooth (p:= ![p,s,-(q+p+s),q]) (by decide) (by intro i; fin_cases i <;> assumption) ![V *ᵥ v,V *ᵥ w,U.col i,U.col j]).comp (f:=fun z => ![z.2.1,z.2.2,-(z.1+z.2.1+z.2.2),z.1]) (q,p,s) (contDiffAt_pi.mpr fun l => by fin_cases l <;> simp <;> fun_prop),fun x y z => ?_⟩
  have ht : source M ![p+reciprocal y,s+reciprocal z,-(q+reciprocal x+(p+reciprocal y)+(s+reciprocal z)),q+reciprocal x] = source M ![p,s,-(q+p+s),q] := by
    convert Emission.periodic ![p,s,-(q+p+s),q] ![y,z,-(x+y+z),x] using 2; ext1 i; fin_cases i <;> simp [reciprocal_neg,reciprocal_add]; abel
  exact congr_arg (fun f : Roll a 4 => formMap U ((f.curryLeft (V *ᵥ v)).curryLeft (V *ᵥ w))) ht

omit h hη [DecidableEq a] in
lemma split_packet (U V : Matrix a b ℂ) : ∃ K : ℝ, 0<K ∧ ∀ {ι : Type} {M : ι → Reader a} {η C : ℝ}, Emission M η C 4 → 0<η → Packet (splitVertex U V (fun _ => source M)) (η/3) (K*C) := by
  let A := max 1 (∑ i, ‖U.col i‖)
  let B := max 1 ‖V.mulVecLin.toContinuousLinearMap‖
  have hA : 1≤A := le_max_left ..; have hB : 1≤B := le_max_left ..
  have he (i : b) : ‖U.col i‖ ≤ A := (Finset.single_le_sum (fun j (_:j∈Finset.univ) => norm_nonneg _) (Finset.mem_univ i)).trans (le_max_right ..)
  have hV (v : CSpace b) (hv : ‖v‖≤1) : ‖V *ᵥ v‖ ≤ B := (V.mulVecLin.toContinuousLinearMap.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv |>.trans (le_max_right ..))
  let K := matrixCost b b; have hK := matrixCost_nonneg b b
  refine ⟨(1+K)*B*B*A*A, by dsimp only [K]; positivity,fun {ι M η C} h hη => ?_⟩
  have hC : 0≤C := by obtain ⟨g,hg,-⟩ := h; exact (tsum_nonneg hg.1).trans hg.2.2
  refine ⟨split_lit h hη,by positivity,by dsimp only [K]; positivity,fun q hq => ?_,fun q p v hq hp hv => ?_,fun q p s v w hq hp hs hv hw => ?_⟩
  · obtain ⟨hh,-,-,ht,-⟩ := args hη hq hq hq
    refine (matrix_norm (Q:=C*(A*A)) (by positivity) (fun i j => ?_)).trans ?_
    · exact (h.bound (p:= ![-q,q]) (by decide) (by intro i; fin_cases i <;> assumption) ![U.col i,U.col j]).trans (by rw [Fin.prod_univ_two]; simp; gcongr; exacts [he _,he _])
    change K*_ ≤ _; rw [show (1+K)*B*B*A*A*C = (1+K)*(C*(A*A))*(B*B) by ring]; exact (mul_le_mul_of_nonneg_right (by linarith : K≤1+K) (by positivity)).trans (le_mul_of_one_le_right (by dsimp only [K]; positivity) (one_le_mul_of_one_le_of_one_le hB hB))
  · obtain ⟨hh,ht,-,-,hz,-⟩ := args hη hq hp hp
    refine (matrix_norm (Q:=C*(B*A*A)) (by positivity) (fun i j => ?_)).trans ?_
    · exact (h.bound (p:= ![p,-(q+p),q]) (by decide) (by intro i; fin_cases i <;> assumption) ![V *ᵥ v,U.col i,U.col j]).trans (by rw [Fin.prod_univ_three]; simp; gcongr; exacts [hV _ hv,he _,he _])
    change K*_ ≤ _; rw [show (1+K)*B*B*A*A*C = (1+K)*(C*(B*A*A))*B by ring]; exact (mul_le_mul_of_nonneg_right (by linarith : K≤1+K) (by positivity)).trans (le_mul_of_one_le_right (by dsimp only [K]; positivity) hB)
  obtain ⟨hh,ht,hr,-,-,hz⟩ := args hη hq hp hs
  refine (matrix_norm (Q:=C*(B*B*A*A)) (by positivity) (fun i j => ?_)).trans ?_
  · exact (h.bound (p:= ![p,s,-(q+p+s),q]) (by decide) (by intro i; fin_cases i <;> assumption) ![V *ᵥ v,V *ᵥ w,U.col i,U.col j]).trans (by rw [Fin.prod_univ_four]; simp; gcongr; exacts [hV _ hv,hV _ hw,he _,he _])
  change K*_ ≤ _; rw [show (1+K)*B*B*A*A*C = (1+K)*(C*(B*B*A*A)) by ring]; gcongr; simp

end Paths
end YM.Push.Loops
