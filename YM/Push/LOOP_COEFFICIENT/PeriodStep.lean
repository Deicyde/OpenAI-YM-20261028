import YM.Push.LOOP_COEFFICIENT.LoopPorts

/-!
# Pass all comparisons through one common sequence of real meshes

`Fee` need only have the unsigned Signature. Never discard the rooted-frame
gradient correction at finite period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Set Filter Lattice Precision RG Wilson Tree Bloch Laurent Exterior
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {a : Type} [Fintype a] [DecidableEq a] {L : Side} {s f : ℕ → Side}
    {R : LoopData G L} {η C σ D Λ : ℝ} {p : Clip} {W : PathData G} {S : ∀ i,StepData (s i) (f i)}
variable {F : ∀ i, Forest (S i).ratio} {ρ : ∀ i, fieldDir G (s i) 1 → AxisChart G (F i)} {P : ChartRatio G}
    {hg : ∀ i, (f i).val = (s i).val * L.val}

def ratioStep (hg : ∀ i, (f i).val = (s i).val * L.val) (i : ℕ) : Ratio (s i) (f i) := ⟨L,hg i⟩
lemma expands_fine (hs : Expands s) (hg : ∀ i, (f i).val = (s i).val * L.val) : Expands f := by
  exact tendsto_atTop_mono (f:=fun i => (s i).val) (fun i => by change (s i).val ≤ (f i).val; rw [hg i]; exact Nat.le_mul_of_pos_right _ L.property) hs

open scoped Matrix.Norms.L2Operator in
lemma logKernel_cont {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] {V : Vertex a b b} (h : LogStrip V η C) (p : Momentum) (hp : star p=p) : ContinuousAt (logKernel V) p :=
  (logKernel_analytic h (Work.F07.realStrip _ (half_pos h.width) hp)).continuousAt

open scoped Matrix.Norms.Frobenius in
lemma Synced.mirrors {E F : ℕ → Type} [∀ i, Fintype (E i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (F i)] {b : Type} [Fintype b] [DecidableEq b]
    {A : ∀ i, Grid (s i) (E i) a} {B : ∀ i, Grid (s i) (F i) b} {X : ∀ i, (E i → ℝ) → Matrix (F i) (F i) ℝ} {V : Vertex a b b} (hs : Expands s)
    (h : ∀ i, Synced (A i) (B i) (B i) (actualMatrix (X i)) V) (hv : LogStrip V η C) (hX : ∀ i, ContDiffAt ℝ ω (X i) 0) : Mirrors A A (fun i => Coeff (ld ∘ X i)) (logKernel V) :=
    compares_mirror (fun i => log_compares (hX i) (h i) hv) (logKernel_cont hv) (exp_error_limit hs (show 0<η/8 by linarith [hv.width]) _)

namespace LoopData
variable (hs : Expands s) (hr : R.Regular η C) (hu : ∀ i, R.Uses (g:=ratioStep hg i) (S i) p W)
    (ha : ∀ i, Admission (F i) (ρ i) p W (R.lift (g:=ratioStep hg i)) P)

include hs hr hu ha
open scoped Matrix.Norms.L2Operator in
lemma signature (hw : W.Bounds p σ D Λ) (hf : η/L.val ≤ σ) : Signature G true (R.target W) :=
  branch_signature hs ha fun t => compares_mirror (fun i => (hu i).compare_branch hr (ha i) (t i)) (fun _ hp => (hr.target_diff hw hf (Work.F07.realStrip _ (half_pos hr.joint.width) hp)).continuousAt)
    (exp_error_limit hs (show 0<η/8 by linarith [hr.joint.width]) (R.meshCost η C))

private def μ := (L.val:ℝ)⁻¹
omit hs hr ha hu in
private lemma μ_pos : 0 < μ (L:=L) := by unfold μ; positivity

omit ha in
lemma fine_signature (hw : W.Bounds p σ D Λ) (hG : G.Simple) : Signature G false (fineKernel R.vector R.ghost) := by
  have hf := expands_fine hs hg
  have hη : 0 < η/L.val/8 := by linarith [hr.vector.width]
  have he i : IsUnit (reference (μ (L:=L)) p W (1:Config G (f i))) := by rw [show μ (L:=L) = mu (S i) from (ratio_mu (S i) (ratioStep hg i)).symm]; exact (hu i).refUnit hr
  apply fee_signature μ_pos hG hw hf he
  have h₁ := Synced.mirrors hf (fun i => (hu i).vector) hr.vector (fun _ => onRef_diff hw mu_pos)
  have h₂ := Synced.mirrors hf (fun i => (hu i).ghost) hr.ghost (fun _ => onGhost_diff)
  have hm := (h₁.smul (1/2:ℂ)).sub h₂
  change Mirrors _ _ (fun i => Coeff (fee (n:=f i) _ p W)) _
  simpa only [show ∀ i, mu (S i) = μ (L:=L) from fun i => ratio_mu (S i) (ratioStep hg i),fee_coeff hw (μ_pos (L:=L)) (he _)] using! hm

open scoped Matrix.Norms.L2Operator in
omit ha hs hu in
private lemma lift_cont (z : Momentum) (hz : star z=z) (k : Site L) : ContinuousAt (fun z => R.rays z k) z := (hr.rays_diff (Work.F07.realStrip _ (half_pos hr.joint.width) hz) k).continuousAt

omit ha in
lemma collect_ref (hw : W.Bounds p σ D Λ) {z : Momentum} (hz : star z = z) :
    logKernel R.ref z = collectPair R.rays (logKernel R.vector) z := by
  have hf := expands_fine hs hg
  have hη := hr.ref.width; have hη' := hr.vector.width
  have hcomp i := log_compares (onRef_diff hw mu_pos) (hu i).vector hr.vector
  have he := Synced.mirrors hf (fun i => (hu i).vector) hr.vector (fun _ => onRef_diff hw mu_pos)
  let V i := Coeff (ld ∘ onRef (n:=f i) p W (mu (S i)))
  let A i := cmat (liftMatrix G (R.lift (g:=ratioStep hg i)))
  let M i := linksGrid G (s i); let B i := linksGrid G (f i)
  have heq (i) : Coeff (ld ∘ onLarge p W (mu (S i)) (R.lift (g:=ratioStep hg i))) = (A i).transpose * V i * A i := large_coeff hw mu_pos ((hu i).refUnit hr)
  have hp i : Projects (ratioStep hg i) (B i) (M i) (A i) R.rays := A0_projects (g:=ratioStep hg i) (G:=G) R.column (Row.rights _ _ hr.col hη.le)
  have hr' := mirrors_pull hg hp (fun i => (hcomp i).off (M:=B i) (X:=V i)) he (lift_cont hr)
  have hl := Synced.mirrors hs (fun i => (hu i).ref) hr.ref (fun _ => onLarge_diff hw mu_pos)
  simp_rw [heq] at hl; exact hl.unique hr' hs hz

open scoped Matrix.Norms.Frobenius in
lemma drift_ref (hw : W.Bounds p σ D Λ) {H : Precision.Bed} (hh : H.metric.strip η C)
    (hA : ∀ i, mean (S i) * R.lift (g:=ratioStep hg i) = 1 - (S i).kernel.penalty⁻¹ • Precision.K (H.metric.acts (s i))) {z : Momentum} (hz : star z=z) :
    logKernel R.joint z = logKernel R.base z + driftKernel (-kineticSymbol G H.metric) (kernelOf (respTrace R.charge)) (kernelOf (reverseTrace R.charge)) z := by
  let t (i) : (S i).Choices := Classical.arbitrary _
  have hη := hr.base.width
  have hl := Synced.mirrors hs (fun i => (hu i).joint (t i)) hr.joint (fun i => onVector_diff (ha i).branches hw)
  choose χ hχ hχ' using fun i => (hu i).base (t i)
  have hc := Synced.mirrors hs hχ' hr.base (fun i => onAdjusted_diff (ha i) (hχ i))
  simp_rw [show ∀ i, Coeff (ld ∘ onAdjusted p W (t i) (R.lift (g:=ratioStep hg i)) (χ i)) = Coeff (fun b => ld (onBase p W (t i) (R.lift (g:=ratioStep hg i)) b)) from fun i => Coeff.congr (adjusted_log (hχ i))] at hc
  obtain ⟨_,_,hv⟩ := hr.charge
  exact hl.unique (drift_mirror t hs ha (fun i => (hu i).charge (t i)) hv hc hA hh hη) hs hz
end LoopData
end YM.Push.Loops
