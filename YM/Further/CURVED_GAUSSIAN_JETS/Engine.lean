import YM.Further.CURVED_GAUSSIAN_JETS.Bridge
import YM.Further.CURVED_GAUSSIAN_JETS.Doses
import YM.Further.CURVED_GAUSSIAN_JETS.Tracks
import YM.Next.FREE_KERNELS.Amend
import YM.Push.CUTOFF_PROJECTORS.Equations

/-!
# Matrix prices transferred to labelled ordered products (not just their sum)
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter Jets Lattice RG Wilson Precision Push.Uniform Progress.StationaryScenes
open Green (wt wt_pos)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I : Type*} [Fintype I] [DecidableEq I] {d k : ℕ}
variable {G : Gauge} {c n : Side} {a : I → Site n} {s : Jets.Weights a} {Q : Directions G c→Prop} {P : Prices} {V : Config G c} {A : Jets.Field G c I} {M R C : ℝ}

lemma guard_good (h : Good A k V) (i j : I) : Good (fun v=> Tracks.tag (A v) i j) k V := by intro x y; simp only [Tracks.tag,Matrix.single_apply]; split_ifs; exact h i j; exact contDiffAt_const
lemma guard_jet (l : Word G c) (A : Jets.Field G c I) (i j : I) : jet l (fun v=> Tracks.tag (A v) i j) V = Tracks.tag (jet l A V) i j := by
  ext x y; simp only [Tracks.tag,jet,Matrix.of_apply,Matrix.single_apply]; split_ifs; rfl; simp [Work.G07.left_const]
lemma guard_flow {A : ℝ → Jets.Field G c I} (h : Flow A V k) (i j : I) : Flow (fun u v=> Tracks.tag (A u v) i j) V k := by
  intro l hl x y; simp_rw [guard_jet, Tracks.tag,Matrix.single_apply]; split_ifs; exact h l hl i j; exact continuousOn_const
lemma cut_entry {B : Table I} (h : s.Costs (2*R) d B C) (hc : 0≤C) (i j : I) : s.Costs R d (Tracks.tag B i j) (C*Decay R (a i) (a j)) := by
  intro z; by_cases hz : z=i; swap
  · simp [Tracks.tag,Ne.symm hz]; exact mul_nonneg (mul_nonneg hc (decay_pos ..).le) (pow_nonneg (s.nonneg _) d)
  subst z
  simp only [Tracks.tag,Matrix.single_apply,true_and,abs_ite,abs_zero,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [show wt (s.width R d) (a i) (a j) = wt (s.width (2*R) d) (a i) (a j)*Decay R (a i) (a j) by unfold wt Weights.width Decay; rw [←Real.exp_add]; congr 1; ring,
      mul_right_comm, mul_right_comm C]
  exact mul_le_mul_of_nonneg_right (h.here i j) (decay_pos ..).le
lemma guard_cash (h : Cash s (2*R) k Q V A C) (hc : 0≤C) (i j : I) : Cash s R k Q V (fun v=> Tracks.tag (A v) i j) (C*Decay R (a i) (a j)) := by
  intro l hl hd; rw [guard_jet]; have hf := h l hl hd
  refine ⟨cut_entry hf.1 hc i j, ?_⟩
  rw [Tracks.tag,Matrix.transpose_single,decay_comm]; exact cut_entry hf.2 hc j i

variable {M' : Fin d → Jets.Field G c I} {C' : Fin d → ℝ}
def build (M' : Fin d → Jets.Field G c I) (v : Config G c) := engine fun i=> M' i v
lemma build_good (h : ∀ i, Good (M' i) k V) : Good (build M') k V := by
  induction d with | zero => exact Good.const (1 : Table I) | succ d ih=> unfold build; simp_rw [engine_next]; exact (h 0).prod (ih (M':=Fin.tail M') fun i=> h i.succ)
lemma build_flow {M' : Fin d → ℝ → Jets.Field G c I} (h : ∀ i, Flow (M' i) V k) (hg : ∀ i {u}, 0<u → Good (M' i u) k V) : Flow (fun u => build (fun i=> M' i u)) V k := by
  induction d with
  | zero => unfold build; simp_rw [engine_zero]; exact fun _ _ _ _=> continuousOn_const
  | succ d ih => unfold build; simp_rw [engine_next]; exact Flow.prod (A:=M' 0) (B:=fun u=>build fun i=> M' i.succ u) (h 0) (ih (M':=Fin.tail M') (fun i=>h i.succ) (fun i {_} hu => hg i.succ hu)) (fun u hu => ⟨hg 0 hu,build_good fun i=>hg i.succ hu⟩)
lemma build_cash (h : ∀ i, Cash s R k Q V (M' i) (C' i)) (hg : ∀ i, Good (M' i) k V) (hc : ∀ i, 0≤C' i) (hr : 0≤s.width R k) : Cash s R k Q V (build M') (∏ i,s.pay k*C' i) := by
  induction d with
  | zero => rw [show (∏ i, s.pay k*C' i) = 1 by simp]; exact cash_one
  | succ d ih => unfold build; simp_rw [engine_next,Fin.prod_univ_succ (fun i=>s.pay k*C' i)]; exact (h 0).product (B:=build (Fin.tail M')) (ih (fun i=> h i.succ) (fun i=>hg i.succ) (fun i=> hc i.succ)) (hg 0) (build_good fun i=>hg i.succ) hr (hc _) (Finset.prod_nonneg fun i _=>mul_nonneg (s.pay_pos _).le (hc _))

def reserved (p : Run I d) (M' : Fin d → Jets.Field G c I) (v : Config G c) := reserve p fun i=> M' i v
lemma reserved_good (h : ∀ i, Good (M' i) k V) (p : Run I d) : Good (reserved p M') k V := build_good (fun i=> guard_good (h i) _ _)
lemma reserved_flow {M' : Fin d → ℝ → Jets.Field G c I} (h : ∀ i, Flow (M' i) V k) (hg : ∀ i {u}, 0<u → Good (M' i u) k V) (p : Run I d) : Flow (fun u=> reserved p fun i=>M' i u) V k := build_flow (fun i=> guard_flow (h i) _ _) (fun i {_} hu=> guard_good (hg i hu) _ _)

def decay (a : I → Site n) (R : ℝ) (p : Run I d) := fare p (fun _=> Matrix.of fun i j=> Decay R (a i) (a j))
lemma decay_strict (p : Run I d) : 0<decay a R p := by unfold decay fare; simp only [of_apply]; exact Finset.prod_pos (fun _ _=>decay_pos ..)
lemma decay_twice (p : Run I d) : decay a R p=decay a (R/2) p * decay a (R/2) p := by
  unfold decay fare; rw [←Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _=> by simp only [of_apply,Decay,←Real.exp_add]; congr 1; ring
lemma decay_cons {a : I → Site n} {R : ℝ} (p : Run I (d+1)) : decay a R p = Decay R (a (p 0)) (a (Fin.tail p 0))* decay a R (Fin.tail p) := fare_next ..
lemma reserved_cash (p : Run I d) (h : ∀ i, Cash s (2*R) k Q V (M' i) (C' i)) (hg : ∀ i, Good (M' i) k V) (hc : ∀ i, 0≤C' i) (hr : 0≤s.width R k) : Cash s R k Q V (reserved p M') ((∏ i,s.pay k*C' i)*decay a R p) := by
  unfold decay fare; simp only [← Finset.prod_mul_distrib, of_apply,mul_assoc]; exact build_cash (fun i=>guard_cash (h i) (hc i) _ _) (fun i=>guard_good (hg i) _ _) (fun i=>mul_nonneg (hc i) (decay_pos ..).le) hr
lemma reserved_read (p : Run I d) (M' : Fin d → Jets.Field G c I) : reserved p M' V (p 0) (p (Fin.last _))=fare p fun i=>M' i V := bought ..
end YM.Further.CurvedGaussianJets.Tracks
