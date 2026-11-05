import YM.ProjectorNext.PROJECTOR_CALIBRATION.Picks

/-! # Weight-triangular exposed law -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Function Filter Tensor Work Labels Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}
namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)

def tail (x : Snap G d) (t : ℝ) : Snap G d := fun i => ∑ j : Level d, if i≤j then
    t^(j.val-i.val) • M.liftLeg i (firing j (x j)) else 0

private lemma relower (x : Snap G d) (j i : Level d) (h : j < i) :
    M.liftLeg i (firing j (x j))=0 := by
  have hv : firing j (x j)∈cutSpace G i := by
    intro k hk; change Pi.single j _ k = _; exact Pi.single_eq_of_ne (h.trans hk).ne' _
  change M.liftAll (firing j (x j)) i = _
  rw [M.diagonal i _ hv, show (firing j (x j)) i=0 from Pi.single_eq_of_ne h.ne' _, map_zero]

lemma collect (x : Snap G d) (t : ℝ) : M.liftAll (stretch t x) = stretch t (M.tail x t) := by
  have he : stretch t x = ∑ j : Level d, t^(j.val+2) • firing j (x j) := by
    have hs (j : Level d) : t^(j.val+2) • firing (G:=G) j (x j) = firing j ((t^(j.val+2)) • x j) := (map_smul ..).symm
    funext i
    simp_rw [hs,Finset.sum_apply]
    change t^(i.val+2) • x i = ∑ j : Level d, ((firing j) (t^(j.val+2) • x j)) i
    convert Eq.symm ((Finset.sum_pi_single i (fun j => t^(j.val+2) • x j) Finset.univ).trans (if_pos (Finset.mem_univ _))) using 1
    rfl
  rw [he,map_sum]
  simp_rw [map_smul]
  funext i; rw [Finset.sum_apply]
  change ∑ j : Level d, (t^(j.val+2)) • M.liftLeg i (firing j (x j)) = _
  simp_rw [stretch,LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, tail,Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : i≤j
  · rw [if_pos hj,smul_smul, ← pow_add, show (i.val+2)+(j.val-i.val)=j.val+2 by change i.val≤j.val at hj; omega]
  rw [if_neg hj, M.relower _ _ _ (lt_of_not_ge hj), smul_zero,smul_zero]

lemma tail_axis (x : Snap G d) : M.tail x 0=x-M.U x := by
  funext i
  unfold tail
  rw [Finset.sum_eq_single i]
  · have h : firing i (x i)∈cutSpace G i := fun k hk => Pi.single_eq_of_ne hk.ne' _
    rw [if_pos (le_refl i),Nat.sub_self,pow_zero,one_smul]
    change M.liftAll (firing i (x i)) i = _; rw [M.diagonal i _ h]
    change (firing i (x i) i) - M.Q i (firing i (x i) i) = x i-M.Q i (x i)
    simp [firing]
  · intro j _ hj
    split
    · rename_i h
      rw [zero_pow (M₀:=ℝ) (Nat.sub_ne_zero_of_lt (Fin.lt_def.mp (lt_of_le_of_ne h hj.symm))), zero_smul]
    rfl
  simp

private lemma power_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (y : E) : ContDiff ℝ ω (fun t : ℝ => t^n • y) := (contDiff_id.pow n).smul contDiff_const

lemma tail_smooth (x : Snap G d) : ContDiff ℝ ω (M.tail x) := by
  apply contDiff_pi.mpr
  intro i; refine ContDiff.sum (s:=Finset.univ (α:=Level d)) ?_; intro j _; split
  · exact power_smooth ..
  exact contDiff_const

private def freeform (i : F.Index) (A : Snap G d) t := Cross.mix (shade F i) M.U A (M.tail A t)

private lemma admits (i : F.Index) (A : Snap G d) (t : ℝ) : Cross.mix (shade F i) M.U (stretch t A) (M.liftAll (stretch t A)) =
    t^(F.grades i).1 • M.freeform F i A t := by
  rw [M.collect]; unfold freeform
  exact Cross.scaled_mix (shade F i) M.U (stretch t (G:=G) (d:=d)) (t^(F.grades i).1) (exposed (F.pure i) t) (fun X => by
    funext j; change M.Q j (t^(j.val+2) • X j) = _; rw [map_smul]; rfl) _ _

/- h coefficient with residual completely smooth. Can use the scalar
Leibniz formula here: convert ℝ^n scaling explicitly to ℂ. -/
lemma in_weight (k n : ℕ) (hk : k ≤ n) (z : ℝ → ℂ) (h : ContDiff ℝ ω z) :
    iteratedDeriv k (fun t : ℝ => t^n • z t) 0 = if k=n then (↑(k.factorial) : ℝ) • z 0 else 0 := by
  let f (t : ℝ) := Complex.ofRealCLM (t^n)
  have hf : ContDiff ℝ ω f := Complex.ofRealCLM.contDiff.comp (contDiff_id.pow n)
  have he (j : ℕ) : iteratedDeriv j f 0 = if j=n then ((j.factorial:ℕ) : ℂ) else 0 := by
    change iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ fun x : ℝ => x^n) 0 _ = _
    rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (f:=fun t : ℝ => t^n) (by exact contDiffAt_id.pow n) le_rfl]
    change ((iteratedDeriv j (fun t : ℝ => t^n) 0:ℝ):ℂ) = _
    rw [iteratedDeriv_fun_pow_zero]; split_ifs <;> simp_all
  change iteratedDeriv k (fun t => f t*z t) 0 = _
  rw [iteratedDeriv_fun_mul (hf.of_le le_top).contDiffAt (h.of_le le_top).contDiffAt]
  simp_rw [he]
  by_cases hh : k=n
  · subst n; rw [Finset.sum_eq_single k]; simp [Complex.real_smul]; intro j _ hj; simp [hj]; simp
  rw [if_neg hh]; apply Finset.sum_eq_zero; intro i hi
  have ht : i ≠ n := (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) (lt_of_le_of_ne hk hh)).ne
  simp [ht]

theorem crossed (i : F.Index) (J : Jet G) (n : ℕ) (hk : n ≤ (F.grades i).1) :
    iteratedDeriv n (fun t => Cross.mix (shade F i) M.U (course J t) (M.liftAll (course J t))) 0 =
      if n=(F.grades i).1 then (↑(n.factorial) : ℝ) • (Labels.read J (F.basis i).val - tally (F.basis i) (M.U (trunk d J))) else 0 := by
  simp_rw [course_eq, admits M F i, in_weight n _ hk (M.freeform F i (trunk d J))
    (contDiff_iff_contDiffAt.mpr fun _ => Cross.mix_smooth (shade F i) M.U contDiffAt_const (M.tail_smooth (trunk d J)).contDiffAt)]
  simp_rw [freeform,M.tail_axis,Cross.restore] -- unnecessary
  rw [label_leg (F.pure i),label_leg (F.pure i), tally, racts]

end Machine
end YM.ProjectorNext.Calibration
