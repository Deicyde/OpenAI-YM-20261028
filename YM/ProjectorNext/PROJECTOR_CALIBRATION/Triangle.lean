import YM.ProjectorNext.PROJECTOR_CALIBRATION.Expose
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Model

/-! # Triangle by the engineering-order probes on *all* real jets -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Source.Drops Function Filter Labels Work Tensor Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {H : Hol G} {d : ℕ}

section Slots
variable (F : Labels.Frame G d)

private lemma recombine (x : F.Coeff) : F.coords.symm x = ∑ i, x i • F.basis i := by
  have he := F.basis.sum_repr (F.coords.symm x)
  symm
  convert he using 2
  rename_i i h; change x i • _ = F.coords (F.coords.symm x) i • _; rw [F.coords.apply_symm_apply]

private lemma basis_value (i : F.Index) (J : Jet G) (n : ℕ) :
    iteratedDeriv n (fun t => Labels.read (scaleJet J t) (F.basis i).val) 0 =
    if n=(F.grades i).1 then (↑(n.factorial) : ℂ)*Labels.read J (F.basis i).val else 0 := by
  simp_rw [read_weight (F.pure i)]
  rw [iteratedDeriv_smul_const (contDiffAt_id.pow _) _, iteratedDeriv_fun_pow_zero]; split_ifs <;> simp_all [Complex.real_smul]

/-- Engineering-filtered source and probe formula, even k>D if useful
(the label is already truncated). -/
lemma sources (x : F.Coeff) (J : Jet G) (k : ℕ) :
    iteratedDeriv k (fun t => Labels.read (scaleJet J t) (F.coords.symm x).val) 0 =
    (↑(k.factorial) : ℂ) * ∑ i : F.Index, if k=(F.grades i).1 then x i * Labels.read J (F.basis i).val else 0 := by
  simp_rw [recombine F,AddSubmonoidClass.coe_finsetSum,map_sum, Submodule.coe_smul_of_tower, map_smul]
  have he (i : F.Index) : ContDiffAt ℝ (k : WithTop ℕ∞) (fun t => x i*Labels.read (scaleJet J t) (F.basis i).val) 0 :=
    contDiffAt_const.mul (read_smooth J (F.basis i).val _).contDiffAt
  simp only [smul_eq_mul]
  rw [iteratedDeriv_fun_sum (fun i _ => he i),Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_const_mul _ (read_smooth J _ _).contDiffAt, basis_value]
  split_ifs <;> ring

lemma witnessed (x : F.Coeff) (J : Jet G) (k : Fin (d+1)) : probe F (J,k) x =
    (↑(k.val.factorial) : ℂ) * ∑ i : F.Index, if k.val=(F.grades i).1 then x i * Labels.read J (F.basis i).val else 0 :=
    (probe_eq F _ _).trans (sources F x J k.val)

lemma distinguishes {x y : F.Coeff} {i : F.Index} (h : ∀ J : Jet G,
    let k := ⟨(F.grades i).1,Nat.lt_succ_of_le (F.bound i)⟩
    probe F (J,k) x=probe F (J,k) y) : x i=y i := by
  let k := (F.grades i).1
  let p (x : F.Coeff) : Label G d := ∑ j : F.Index, if k=(F.grades j).1 then x j • F.basis j else 0
  have he (x : F.Coeff) (J) : Labels.read J (p x).val = ∑ i : F.Index, if k=(F.grades i).1 then x i * Labels.read J (F.basis i).val else 0 := by
    unfold p; rw [AddSubmonoidClass.coe_finsetSum,map_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul]
    exact map_zero _
  have hp : p x=p y := by
    refine Subtype.ext (Labels.eval_ext _ _ fun J => ?_)
    rw [he,he]; have hz := h J
    simp_rw [witnessed] at hz
    exact mul_left_cancel₀ (show (k.factorial:ℂ)≠0 by exact_mod_cast Nat.factorial_ne_zero k) hz
  have hx (x : F.Coeff) : F.basis.repr (p x) i = x i := by
    simp_rw [p,map_sum,Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · simp [k]
    · intro j _ hj; split_ifs <;> simp [Finsupp.single_eq_of_ne hj.symm]
    simp
  rw [← hx x,← hx y,hp]
end Slots

namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)

/- k-tier equation cancellation, no assumption the frame itself chosen
to start with equation basis. Read shell contribution at all weight h
(including k=0). -/
lemma canceled (w : equationSpace F) (J : Jet G) (k : ℕ) :
    (∑ i : F.Index, if k=(F.grades i).1 then w.val i * tally (F.basis i) (M.U (trunk d J)) else 0) = 0 := by
  let A := M.U (trunk d J)
  let j := expand d A
  have ht (t : ℝ) : Labels.read (scaleJet j t) (F.coords.symm w.val).val = 0 := by
    have hU (x : Snap G d) : Labels.read (expand d (M.U x)) (F.coords.symm w.val).val = 0 := by
      obtain ⟨Y,hY⟩ := M.toSplit.constrained x
      rw [hY]; exact (equation_iff F).1 w.2 _
    have he : scaleJet j t = expand d (M.U (stretch t (trunk d J))) := by
      unfold j; rw [← dilated]
      congr 1
      funext l; change (t^(l.val+2)) • (M.Q l _) = M.Q l ((t^(l.val+2)) • _); rw [map_smul]
    rw [he]; exact hU _
  have he := sources F w.val j k
  rw [funext ht] at he
  rw [show iteratedDeriv k (fun _ : ℝ => (0:ℂ)) 0=0 by change iteratedDeriv k 0 0=0; simp] at he
  apply mul_left_cancel₀ (show (k.factorial:ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero k)
  rw [mul_zero]
  exact he.symm

theorem certified : triangular (M.trophy F) := by
  intro x i h
  apply distinguishes F
  intro J
  let k : Fin (d+1) := ⟨(F.grades i).1,Nat.lt_succ_of_le (F.bound i)⟩
  change probe F (J,k) _ = _
  rw [M.spends F x (J,k),witnessed F (x:F.Coeff)]
  have he (j : F.Index) : x.val j*M.calendar F j (J,k) 0 0 =
      (↑(k.val.factorial):ℂ)*((if k.val=(F.grades j).1 then x.val j*Labels.read J (F.basis j).val else 0)-
        if k.val=(F.grades j).1 then x.val j*tally (F.basis j) (M.U (trunk d J)) else 0) := by
    by_cases ht : (F.grades j).1<k.val
    · simp only [h j ht,zero_mul,ite_self,sub_self,mul_zero]
    rw [M.as_recorded]; dsimp only; rw [M.crossed F j J k.val (le_of_not_gt ht)]
    split_ifs
    · simp [Complex.real_smul]; ring
    ring
  simp_rw [he,← Finset.mul_sum, Finset.sum_sub_distrib, M.canceled,sub_zero]; rfl
end Machine
end YM.ProjectorNext.Calibration
