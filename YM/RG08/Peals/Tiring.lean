import YM.RG08.Peals.Stroke

/-!
# Finite heat polynomial follows literal theory and at every true period

Finite covariance includes wraps on every contraction. `m` variant of a
chirp cannot be sent to the cover via just holding coarsest period fixed! -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α I : Type} {σ θ A B C : ℝ} {r n : ℕ} {m : Side} {M : Row α α}
variable [Fintype α] [DecidableEq α]
variable {F H : Shale α (r+2)}

omit [DecidableEq α] in
private lemma swap_sum_series {a : ℕ} {u : Shale α a} (h : Summable u) (v : Fin a → PAC α m) :
    ∑ z, (∑' j,u j * rosary v z j)=∑' j, (∑ z,u j*rosary v z j) := (Summable.tsum_finsetSum (s:=univ) (fun z _=>bead_summable _ v h z)).symm
private def take2 (i j : Co m α) (x : PAC α m) : Fin (r+2) → PAC α m := Fin.cons (zpk i) (Fin.cons (zpk j) (fun _=>x))

private lemma two_summed (h : Tunable F) (u : Co m α) (i) (x : PAC α m) : Summable
    (fun z => (∑ y, F z * rosary (take2 u i x) y z)) := Summable.congr
      (summable_sum (s:=univ) (fun y _=>bead_summable F (take2 u i x) h.1 y)) (fun _=> rfl)
private lemma chill (b : Beads α (r+2)) (M : Row α α) (z : Site m) (x : PAC α m) :
    (∑ i,∑ j, M.acts m i j * (F b*rosary (take2 i j x) z b))=
      (F*tuneS M (some m) : Shale α (r+2)) b*rosary (fun _=> x) z (stems b) := by
  let u := silks z b 0; let v := silks z b (Fin.succ (0:Fin _))
  rw [sum_eq_single u,sum_eq_single v]; swap
  · intro j _ hj; unfold rosary take2; rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    change _*(F b*(_*((zpk j v)*_)))=_; rw [show zpk j v=0 from Pi.single_eq_of_ne hj.symm _]; ring
  swap; · simp
  swap
  · intro j _ hj; apply sum_eq_zero; intro i _; unfold rosary take2; rw [Fin.prod_univ_succ]; change _*(F b*(zpk j u *_))=_; rw [show zpk j u=0 from Pi.single_eq_of_ne hj.symm _]; ring
  swap; · simp
  unfold rosary take2; rw [Fin.prod_univ_succ,Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,u,v, zpk, Pi.single_eq_same,one_mul,Pi.mul_apply]
  rw [tuneS,stroke_trans M _ _ _ z]; unfold silks; rw [← mul_assoc,mul_comm _ (F b)]; rfl
set_option maxHeartbeats 300000 in
lemma tiring {M : Row α α} (h : Whole M) (e : Tunable F) (m : Side) :
    stanza (chirp M (some m) F) m=lap (M.acts m) (stanza F m) := by
  rw [chirp,stanza_scale _ (score_summable (rumba_summable _ e.1 h)),stanza_score]
  swap; · exact rumba_summable _ e.1 h
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,stanza, Tensor.diagonal]; -- avoid inside lap ...
  rw [rumba,recital_pool _ (spinS _ e.1 h)]
  let V := recital F m
  have hx (i j : Co m α) : Analysis.D (zpk j) (Analysis.D (zpk i) (Tensor.diagonal V)) x =
      ((↑(r+2:ℕ):ℝ)*(↑(r+1:ℕ):ℝ))*recital F m (take2 i j x) := DDfade (zpk i) (zpk j) V (e.2.2 m) x
  change _=lap (M.acts m) (Tensor.diagonal V) x
  simp_rw [lap,hx,mul_left_comm (M.acts m _ _)]; simp_rw [← Finset.mul_sum]; rw [← mul_assoc, ← mul_assoc _ (↑(r+2:ℕ):ℝ)]
  have hh : ((1/2:ℝ)*↑(r+2:ℕ)*↑(r+1:ℕ))=batting r := by push_cast; rfl
  rw [hh]; congr 1
  simp_rw [recital_eval _ e.1,swap_sum_series e.1,← tsum_mul_left];
  have he (i) (j) : Summable fun k => M.acts m i j * (∑ y, F k*rosary (take2 i j x) y k) := (two_summed e ..).mul_left _
  simp_rw [← Summable.tsum_finsetSum (f:=fun j (k : Beads α (r+2))=> M.acts m _ j * _) (fun j _=> he _ j)]; -- implicit
  rw [← Summable.tsum_finsetSum (s:=univ) (fun i _=> summable_sum (s:=univ) fun j _=> he i j)]
  have hG (z : Site m) : Summable fun j => (F * tuneS M (some m) : Shale α (r+2)) (j:Beads α (r+2)) * rosary (fun _=> x) z (stem1 (stem1 j)) := sum_bounded (spinS _ e.1 h) (fun i=> rosary_bill (fun _ : Fin r=> x) _ _)
  rw [← Summable.tsum_finsetSum (fun z _=> hG z)]; apply tsum_congr; intro b
  symm; simp_rw [Finset.mul_sum];
  have ht (i : Co m α) : ∑ j:Co m α,∑ y,M.acts m i j*(F b*rosary (take2 i j x) y b)=_ := Finset.sum_comm
  simp_rw [ht]; rw [sum_comm]; apply sum_congr rfl; intro z _; exact chill b M z x
end YM.RG08
