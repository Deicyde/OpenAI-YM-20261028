import YM.Push.LOOP_COEFFICIENT.Paths.Hessian
import YM.Push.LOOP_COEFFICIENT.Paths.Reader

/-!
# Routing anchored translation Hessians
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Filter Set Matrix Lattice Laurent Bloch Exterior RG Complex Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {a b J E ι : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype J] [DecidableEq J] [Fintype E]
    {n : Side} {A : Grid n E a} {B : Grid n J b}

omit [DecidableEq J] in
lemma test_routed [DecidableEq E] {i j : Site n} {S : Matrix E J ℂ} {T : Matrix a b ℂ}
    (h : ∀ k x y, (plane A k *ᵥ x) ⬝ᵥ (S *ᵥ plane B j *ᵥ y) = if k=-i then (n.val:ℂ)^4 • (x ⬝ᵥ T *ᵥ y) else 0) : Routed A B i j S T := by
  have he k : pick A k * (S * plane B j) = pick A k * (plane A i * T) := by
    rw [← Matrix.mul_assoc _ _ T,pick_plane]
    refine pairing_ext fun x y => ?_; rw [← mulVec_mulVec,pick, smul_mulVec,dotProduct_smul,Matrix.dotProduct_mulVec, vecMul_transpose, ← mulVec_mulVec,h]; split <;> split <;> simp_all [side_ne n]
  rw [Routed, ← Matrix.one_mul (S * _),← plane_pick A,Matrix.sum_mul]
  calc
    _ = (∑ k,plane A k * pick A k) * (plane A i * T) := by simp_rw [Matrix.sum_mul,Matrix.mul_assoc,he]
    _ = _ := by rw [plane_pick,Matrix.one_mul]

variable {N P : Matrix E J ℝ} {U V : Matrix a b ℂ}
    {g : (E → ℝ) → ℝ} {M : ι → Reader a} {η ρ C : ℝ} (h : Damped M η ρ C)
    (hg : ContDiffAt ℝ ω g 0) (hf : ∀ᶠ x in 𝓝 0, (g x : ℂ) = total M A (cvec x))
    (hN : ∀ i : Site n, Routed A B i i (cmat N) U) (hP : ∀ i : Site n, Routed A B i i (cmat P) V)

include h hg hf hN
lemma base_routed {q : Momentum} {j : Site n} (hq : Matches q j) : Routed B B j j (actualMatrix (bank N P g)).base
    ((splitVertex U V (fun _ => source M)).base q) := by
  refine test_routed fun k x y => ?_; rw [bank_base hg h.total_diff hf,(hN k).vector,(hN j).vector]
  have h' {s} (hs : Matches s k) : iteratedFDeriv ℂ 2 (total M A) 0 ![plane A k *ᵥ U *ᵥ x, plane A j *ᵥ U *ᵥ y] = if k=-j then (n.val:ℂ)^4 • source M ![s,q] ![U *ᵥ x, U *ᵥ y] else 0 := by
    have H := h.total_plane (A:=A) (r:= ![k,j]) (p:= ![s,q]) (by intro i; fin_cases i <;> first | exact hs | exact hq) ![U *ᵥ x,U *ᵥ y]
    erw [Fin.sum_univ_two,ite_cond_congr (propext (show k+j=0 ↔ k=-j from eq_neg_iff_add_eq_zero.symm))] at H
    convert H using 2; ext1 i; fin_cases i <;> rfl
  split
  · rename_i he; subst k; rw [h' hq.neg,if_pos rfl,splitVertex,form_pair]
  · rename_i he; rw [h' (mon_matches k), if_neg he]

include hP
lemma one_routed {p q : Momentum} {i j : Site n} (hq : Matches q j) (hp : Matches p i) (v : CSpace b) : Routed B B (j+i) j
    ((actualMatrix (bank N P g)).lin (plane B i *ᵥ v)) ((splitVertex U V (fun _ => source M)).one q p v) := by
  refine test_routed fun k x y => ?_; rw [bank_one hg h.total_diff hf,(hN k).vector,(hN j).vector,(hP i).vector]
  have h' {s} (hs : Matches s k) : iteratedFDeriv ℂ 3 (total M A) 0 ![plane A i *ᵥ V *ᵥ v, plane A k *ᵥ U *ᵥ x, plane A j *ᵥ U *ᵥ y] = if k=-(j+i) then (n.val:ℂ)^4 • source M ![p,s,q] ![V *ᵥ v,U *ᵥ x, U *ᵥ y] else 0 := by
    have H := h.total_plane (A:=A) (r:= ![i,k,j]) (p:= ![p,s,q]) (by intro l; fin_cases l <;> first | exact hp | exact hs | exact hq) ![V *ᵥ v,U *ᵥ x,U *ᵥ y]
    erw [Fin.sum_univ_three,ite_cond_congr (propext (show i+k+j=0 ↔ k=-(j+i) by rw [eq_neg_iff_add_eq_zero, show i+k+j=k+(j+i) by abel]))] at H
    convert H using 2; ext1 i; fin_cases i <;> rfl
  split
  · rename_i he; subst k; rw [h' (hq.add hp).neg,if_pos rfl]; exact congr_arg _ (form_pair U ((source M ![p,-(q+p),q]).curryLeft (V *ᵥ v)) x y).symm
  · rename_i he; rw [h' (mon_matches k), if_neg he]

lemma two_routed {p q z : Momentum} {i j l : Site n} (hq : Matches q j) (hp : Matches p i) (hz : Matches z l) (v w : CSpace b) : Routed B B (j+i+l) j
    ((actualMatrix (bank N P g)).quad (plane B i *ᵥ v) (plane B l *ᵥ w)) ((splitVertex U V (fun _ => source M)).two q p z v w) := by
  refine test_routed fun k x y => ?_; rw [bank_two hg h.total_diff hf,(hN k).vector,(hN j).vector,(hP i).vector,(hP l).vector]
  have h' {s} (hs : Matches s k) : iteratedFDeriv ℂ 4 (total M A) 0 ![plane A i *ᵥ V *ᵥ v, plane A l *ᵥ V *ᵥ w, plane A k *ᵥ U *ᵥ x, plane A j *ᵥ U *ᵥ y] = if k=-(j+i+l) then (n.val:ℂ)^4 • source M ![p,z,s,q] ![V *ᵥ v,V *ᵥ w,U *ᵥ x, U *ᵥ y] else 0 := by
    have H := h.total_plane (A:=A) (r:= ![i,l,k,j]) (p:= ![p,z,s,q]) (by intro t; fin_cases t <;> first | exact hz | exact hp | exact hs | exact hq) ![V *ᵥ v,V *ᵥ w,U *ᵥ x,U *ᵥ y]
    erw [Fin.sum_univ_four,ite_cond_congr (propext (show i+l+k+j=0 ↔ k=-(j+i+l) by rw [eq_neg_iff_add_eq_zero, show i+l+k+j=k+(j+i+l) by abel]))] at H
    convert H using 2; ext1 t; fin_cases t <;> rfl
  split
  · rename_i he; subst k; rw [h' ((hq.add hp).add hz).neg,if_pos rfl]; exact congr_arg _ (form_pair U (((source M ![p,z,-(q+p+z),q]).curryLeft (V *ᵥ v)).curryLeft (V *ᵥ w)) x y).symm
  · rename_i he; rw [h' (mon_matches k), if_neg he]

lemma Damped.synced : Synced B B B (actualMatrix (bank N P g)) (splitVertex U V (fun _ => source M)) :=
  ⟨base_routed h hg hf hN, one_routed h hg hf hN hP,two_routed h hg hf hN hP⟩
end YM.Push.Loops.Paths
