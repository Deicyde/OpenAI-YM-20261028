import YM.Next.FREE_KERNELS.Warm


/-!
# Counting metric for log-det window bills

Use real physical color components, dimension displayed (even zero).
Keep receipts uniform in torus on the actual discrete rows where
published. Logs here real. No transport of mass or analytic branch
from these free matrices into selected interacting sectors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.Panel
open RG Precision Matrix Function Unitary
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ComplexOrder

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {A : Matrix ι ι ℝ} (H : A.IsHermitian)

def amount (η L : ℝ) := |Real.log η|+|Real.log L|
lemma amount_nonneg (η L : ℝ) : 0 ≤ amount η L := add_nonneg (abs_nonneg _) (abs_nonneg _)

include H
lemma bill_quad {η L : ℝ} (h : Numeric A η L) (i : ι) : η ≤ H.eigenvalues i ∧ H.eigenvalues i ≤ L := by
  let Y : ι → ℝ := ⇑(H.eigenvectorBasis i)
  have he := H.eigenvalues_eq i
  have hs : (star Y)=Y := by ext; simp
  change _ = RCLike.re (dotProduct (star Y) _) at he
  rw [hs] at he
  have ht : dotProduct Y Y = 1 := by
    nth_rw 2 [←hs]
    rw [← EuclideanSpace.inner_eq_star_dotProduct (x:= (H.eigenvectorBasis i)) (y:= (H.eigenvectorBasis i)),real_inner_self_eq_norm_sq,(H.eigenvectorBasis.orthonormal.1 i),one_pow]
  have hh := h Y; rw [ht, mul_one, mul_one,← show H.eigenvalues i = dotProduct Y _ from he] at hh
  exact hh

lemma determinant {η L : ℝ} (h : Numeric A η L) (he : 0 < η) :
    0 < A.det ∧ (η^(Fintype.card ι) ≤ A.det ∧ A.det ≤ L^(Fintype.card ι)) ∧
      |Real.log A.det| ≤ Fintype.card ι * amount η L := by
  have hv := bill_quad H h
  have hp i := he.trans_le (hv i).1
  rw [H.det_eq_prod_eigenvalues]
  change 0 < ∏ i, H.eigenvalues i ∧ (η^(Fintype.card ι) ≤ ∏ i,H.eigenvalues i ∧ (∏ i,H.eigenvalues i) ≤ L^(Fintype.card ι)) ∧ |Real.log (∏ i,H.eigenvalues i)| ≤ _
  refine ⟨Finset.prod_pos (fun i _=>hp i),⟨?_,?_⟩,?_⟩
  · convert Finset.prod_le_prod (s:=Finset.univ) (fun _ _=>he.le) (fun i _=>(hv i).1) using 1 <;> first | rfl | simp
  · convert Finset.prod_le_prod (s:=Finset.univ) (fun i _=>(hp i).le) (fun i _=>(hv i).2) using 1 <;> first | rfl | simp
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun _=>amount η L) (fun i _=>?_)).trans (by simp))
  refine abs_le.mpr ⟨?_,?_⟩ <;> unfold amount
  · linarith [Real.log_le_log he (hv i).1, neg_le_abs (Real.log η), abs_nonneg (Real.log L)]
  linarith [Real.log_le_log (hp i) (hv i).2, le_abs_self (Real.log L), abs_nonneg (Real.log η)]

omit H in
/-- e.g. apply on the accepted `plan.all` all-period, fixed numbers
of columns/built horizons. Quantitative log cost on true free dense
finite metric WITHOUT determinant-sign hypothesis. Does *NOT* say the
selected Gram on Tree.AFree is this horizon metric. -/
theorem horizon_cost {G : Gauge} (H : Levels G) (M : Horizon H) (P : MapPrices) (h : M.Suffices P)
    (N i : ℕ) (hi : i≤N) (n : Lattice.Side) :
    let j := H.clock.J i
    let C := (M.H N i).metric.acts n
    C.PosDef ∧ 0<C.det ∧ P.η j ^ Fintype.card (Exterior.Body 2 n) ≤ C.det ∧
      |Real.log C.det| ≤ Fintype.card (Exterior.Body 2 n)*amount (P.η j) (P.Ω j) := by
  intro j C
  have Hv := h.all N i hi n
  have he : C.IsHermitian := by simpa [Matrix.IsHermitian] using Hv.symmetric.1
  have hh := Hv.uniform.1
  have ht := determinant he hh (P.eta_pos j)
  exact ⟨he.posDef_iff_eigenvalues_pos.mpr (fun i => (P.eta_pos j).trans_le (bill_quad he hh i).1),ht.1,ht.2.1.1,ht.2.2⟩


omit H [DecidableEq ι] [Fintype ι] in
/-- The same pre-L Free.Warm cut when applicable: principal real
log isn't used on arbitrary complex p. Only physical `p`, and real
amount for its Hermitian determinant. Numerical convention explicitly on
retained weighted rows. -/
theorem warm_logs {J : Type*} {m : Type} [Fintype m] [DecidableEq m]
    {f : J → Bloch.Row m m} (h : Next.Free.Warm f) :
    ∃ η L : ℝ, 0<η ∧ 0<L ∧ ∀ (i : J) (p : Bloch.Momentum), Next.Free.physical p →
      let A := (f i).read p
      (0 < A.det.re ∧ A.det.im = 0) ∧
        η^(Fintype.card m) ≤ ‖A.det‖ ∧ ‖A.det‖≤L^(Fintype.card m) ∧
          |Real.log ‖A.det‖| ≤ Fintype.card m* amount η L := by
  obtain ⟨η,L,he,hl,hh⟩ := h.funds
  refine ⟨η,L,he,hl,fun i p hp => ?_⟩
  intro B
  obtain ⟨hb,hg⟩ := hh i p hp
  change B.IsHermitian at hb
  obtain ⟨y,s,hs⟩ := (show ∃ (y : Holder.U m) (s : m → ℝ), B=y.val*Holder.D s*y.valᴴ from ⟨_,_,Holder.spectral_diag hb⟩)
  have hB : Work.F07.Band B η L := hg
  rw [hs] at hB
  have hx := (Work.F07.unitaryBand y s _ _).mp hB
  have hm (i) := he.trans_le (hx i).1
  have hd : B.det = ∏ i,s i := by
    have hy : (y.valᴴ).det*y.val.det=1 := by rw [← Matrix.det_mul,Holder.united,Matrix.det_one]
    rw [hs, Matrix.det_mul,Matrix.det_mul]; rw [show y.val.det*_*(y.valᴴ).det = (Holder.D s).det*((y.valᴴ).det*y.val.det) by ring, hy,mul_one, Holder.D, det_diagonal]; simp
  have HW := (Next.Free.band_bill hb (show Work.F07.Band B η L by rwa [hs]) he hl).1
  refine ⟨?_,HW,?_,?_⟩ <;> rw [hd]
  · simpa only [Complex.ofReal_re,Complex.ofReal_im,and_true] using (Finset.prod_pos (s:=Finset.univ) fun j _=>hm j)
  all_goals rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Finset.prod_pos (s:=Finset.univ) fun j _=>hm j)]
  · convert Finset.prod_le_prod (s:=Finset.univ) (fun j _=>(hm j).le) (fun j _=>(hx j).2) using 1 <;> first | rfl | simp
  rw [Real.log_prod (fun i _ => (hm i).ne')]
  refine (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (g:=fun _=>amount η L) (fun i _=>?_)).trans (by simp))
  refine abs_le.mpr ⟨?_,?_⟩ <;> unfold amount
  · linarith [Real.log_le_log he (hx i).1, neg_le_abs (Real.log η), abs_nonneg (Real.log L)]
  linarith [Real.log_le_log (hm i) (hx i).2, le_abs_self (Real.log L), abs_nonneg (Real.log η)]

end YM.SectorNext.Vacuum.Panel
