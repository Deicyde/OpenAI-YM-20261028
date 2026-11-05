import YM.RG08.Packets.Present
import YM.Next.FREE_KERNELS.Primal

/-!
# Constant-column test on the cover, for the independently supplied linear history
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG Precision Next.Free Exterior
open scoped Topology ENNReal

set_option autoImplicit false
variable {α β γ : Type} {L L' : Side} {S : Kernel α β} {T : Kernel β γ} {σ τ p q : ℝ}

theorem travels_bind [Fintype β] (h : RowCost σ L S p) (H : RowCost τ L' T q) (hs : 0 ≤ σ) (ht : 0 ≤ τ) (hk : travels S) (hg : travels T) : travels (bind S T) := by
  classical
  choose f hf using hk
  choose g Hg using hg
  intro i j
  refine ⟨∑ k,f i k * g k j,?_⟩
  intro x
  let E (k:β)(w: Cover × Cover):= S (x,i) (w.1,k)* T (w.1,k) (w.2,j)
  have hSum (k:β) : Summable (E k) := by
    apply Summable.of_norm
    simp only [Real.norm_eq_abs]; exact produce_any h H hs ht (x,i) k j
  simp_rw [bind_apply]
  rw [Summable.tsum_finsetSum (show ∀ k ∈ (Finset.univ:Finset β), Summable (fun y=>tagged S T k (x,i) (y,j)) from fun k _=> (hSum k).prod_symm.prod)]
  refine Finset.sum_congr rfl fun k _=> ?_
  unfold tagged; rw [(hSum k).tsum_comm]
  simp_rw [tsum_mul_left, Hg k j,tsum_mul_right,hf]

theorem travels_plain (H : Row α β): travels (plain H) := by
  intro i j; refine ⟨∑'v,H i j v,fun x=>?_⟩
  unfold plain
  exact (show (∑' y:Cover,H i j (y-x))= _ from by simp_rw [sub_eq_add_neg]; exact (Equiv.addRight (-x)).tsum_eq _)

theorem alias_origin {i j : ℕ} (P : Flight i j) (k : ℝ) (hk : 0 < k) (hj : 4 ≤ j) (z : Site P.L) (a b : Faces) :
    (P.duo k).T.read 0 (z,a) b = (toll P.L 2) * ((1 : Matrix Faces Faces ℂ) a b) := by
  have H:= P.legal
  have hp:= (secure_both (j:=i) (t:=j) k hk H hj).2
  have he : (0:Momentum) ∈ baseCube := by
    constructor
    · change star (0:Momentum) = 0; simp
    simp [Real.pi_pos.le]
  unfold Flight.duo
  rw [hp.bankRead H 2 (Nat.zero_le _) P z he a b, spread, Finset.sum_eq_single (0:Site P.L)]
  · have hx : aliasAt (0:Momentum) (0:Site P.L)=0 := Flight.toe_zero P
    rw [Flight.wire_origin,hx,listChip]; simp
  · intro u _ hu; rw [Flight.wire_none P k hu, smul_zero,smul_zero]
  simp

theorem travels_duo {i j : ℕ} (P : Flight i j) (k : ℝ) (hk : 0 < k) (hj : 4 ≤ j) :
    travels (install (P.duo k).T) := by
  intro a b
  refine ⟨((∑' v:Cover,(P.duo k).T ((0:Site P.L),a) b v):ℝ),fun x=>?_⟩
  unfold install
  rw [show (∑' y:Cover,(P.duo k).T ((wrap P.L x),a) b (y - rent P.L x)) = ∑' y:Cover,(P.duo k).T ((wrap P.L x),a) b y by
    simp_rw [sub_eq_add_neg]; exact (Equiv.addRight (-(rent P.L x))).tsum_eq _]
  apply Complex.ofReal_injective
  -- extend roadSum_price to cross
  have hh (u : Site P.L) : Complex.ofReal (∑' v,(P.duo k).T (u,a) b v)= (P.duo k).T.read 0 (u,a) b := by rw [Row.read,Matrix.of_apply,Laurent.read]; simp [← Complex.ofReal_tsum]
  simp_rw [hh,alias_origin P k hk hj]

theorem travels_route {i j : ℕ} (F : Flight i j) (k : KernelChoices) (hj : 4 ≤ j)
    {V : Towers F.L} {H H' : Bed} (hg : V.T=(F.duo k.penalty).T)
    (ht : V.T.strip σ p) (hu : H.inverse.strip σ p) (hx : H'.metric.strip τ q) (hs : 0 ≤ σ) (hτ : 0 ≤ τ) (hp : 0 ≤ p):
    travels (response V H H') := by
  have hT := cross_row (L:=F.L) ht hs le_rfl
  have hR:= row_left (L:=F.L) hu le_rfl hT hs hp (by positivity)
  have Hv : travels (install V.T) := hg.symm ▸ travels_duo F k.penalty k.penalty_pos hj
  unfold response sandwich
  exact travels_bind hR (plain0 hx le_rfl).1 hs hτ (travels_bind (plain0 hu le_rfl).1 hT hs hs (travels_plain _) Hv) (travels_plain _)
end YM.RG08.Flat
