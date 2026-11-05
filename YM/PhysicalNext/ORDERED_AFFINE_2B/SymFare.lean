import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Epoch
import YM.AnalyticBridge.RESET_INCOME_PORT.Fiber
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Further.CURVED_GAUSSIAN_JETS.Bridge
import YM.Further.CURVED_GAUSSIAN_JETS.Colors
import YM.Further.CURVED_GAUSSIAN_JETS.Law
import YM.Further.CURVED_GAUSSIAN_JETS.Perturb
import YM.Further.CURVED_GAUSSIAN_JETS.Tracks
import YM.PhysicalNext.ORDERED_AFFINE_2B.Padding
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymRows
import YM.Push.COMMON_WITNESSES.Frequent
import YM.Push.RELAY_MARK.Linear
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix
/-!
# Group trace & open ends at their actual spatial walks

Keep ordered directions on individual letters. A *scalar* label is the
WHOLE color contraction, because trace telescoping only with all actual
orientations and colors. Especially at Z⁺/Z⁻ transport where signs and
vectors cannot be forgotten. Don't collapse these to an entry at one
point, price the complete walk. Engine in CGJ.Track is ordered with
repeats/winds. Here all generic steps count ALL walks (no `if_nonzero`
range selection), later can issue an equivariant a priori truncation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymFare
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Stores
open Next Next.SectorChange AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor  Matrix
open Further Further.CurvedGaussianJets Tracks Completion SymRows 
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "RPrice" => Next.SectorChange.Prices

variable {α β : Type} {d : ℕ} [DecidableEq α] [DecidableEq β]
section code
-- constructors include* filters* of colors/products. Keep these
-- filters explicit for re-joining with `reports` left formulas.
variable (p : Run α d)

def mix (x : Run β d) : Run (α × β) d := fun i => (p i,x i)
variable [Fintype β]
-- traced p incl conditional on the actual fine links matching
-- (not same projected window anchor).
def close (w : Run (α × β) d → ℝ) : ℝ := ∑ u : Run β d, if p (Fin.last d)=p 0 ∧ u (Fin.last d)=u 0 then w (mix p u) else 0
def facing (z y : α×β → ℝ) (w : Run (α×β) d → ℝ) := ∑ u : Run β d,
    z (p 0,u 0)*y (p (Fin.last d),u (Fin.last d))*w (mix p u)
def strip (M : Gaussian.Table (α × β)) (i j : α) : Gaussian.Table β := M.submatrix (Prod.mk i) (Prod.mk j)
def cruise (M : Fin d → Gaussian.Table (α×β)) : Gaussian.Table β := engine fun i : Fin d => strip (M i) (p i.castSucc) (p i.succ)

omit [DecidableEq α] in
lemma printed (M : Fin d → Gaussian.Table (α×β)) (i j : β) : cruise p M i j=∑ u : Run β d, ends i j u (fare (mix p u) M) := engine_entries ..
lemma returns (M : Fin d → Gaussian.Table (α×β)) : close p (fun j=> fare j M)=if p (Fin.last d)=p 0 then Matrix.trace (cruise p M) else 0 := by
  unfold close; split
  · next he => rw [Matrix.trace]; simp_rw [diag_apply, printed]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun u _=>?_;
               unfold ends; simp only [he,true_and]; rw [Finset.sum_eq_single (u 0) (fun i _ hi=> if_neg (fun hh=>hi hh.1.symm)) (by simp)]; simp
  next he => simp [he]
omit [DecidableEq α] in
lemma stared (M : Fin d → Gaussian.Table (α×β)) (z y : α×β→ℝ) : facing p z y (fun j=>fare j M)=
    (z ∘ Prod.mk (p 0)) ⬝ᵥ (cruise p M *ᵥ (y ∘ Prod.mk (p (Fin.last d)))) := by
  simp only [facing,mulVec,dotProduct,printed,Function.comp_apply,Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (j : β) (u : Run β d) => ∑ i : β, z (p 0,i)*(ends i j u (fare (mix p u) M)*y (p (Fin.last d),j)))]
  unfold ends; refine Finset.sum_congr rfl fun u _=> ?_
  simp only [ite_mul,mul_ite,mul_zero,zero_mul]
  rw [Finset.sum_eq_single (u (Fin.last d)) (fun i _ hi=> by simp [Ne.symm hi]) (by simp)]; simp; ring

omit [DecidableEq α] [DecidableEq β] in
lemma faces_charge (z y : α×β→ℝ) (a : ℝ) (w : Run (α × β) d→ℝ) : facing p z y (fun j=>a*w j)=a*facing p z y w := by unfold facing; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=>by ring)
end code

variable [Fintype α] [Fintype β] (O : ColorOrtho G α) (e : α ≃ β) (A : Gaussian.Table (β × G.ColorIndex))
omit [DecidableEq β] [Fintype β] in
lemma strips (i j : α) : strip (warp O e A) i j = asMatrix O i * strip A (e i) (e j) * (asMatrix O j)ᵀ := by
  ext a b; unfold warp; unfold strip; rw [submatrix_apply,dressed_apply,mul_apply]
  apply Finset.sum_congr rfl; intro t ht; rw [mul_apply]; rfl
omit [DecidableEq β] [Fintype β] in
lemma cruised (M : Fin d → Gaussian.Table (β×G.ColorIndex)) (p : Run α d) : cruise p (fun j=>warp O e (M j)) =
    asMatrix O (p 0) * cruise (e∘p) M * (asMatrix O (p (Fin.last d)))ᵀ := by
  induction d with
  | zero =>
    have ht := matrix_orth O (p 0); unfold cruise; rw [engine_zero,engine_zero, Matrix.mul_one]; exact (mul_eq_one_comm.mp ht).symm
  | succ d ih =>
    let u := Fin.tail p; let W := asMatrix O; let N := Fin.tail M
    unfold cruise; rw [engine_next,engine_next,strips]; change (W (p 0) * strip _ _ _ * (W (u 0))ᵀ)*cruise u (fun i=>warp O e (N i))= W (p 0)*(strip _ _ _ *cruise (e∘u) N)*(W _)ᵀ; rw [ih]
    have he:=matrix_orth O (u 0); change (W _)ᵀ * W _ = 1 at he
    simp_rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (W (u 0))ᵀ _ _,he,Matrix.one_mul]; rfl

omit [Fintype β] in
lemma closing (M : Fin d → Gaussian.Table (β×G.ColorIndex)) (p : Run α d) : close p (fun j=>fare j (fun j=>warp O e (M j)))=close (e∘p) (fun j=>fare j M) := by
  rw [returns,returns,cruised]; simp only [Function.comp_apply,e.injective.eq_iff]; split; swap
  · rfl
  next he => rw [he,Matrix.trace_mul_comm,← Matrix.mul_assoc,matrix_orth O,Matrix.one_mul]



omit [Fintype β] [DecidableEq β] in
lemma royalties (i : α) : ∑ j : G.ColorIndex, warp O e A (i,j) (i,j)=∑ j : G.ColorIndex, A (e i,j) (e i,j) := by
  change Matrix.trace (strip (warp O e A) i i)=Matrix.trace (strip A (e i) (e i))
  rw [strips,Matrix.trace_mul_comm,←Matrix.mul_assoc,matrix_orth O,Matrix.one_mul]
end YM.PhysicalNext.OrderedAffine2B.SymFare
