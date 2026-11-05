import YM.Planned.STATIONARY_JET_PORT.Identities

set_option warningAsError false

/-! All orders of the real slice inverse; localized log determinant tensors -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push.Uniform Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical
variable {ι τ : Type} [Fintype ι] {n : Side} {l : ι → Site n} {m : τ → Site n}
    {N K k : ℕ} {a C D : ℝ} {M : Positions ι → Matrix τ τ ℝ} {x : Positions ι}

lemma Cable.takeFinger (hM : bornMatrix M x) (h : Cable l m m none a N M x C) (hk : k<N) (d : ι) :
    Cable l m m (some (l d)) a k (finger M d) x C := by
  intro i j v hv q
  change ‖entry (fun y => fderiv ℝ (fun z => M z i j) y (bolt d)) x q‖ ≤ C*_*_*glaze l (m i) q a
  rw [peel_snoc (hM i j)]
  apply (h.paid i j _ (show v+1 ≤ N by omega)).trans_eq
  rw [glaze_snoc,thread_none,thread_leg]; ring

-- First argument of weakLine is an already common (min) unshifted rate.
def weakLine (a : ℝ) : ℕ → ℝ
  | 0 => a
  | k+1 => slip k (slip k (weakLine a k))
lemma weakLine_pos (ha : 0<a) (k : ℕ) : 0<weakLine a k := by
  induction k with
  | zero => exact ha
  | succ k ih => exact slip_pos _ (slip_pos _ ih)
lemma weakLine_anti (ha : 0<a) (k : ℕ) : weakLine a (k+1) ≤ weakLine a k :=
  (slip_le _ (slip_pos _ (weakLine_pos ha k)).le).trans (slip_le k (weakLine_pos ha k).le)
lemma weakLine_cap (ha : 0<a) (k : ℕ) : weakLine a k ≤ a := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (weakLine_anti ha k).trans ih

def lineCost (a C D : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => D -- assumes charge D of undifferentiated inverse
  | k+1 =>
    let w := weakLine a k; let b := lineCost a C D K k
    b + b*C*conductor k K w * b * conductor k K (slip k w)
lemma lineCost_pos (ha : 0<a) (hc : 0<C) (hd : 0<D) (k : ℕ) (K : ℕ) : 0<lineCost a C D K k := by
  induction k with
  | zero => exact hd
  | succ k ih =>
    have H := weakLine_pos ha k; have hh := conductor_pos k K H; have hh' := conductor_pos k K (slip_pos k H)
    unfold lineCost; dsimp only; positivity

variable [Fintype τ] [DecidableEq τ]

/-- Sealing of a base inverse (ordinary or e.g. ANY shifted resolvent), and
cables on the derivative of the base matrix (may ignore the cost of the
zeroth H value!), suffice IN TRUE derivatives of the actual inverse. If
using `energy = 1+spectral parameter`, this retains one gain in all the
bounds and even a second in newest positive orders (not needed here). -/
theorem inverse_lines (hM : bornMatrix M x) (hdM : (M x).det ≠ 0)
    (hm : Multiplicity m K) (ha : 0<a) (hc : 0<C) (hd : 0<D) (energy : ℝ) (he : 1 ≤ energy)
    (h0 : Sealed m a (M x)⁻¹ (D/energy))
    (h : ∀ v < N, ∀ d, Cable l m m (some (l d)) a v (finger M d) x C) (k : ℕ) (hk : k≤N) :
    Cable l m m none (weakLine a k) k (fun y => (M y)⁻¹) x (lineCost a C D K k /energy) := by
  let F y := (M y)⁻¹
  induction k with
  | zero =>
    intro i j u hu q; obtain rfl : u=0 := by omega
    simpa only [entry,iteratedFDeriv_zero_apply,Real.norm_eq_abs, thread_none,mul_one,
      spanSites, Fin.sum_univ_zero,Nat.cast_zero,mul_zero,Real.exp_zero,lineCost,weakLine] using h0 i j
  | succ k ih =>
    let w := weakLine a k
    let B := lineCost a C D K k
    let W := slip k w
    have he' := zero_lt_one.trans_le he
    let E := B/energy
    have hw : 0<w := weakLine_pos ha k
    have hW : 0<W := slip_pos k hw
    have hB : 0<B := lineCost_pos ha hc hd k K
    have hE : 0<E := div_pos hB he'
    have ht := conductor_pos k K hw; have hv := conductor_pos k K hW
    have hg : Cable l m m none w k F x E := ih (by omega)
    have hf : bornMatrix F x := hM.inverse hdM
    intro i j u hu q
    rcases eq_or_lt_of_le hu with hu|hu
    · subst u
      let d := q (Fin.last k); let U := finger M d
      have hh := (h k (by omega) d).rate hc.le (weakLine_cap ha k)
      have first : Cable l m m (some (l d)) W k (fun y => F y * U y) x (E*C*conductor k K w) := by
        have t := Cable.multiply (v:=m) (u:=m) (m:=m) hf (hM.finger d) hg hh hw hE hc hm
        unfold splice at t; exact t
      have H := Cable.multiply (v:=m) (u:=m) (m:=m) (hf.multiply (hM.finger d)) hf first (hg.rate hE.le (slip_le k hw.le)) hW
        (mul_pos (mul_pos hE hc) ht) hE hm
      let Y := E*C*conductor k K w * E * conductor k K W
      let T := slip k W
      have hZ : Cable l m m (some (l d)) T k (finger F d) x Y := by
        have t := (H.neg ((hf.multiply (hM.finger d)).multiply hf)).germ (inverse_germ hM hdM d).symm
        unfold splice at t; exact t
      have hC : Y ≤ lineCost a C D K (k+1)/energy := by
        have H := div_le_self hB.le he
        change E*C*conductor k K w * E * conductor k K W ≤
          (B + B*C*conductor k K w * B * conductor k K W) / energy
        rw [add_div,show B*C*_*B*_ / energy=E*C*conductor k K w *B * conductor k K W by unfold E; ring]
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H (by positivity)) hv.le).trans
          (le_add_of_nonneg_left hE.le)
      rw [peel (hf i j)]
      have hz := (hZ.cost hC).paid i j (fun t : Fin k => q t.castSucc) le_rfl
      apply hz.trans_eq
      change (lineCost _ _ _ _ _ / _)*(_*thread (some (l d)) T _*_) = _*_ *thread none T _ * glaze _ _ _ T
      rw [show weakLine a (k+1) = T from rfl,thread_none,glaze_last,thread_leg]; unfold d; ring
    exact (((hg.rate hE.le (weakLine_anti ha k)).cost
      (div_le_div_of_nonneg_right (b:=lineCost a C D K (k+1)) (le_add_of_nonneg_right (by positivity)) he'.le)) i j u (by omega) q)

-- Pass to closed loops in varying backgrounds. Use `trace` with row label
-- multiplicity, no volume-scaled norm of H or rank-times-det estimates.
def loopBill (a C D : ℝ) (K N : ℕ) := D*C*conductor N K a * (1+(K:ℝ)*countCost (slip N a/2))
lemma loopBill_pos (ha : 0<a) (hc : 0<C) (hd : 0<D) (N K : ℕ) : 0<loopBill a C D K N := by
  have h := conductor_pos N K ha; have H := count_pos (half_pos (slip_pos N ha)); unfold loopBill; positivity

theorem logdet_scatter (hM : bornMatrix M x) (hdM : (M x).det ≠ 0) (hm : Multiplicity m K)
    (ha : 0<a) (hc : 0<C) (hd : 0<D)
    (h : ∀ d, Cable l m m (some (l d)) a N (finger M d) x C)
    (hR : Cable l m m none a N (fun y => (M y)⁻¹) x D) :
    Scatter l (weaker (N+1) (slip N a)) (N+1) (fun y => Real.log (M y).det) x (loopBill a C D K N) := by
  intro k hk q j
  cases k with
  | zero => exact Fin.elim0 j
  | succ k =>
    let w := slip N a; have hw : 0<w := slip_pos N ha
    let d := q (Fin.last k)
    let u (i : Fin k) := q i.castSucc
    let F (y) := (M y)⁻¹ * finger M d y
    let e j := entry (fun y => F y j j) x u
    let B := D*C*conductor N K a; have hB : 0<B := by have H := conductor_pos N K ha; unfold B; positivity
    have hf : bornMatrix F x := (hM.inverse hdM).multiply (hM.finger d)
    have hh : Cable l m m (some (l d)) w N F x B := by
      have t := Cable.multiply (v:=m) (u:=m) (m:=m) (hM.inverse hdM) (hM.finger d) hR (h d) ha hd hc hm
      unfold splice at t; exact t
    have he (j : τ) : ‖e j‖ ≤ B*glaze l (m j) q w := by
      rw [glaze_last]
      apply (hh.paid j j u (show k ≤ N by omega)).trans_eq
      simp only [Decay,thread_leg,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] -- thread_leg after Decay
      rfl
    rw [ev_peel (hM.determinant.log hdM) q (log_germ hM hdM d)]
    change ‖entry (fun y => ∑ i, F y i i) x u‖ ≤ _
    let L := l (q j); let V := glaze l L q (weaker (N+1) w); have hV : 0<V := Real.exp_pos _
    rw [entries_finset (fun i _ => hf i i)]
    apply le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _ => (he i).trans (mul_le_mul_of_nonneg_left (price_relative hk q j hw.le) hB.le))))
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    change B*((∑ i, Decay (w/2) L (m i))*V) ≤ (B*(1+(K:ℝ)*countCost (w/2)))*V
    rw [mul_assoc B (1+_) V]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((hm.count m (half_pos hw) L).trans (le_add_of_nonneg_left zero_le_one)) hV.le) hB.le
end YM.Planned.JetPort
