import YM.Push.FREE_RESOLVENT.Layout

/-!
# Track prices in the exponential metric

Work at the origin with B field in actual log chart. Taylor indices held
in physical locations. Thresholds uniform across all periods and forests,
no second period copy sneaking into the estimates through a Pi-vector
bound. L-dependence explicitly post-L. Input exponential only on TRUE
lengths; the strip in the output of the jet estimates costs a fixed portion
of it including all mark relocations. Output explicitly absolute Schur,
pointwise and before any tensor summation. Use smaller rate for additional
moments/infinite-lattice degree caps. Cut tests are *structural cuts* and
do not include derivative of any choice conditions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set Mark
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c n : Side} {S : StepData c f} {r k : ℕ} {σ V A γ M β d : ℝ}

abbrev marks (G : Gauge) (c : Side) (δ : ℝ) := positions (native c) (hearth (G:=G) (r:=1)) δ

def shorter (R : ℕ) : Admit := fun x => decide (x.length ≤ R)
def longer (R : ℕ) : Admit := fun x => !(shorter R x)
def all : Admit := fun _ => true

def facetReserve (W : PathData G) (i : tile G f) (q : ℕ) := W.row (plaqEquiv.symm i.2.1) q

lemma track_entry (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q k : ℕ) (hs : 0 < σ) (l : List (raw G c)) (hl : l.length ≤ k) (hd : 0 ≤ d) (hg : 0 ≤ γ)
    (hv : γ+2*k*d ≤ σ/2) (R : ℕ) (hR : ∀ z, r z=true → R ≤ z.length) :
    let P := facetReserve W i q
    let C := Real.exp (-(σ/4)*R) * ((|P.1| * Real.exp (σ*P.2.length))*elbow G k (σ/4))
    let a := |jet (ray G c) (edgework S s W r i j q) l 0|
    let b := (native c).weight γ (named S s i) (named S s j)*a
    (marks G c d).pay l (named S s i)*b ≤ C ∧ (marks G c d).pay l (named S s j)*b ≤ C := by
  intro P C a b
  by_cases he : jet (ray G c) (edgework S s W r i j q) l 0=0
  · have hh : b=0 := by unfold b a; rw [he,abs_zero,mul_zero]
    have hc : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) (elbow_nn ..))
    simp only [hh,mul_zero,hc,and_self]
  have hc : edgework S s W r i j q≠0 := fun h => he (by rw [h,zero_null])
  have ht : r P.2=true := by
    by_contra hh; apply hc
    funext B
    exact if_neg hh
  let x := named S s i; let y := named S s j; let L : ℝ := P.2.length
  obtain ⟨h1,h2⟩ := forward S s W r i j q he
  have hL : (native c).d x y ≤ L := by
    change ((separation _ _):ℝ) ≤ ((P.2.length:ℕ):ℝ); exact_mod_cast h1
  have hm (t : raw G c) (h : t∈l) : (native c).d x (hearth t) ≤ L := by
    change ((separation _ _):ℝ) ≤ ((P.2.length:ℕ):ℝ); exact_mod_cast h2 t h
  have hn : 0 ≤ L := by unfold L; positivity
  have hK (z : Site c) (hz : (native c).d z x ≤ L) : (marks G c d).pay l z*b ≤ C := by
    have hh t (h : t∈l) : (native c).d z (hearth t) ≤ 2*L := le_trans ((native c).triangle z x _) ((add_le_add hz (hm t h)).trans_eq (two_mul L).symm)
    have h5 := sheetEdge_ceiling S s W r i j q k (by linarith : 0 < σ/4)
    have ha : a ≤ |P.1| * Real.exp (σ/4*L)*elbow G k (σ/4) := calc
      a = ‖jet (ray G c) (sheetEdge S s W r i j q) l 0‖ := by
        unfold a
        rw [identical _ (show sheetEdge S s W r i j q=ᶠ[𝓝 0] edgework S s W r i j q from
          (same_edge S s W r).mono fun _ h => h i j q)]; rfl
      _ ≤ _ := h5.bill (slot_nn _) (ray G c) ray_nn l hl 0
    refine (mul_le_mul (plumb (native c) z hearth l hd _ hh)
      (mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left hL hg)) ha (abs_nonneg _) (Real.exp_pos _).le)
      (show 0 ≤ b from mul_nonneg ((native c).weight_nn ..) (abs_nonneg _)) (Real.exp_pos _).le).trans ?_
    have hA : (l.length:ℝ)*d*(2*L)+γ*L+σ/4*L ≤ -(σ/4)*R+σ*L := by
      have hu : (R:ℝ) ≤ L := by unfold L; exact_mod_cast hR _ ht
      have hi : (l.length:ℝ) ≤ (k:ℝ) := by exact_mod_cast hl
      nlinarith only [mul_le_mul_of_nonneg_right hv hn, mul_le_mul_of_nonneg_left hu hs.le,
                        mul_le_mul_of_nonneg_right hi (mul_nonneg hd hn)]
    apply le_trans _ (le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone hA) (mul_nonneg (abs_nonneg P.1) (elbow_nn G k (σ/4)))) ?_)
    · simp only [Real.exp_add]; exact le_of_eq (by ring)
    unfold C L; rw [Real.exp_add]; exact le_of_eq (by ring)
  exact ⟨hK x (by rw [Cost.self]; exact hn), hK y (by rw [Cost.comm]; exact hL)⟩

theorem track_rows (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (k : ℕ)
    (hs : 0 < σ) (hW : Sheet W σ M) (hm : 0 ≤ M)
    (hd : 0 ≤ d) (he : 0 < γ) (hh : 2*γ+2*k*d ≤ σ/2)
    (R : ℕ) (hR : ∀ z, r z=true → R ≤ z.length) :
    Bundle (ray G c) (marks G c d) (native c) (named S s) (named S s) (tracks S s W r) 0 k γ
      (torusPay (Co S.patch.L (PAC G 2)) γ * (Real.exp (-(σ/4)*R)*(M*elbow G k (σ/4)))) := by
  have hz := elbow_nn G k (σ/4)
  refine ⟨tracks_smooth hs hW S s r k,fun l hl => ?_⟩
  let X := tracks S s W r
  let C := Real.exp (-(σ/4)*R)
  have hc : 0 < C := Real.exp_pos _
  let B := elbow G k (σ/4)
  let H := C*(M*B)
  have hN : 0 ≤ H := mul_nonneg hc.le (mul_nonneg hm hz)
  let a := named S s (G:=G) (r:=2)
  let D := native c
  let Y := jet (ray G c) X l 0
  have hp (i j : tile G f) : (marks G c d).pay l (a i)*(D.weight (2*γ) (a i) (a j) * |Y i j|) ≤ H ∧
      (marks G c d).pay l (a j)*(D.weight (2*γ) (a j) (a i) * |Y i j|) ≤ H := by
    let P (q : ℕ) := facetReserve W i q
    have he (q : ℕ) := track_entry S s W r i j q k hs l hl hd (mul_nonneg (by norm_num) he.le) hh R hR
    let w := fun q => C*((|(P q).1| * Real.exp (σ*(P q).2.length))*B)
    have h : RG.SumBudget (fun q => |(P q).1| * Real.exp (σ*(P q).2.length)) M := hW _
    have hw : Summable w := (h.2.1.mul_right B).mul_left C
    have hw' : (∑' q, w q) ≤ H := by
      unfold w; rw [tsum_mul_left,tsum_mul_right]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h.2.2 hz) hc.le
    let F q := jet (ray G c) (edgework S s W r i j q) l 0
    have hb : HasSum F (Y i j) := track_polar hs hW S s r i j l _
    let L := D.weight (2*γ) (a i) (a j)
    have hh (d : ℝ) (hd : 0 < d) (hy : ∀ q, d*(L*|F q|) ≤ w q) : d*(L*|Y i j|) ≤ H := by
      have hL : 0 < L := D.weight_pos ..
      let g q := ‖(d*L)*(F q)‖
      have ht (q) : g q=d*(L*|F q|) := by unfold g; simp [Real.norm_eq_abs,abs_of_pos hL,abs_of_pos hd,mul_assoc]
      have hs : Summable g := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => (ht i).trans_le (hy _)) hw
      have he := le_trans (norm_tsum_le_tsum_norm hs) ((hs.tsum_le_tsum (fun i => (ht i).trans_le (hy _)) hw).trans hw')
      rw [(hb.mul_left (d*L)).tsum_eq] at he
      simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos hd,abs_of_pos hL,mul_assoc] using he
    constructor
    · exact hh _ (pay_pos ..) fun q => (he q).1
    rw [Cost.weight_symm]; exact hh _ (pay_pos ..) fun q => (he q).2
  have ht := named_volume S s 2 _ he (G:=G)
  nth_rw 1 [show γ=2*γ-γ by ring] at ht
  exact Bill.of_entry ht ht hN (fun i j => (hp i j).1) fun i j => (hp i j).2

lemma remaining_work (S : StepData c f) (s : Signed) (W : PathData G) (R : ℕ) (hs : 0 < σ) (h : Sheet W σ M) :
    tracks S s W all =ᶠ[𝓝 0] fun x => tracks S s W (shorter R) x + tracks S s W (longer R) x := by
  -- first for regularized entries
  filter_upwards [returns (G:=G) S s, same_edge S s W all, same_edge S s W (shorter R), same_edge S s W (longer R)] with B hB h1 h2 h3
  ext i j
  simp_rw [Matrix.add_apply, tracks, of_apply, ← h1, ← h2, ← h3]
  have hw (r : Admit) : Summable (fun q => sheetEdge S s W r i j q B) := by
    have ht := fun q => (sheetEdge_ceiling S s W r i j q 0 hs).op 0 B le_rfl
    simp_rw [norm_iteratedFDeriv_zero] at ht
    exact Summable.of_norm_bounded ((h (plaqEquiv.symm i.2.1)).2.1.mul_right (elbow G 0 σ)) ht
  rw [← (hw _).tsum_add (hw _)]
  refine tsum_congr fun q => ?_
  simp only [sheetEdge, all, longer]
  by_cases H : shorter R (W.row (plaqEquiv.symm i.2.1) q).2 = true <;> simp [H]
end YM.FreeResolvent.Affine
