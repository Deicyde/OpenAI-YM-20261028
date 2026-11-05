import Mathlib.Analysis.Real.Pi.Bounds
import YM.RG08.Fields.Regale

/-! # Real punctured costs to cover estimates. Use unchanged absolute strip
which is budgeted before the length. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open scoped Topology BigOperators
variable {ι ζ : Type} {V : Row ι ζ} {σ C D X : ℝ}
lemma off_grid [DecidableEq ι] [DecidableEq ζ] [Fintype ζ] [Fintype ι] (h : V.safe) (L : Side) (a b : Site L) (i : ι) (j : ζ) :
    (L.val:ℂ)^4*(V.acts L (a,i) (b,j):ℂ)= ∑ p : Site L, cell p a * V.read (mon p) i j * star (cell p b) := by
  have he := circulant L V h
  let S:=rotations L ι; let U:=rotations L ζ; let Q:=approached (V.acts L); let B:=fiber (fun p : Site L=> V.read (mon p)); let u:=(L.val:ℂ)^4
  have hh : u • Q = S*B*Uᴴ := by rw [← show Q*U = S*B from he, Matrix.mul_assoc, show U*Uᴴ=(L.val:ℂ)^4 • 1 from rotations_gram ..,Matrix.mul_smul,Matrix.mul_one]
  change (u • Q) _ _=_
  rw [hh,mul_apply,Fintype.sum_prod_type]; unfold S B; simp_rw [rot_fiber]
  unfold U rotations; simp [apply_ite (starRingEnd ℂ),mul_ite]
lemma hailbound [Fintype ζ] [Fintype ι] (hv : V.safe) (h : ∀ p∈baseCube, ∀ i j, ‖V.read p i j‖ ≤ D) (i j x) : ‖V i j x‖ ≤ D := by
  classical
  have H (c : Side) (a b : Site c) : ‖V.acts c (a,i) (b,j)‖ ≤ D := by
    apply le_of_mul_le_mul_left _ (pow_pos (side_pos c) 4)
    rw [← Complex.norm_real,← Complex.norm_natCast (c.val:ℕ),← norm_pow,← norm_mul,off_grid hv c a b i j]
    refine (norm_sum_le ..).trans ?_
    have hh (p x : Site c): ‖cell p x‖=1 := mode_real _ _ (real_frequency _)
    simp_rw [norm_mul,norm_star,hh,one_mul,mul_one, norm_pow,Complex.norm_natCast]
    exact (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _ => D) fun p _=> h _ (mon_mem c _) _ _).trans_eq (by simp)
  let n (i : ℕ) : Side:= ⟨i+1,by omega⟩
  have ht : Tendsto (fun i=> (n i).val) atTop atTop := tendsto_atTop_mono (fun i => show i ≤ i + 1 by omega) tendsto_id
  exact le_of_tendsto ((entry_limit _ ht V hv i j x).norm) (.of_forall fun i=> H _ _ _)

private lemma real_step (t : ℝ) (ht : 0≤t) (hb : t≤1) : ∃ p∈baseCube, ‖p‖=t := by
    let v (a : Axis): ℂ:=t
    have hv : physical v:=by apply (physical_iff _).mpr; intro j; simp [v]
    refine ⟨v,⟨hv,fun j=> ?_⟩,?_⟩
    · simp only [v,Complex.ofReal_re]; exact (abs_of_nonneg ht).trans_le (hb.trans (by linarith [Real.pi_gt_three]))
    refine le_antisymm ((pi_norm_le_iff_of_nonneg ht).2 fun i=> by simp [v,abs_of_nonneg ht]) ?_
    have hh:= norm_le_pi_norm v 0; exact (show ‖v 0‖=t from by simp [v,abs_of_nonneg ht]).symm.trans_le hh
private lemma zero_wing (hz : 0<σ) (hC : V.strip σ C) (h : ∀ p∈baseCube,p≠0 → ∀ i j, V.read p i j=0) (i j p) (hp : p∈baseCube) : V.read p i j=0 := by
  let f t:= V.read t i j
  refine renew_q f (fun _=>0) 0 (fun p hp=> continuousAt_pi.mp (continuousAt_pi.mp (read_here _ (Whole.flipV hz hC) hp) i) j)
    (fun _ _=> continuousAt_const) (fun p hp hx=> h p hp (fun he => hx (by rw [he]; simp [Exterior.q])) _ _) p hp
  where Whole.flipV (h : 0<σ) (H : V.strip σ C) : Whole V := ⟨_,_,h,H⟩
lemma ship_warp (σ A D : ℝ) (hσ : 0<σ) (ha : 0≤A) (hb : 0≤D) :
    ∃ c:ℝ, 0<c ∧ ∀ (ι ζ : Type) [Fintype ζ] [Fintype ι] (V : Row ι ζ) (X : ℝ), 0≤X → V.strip σ A →
      (∀ p∈baseCube,p≠0 → ∀ i j, ‖V.read p i j‖ ≤ D*X^26*rim p^12) → V.strip (σ/4) (c*X) := by
  let θ:=σ/2; let η:=σ/4; have hθ : 0<θ∧θ<σ:=by unfold θ; constructor <;> linarith
  have hη : 0<η:=by unfold η; linarith
  let d := (σ-θ)⁻¹*A
  have hd : 0≤d:= mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hθ.2.le)) ha
  let L := max A (2*d+D)
  have hL : 0≤ L:= ha.trans (le_max_left ..)
  let c:= Real.sqrt (L*A); let m:=(2*((1+η)/η))^(Fintype.card Axis)
  have hc : 0≤c:= Real.sqrt_nonneg _; have hm : 0≤m:= by unfold m; positivity
  refine ⟨c*m+1,by positivity,fun ι ζ _ _ V X hX hA H =>?_⟩
  suffices h : ∀ p∈baseCube, ∀ i j, ‖V.read p i j‖ ≤ L*X^2 by
    have hh:= hailbound (V.rights σ A hA hσ.le) h
    have hv := Width.compactPay (α:=Axis) η hη
    intro i j
    have ht := Push.AbsoluteSums.budget_scale (mul_nonneg hc hX) hv
    apply (Push.AbsoluteSums.budget_loosen (budget_minor ht (fun x:Cover=> show 0≤Real.exp (η*size x)*‖V i j x‖ by positivity) ?_) ?_)
    · intro x
      let s : ℝ := η*size x
      have hu:= Push.AbsoluteSums.budget_single (hA i j) x
      change Real.exp (σ*(size x:ℝ)) * ‖V i j x‖ ≤ _ at hu
      have he := (mul_le_mul hu (hh i j x) (norm_nonneg _) ha)
      have hj : ‖V i j x‖^2*Real.exp (4*s) ≤ A*(L*X^2) := by
        rw [show 4*s=σ*size x from (by unfold s η; ring)]
        exact le_trans (le_of_eq (by ring)) he
      change Real.exp s * _ ≤ c*X*Real.exp (-η*size x)
      rw [show -η*size x= -s from by unfold s; ring]
      apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 2≠0)).1
      simp only [mul_pow,show c^2=L*A from Real.sq_sqrt (mul_nonneg hL ha)]
      apply le_of_mul_le_mul_left _ (pow_pos (Real.exp_pos s) 2)
      calc
        _ = ‖V i j x‖^2*Real.exp (4*s) := by rw [show 4*s=(s+s)+(s+s) from by ring,Real.exp_add,Real.exp_add]; ring
        _ ≤ _ := hj.trans_eq (by rw [Real.exp_neg]; field_simp)
    have ha : c*m ≤ c*m+1:= by linarith
    exact (le_of_eq (by ring : c*X*m=c*m*X)).trans (mul_le_mul_of_nonneg_right ha hX)
  by_cases hx : X=0
  · intro p hp i j
    have hh p (hp:p∈baseCube) (hz:p≠0) i j : V.read p i j=0 := norm_le_zero_iff.mp (by simpa [hx] using H p hp hz i j)
    rw [zero_wing hσ hA hh i j p hp]; simp [hx]
  intro p hp i j; have hxc : 0<X := lt_of_le_of_ne hX (Ne.symm hx); let f p:= V.read p i j
  by_cases hcX : X ≤ 1
  · have he : X^2 ≤ 1 := pow_le_one₀ hX hcX
    have hh := pow_pos hxc 2
    have hq (p : Momentum) (hp : p∈baseCube) (hv : X^2 ≤ ‖p‖) : ‖f p‖ ≤ D*X^2 := by
      have hz := hh.trans_le hv
      have ht : rim p ≤ (X^2)⁻¹ := max_le (one_le_inv₀ hh|>.mpr he) ((inv_le_inv₀ hz hh).2 hv)
      apply (H _ hp (norm_pos_iff.mp hz) i j).trans
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (rim_live _).le ht 12) (by positivity : 0≤D*X^26)).trans_eq (by field_simp)
    by_cases hr : X^2 ≤ ‖p‖
    · exact (hq _ hp hr).trans (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left (mul_nonneg (by norm_num) hd)).trans (le_max_right ..)) (by positivity))
    obtain ⟨q,hv,hw⟩:=real_step (X^2) hh.le he
    have hu : ‖f p - f q‖ ≤ d * ‖p-q‖ := Work.F07.readDiff (Row.constant_strip V hA i j) hθ.1 hθ.2
      (Work.F07.realStrip θ hθ.1 hp.1) (Work.F07.realStrip θ hθ.1 hv.1)
    calc
      _ ≤ ‖f p-f q‖+‖f q‖ := norm_le_norm_sub_add ..
      _ ≤ d* (X^2+X^2)+D*X^2 := add_le_add (hu.trans (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (not_le.mp hr).le hw.le)) hd)) (hq _ hv hw.ge)
      _ ≤ _ := le_trans (le_of_eq (by ring : _=(2*d+D)*X^2)) (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg hX _))
  exact (frost_read hp.1 hσ hA i j).trans ((le_max_left ..).trans (le_mul_of_one_le_right hL (one_le_pow₀ (not_le.mp hcX).le)))

end YM.RG08.Drift
