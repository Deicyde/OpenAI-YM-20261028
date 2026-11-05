import YM.Push.RELAY_MARK.Cutoff
import YM.Work.D01

/-!
# Growth accounting on the actual cutoff coefficient arrays

At this interface `F.fuse` = mesh **then** period. `dollar`
isn't an assumption about the costs of just fixed reference vectors. Price
the parameters of our equation lifts from arbitrary array bounds; preserve
subexponential payment even when undoing threshold powers (and back).
This is arithmetic on the actual C, not constructing the funded history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {d : ℕ} {S : Schedule}

def Score (s : Schedule) (F : Extraction.Order) (f : ℕ × ℕ → ℝ) :=
    ∀ ε> (0:ℝ), ∀ᶠ i : ℕ × ℕ in F.fuse, f i ≤ Real.exp (ε*s.scale i.1)

namespace Score
variable {f g : ℕ×ℕ→ℝ}
lemma of_mesh {f : ℕ→ℝ} (h : ∀ ε>(0:ℝ), ∀ᶠ n in atTop, f n ≤ Real.exp (ε*S.scale n)) :
    Score S F (fun i => f i.1) := by
  intro ε he; rw [Order.fused]; exact Eventually.of_forall fun p=> F.mesh.cofinal.eventually (h ε he)

lemma const (S : Schedule) (F : Extraction.Order) (c : ℝ) : Score S F fun _=>c := of_mesh (f:=fun _=>c) (fun _ he=>
    (Real.tendsto_exp_atTop.comp (S.divergent.const_mul_atTop he)).eventually_ge_atTop c)

lemma easier (hg : Score S F g) (h : ∀ᶠ i in F.fuse,f i ≤ g i) : Score S F f := fun ε he=>
    h.mp ((hg ε he).mono (fun _ hh hl=>hl.trans hh)) -- check

lemma mul (hf : Score S F f) (hg : Score S F g) (h : ∀ᶠ x in F.fuse, 0 ≤ g x) : Score S F (fun i=> f i*g i) := by
  intro ε he; filter_upwards [hf (ε/2) (half_pos he),hg _ (half_pos he), h] with i h1 h2 h3
  exact (mul_le_mul h1 h2 h3 (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; ring_nf)

lemma power (hf : Score S F f) (h : ∀ᶠ x in F.fuse, 0 ≤ f x) (i : ℕ) : Score S F fun j=> f j^i := by
  induction i with
  | zero => simp only [pow_zero]; exact const S F 1
  | succ i ih => simp only [pow_succ]; exact ih.mul hf h

lemma add (hf : Score S F f) (hg : Score S F g) : Score S F (fun i=> f i+g i) := by
  intro ε he; filter_upwards [hf (ε/2) (half_pos he),hg _ (half_pos he), const S F 2 _ (half_pos he)] with i h1 h2 h3
  apply (add_le_add h1 h2).trans
  let a := (ε/2)*S.scale i.1
  change 2≤Real.exp a at h3
  rw [show ε*S.scale i.1= a+a by unfold a; ring, Real.exp_add]; change Real.exp a+Real.exp a ≤ _; nlinarith
end Score

lemma accounting (x : Rowe C d) : dollar C F x ↔ Score C.S F (fun j=> ‖(C.factory d j.1 j.2).terminal.symm (x j)‖) := by
  unfold dollar Score; refine forall_congr' (fun ε=>imp_congr_right fun _=>?_)
  exact (Extraction.Order.fused F (fun j => ‖(C.factory d j.1 j.2).terminal.symm (x j)‖ ≤ Real.exp (ε*C.S.scale j.1))).symm

lemma warm (C : Family G) (F : Extraction.Order) : Score C.S F fun i=> (C.path.levels.clock.threshold i.1)⁻¹ := by
  let Y := C.path.levels.clock
  refine Score.of_mesh (f:=fun N => (Y.threshold N)⁻¹) ?_
  intro ε he
  let b := Y.bar
  let k := G.slopeConstant
  have hs := C.S.divergent
  have hp : Tendsto (fun N => ε*(ε*C.S.scale N)) atTop atTop := (hs.const_mul_atTop he).const_mul_atTop he
  filter_upwards [hp.eventually_ge_atTop (k+b),hs.eventually_ge_atTop (1:ℝ)] with i hi hi'
  have hh : (Real.sqrt (Y.hatBeta i))^2=Y.hatBeta i := Real.sq_sqrt ((le_trans (by norm_num) (C.path.levels.fits.delayed i).le))
  have hl : (1+ε*C.S.scale i)^2 ≥ Y.hatBeta i := by
    let x := C.S.scale i
    have hx : 1≤x := hi'
    change b+k*x ≤ (1+ε*x)^2
    have hr : k+b ≤ ε*(ε*x) := hi
    nlinarith only [mul_le_mul_of_nonneg_right hr (show 0 ≤ x by linarith),
      le_mul_of_one_le_right (a:=b) Y.bar_pos.le hx,mul_nonneg he.le (show 0 ≤ x by linarith only [hx]), zero_le_one (α:=ℝ)]
  have hy : Real.sqrt (Y.hatBeta i) ≤ Real.exp (ε*C.S.scale i) := by
    have hv := Real.add_one_le_exp (ε*C.S.scale i)
    have ht := Real.sqrt_nonneg (Y.hatBeta i)
    have hX : 0≤ε*C.S.scale i := mul_nonneg he.le (by linarith only [hi'])
    nlinarith only [hh,hl,hv,hX,ht]
  unfold Calendar.threshold Calendar.hatCoupling
  rw [mul_inv_rev, inv_inv]
  exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) (inv_le_one_of_one_le₀ (Real.one_le_exp (sq_nonneg _)))).trans hy

lemma columns_paid (C : Family G) (F : Extraction.Order) : Score C.S F fun i=> (C.path.levels.params i.1).columns := by
  apply Score.of_mesh (f:=fun i : ℕ => (C.path.levels.params i).columns)
  intro ε he
  filter_upwards [Work.D01.columnLogs_le C.path.levels ε he,eventually_gt_atTop 0] with i hi hx
  cases i with
  | zero=> omega
  | succ j =>
    let x := (C.path.levels.params (j+1)).columns
    have hp : Real.log x ≤ ε*C.S.scale (j+1) := le_trans (b:=Work.D01.columnLogs _ _)
      (by rw [Work.D01.columnLogs_succ]; exact le_add_of_nonneg_left (Work.D01.columnLogs_nonneg ..)) hi
    change x ≤ _
    exact (Real.exp_log (show 0<x from lt_of_lt_of_le zero_lt_one (C.path.levels.params _).columns_ge)) ▸ Real.exp_le_exp.mpr hp

-- Fixed frame pricing.
lemma counted_grade (B : Frame G d) (i : B.Index) : (B.grades i).2 ≤ d := by
  classical
  let p := B.basis i
  have he : p.val≠0 := fun he=> B.basis.ne_zero i (Subtype.ext he)
  obtain ⟨k,hk⟩ : p.val.support.Nonempty := by simpa [Finset.nonempty_iff_ne_empty,MvPolynomial.support_eq_empty] using he
  have hb : Finsupp.weight bidegree k=B.grades i := (pure_grade _ p).mp (B.pure i) (MvPolynomial.mem_support_iff.mp hk)
  have ht := power_le k
  have hr := weight_slot k
  have h0 := B.bound i; rw [← hb,hr] at h0; rw [← hb]; exact ht.trans h0

lemma issued (C : Family G) (N d) (x : C.label d) : ‖tied C d N x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  let Q := C.labels.level d
  let t := (C.path.levels.budget N).threshold
  have he : 0≤ t^(Q.grades i).2 := pow_nonneg (positive_t C N).le _
  have ht : t^(Q.grades i).2 ≤ 1 := pow_le_one₀ (positive_t C N).le (C.path.levels.budget N).threshold_le
  change ‖Q.scaled t x i‖ ≤ _
  rw [Frame.scaled_apply,norm_mul, Complex.norm_real,Real.norm_of_nonneg he]; exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_le_pi_norm _ _)

lemma pay_back (C : Family G) (N d) (x : C.label d) : ‖(tied C d N).symm x‖ ≤ (C.path.levels.clock.threshold N)⁻¹^d * ‖x‖ := by
  let θ := (C.path.levels.budget N).threshold
  have he : 0<(C.path.levels.clock.threshold N)⁻¹ := inv_pos.mpr (positive_t C N)
  have ht : 1 ≤ θ⁻¹ := (one_le_inv₀ (positive_t C N)).mpr (C.path.levels.budget N).threshold_le
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (pow_pos he _).le (norm_nonneg _))).mpr
  intro i
  change ‖(C.labels.level d).scaled θ⁻¹ x i‖ ≤ _
  change 0 < θ⁻¹ at he
  rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg he.le _)]
  exact mul_le_mul (pow_le_pow_right₀ ht (counted_grade ..)) (norm_le_pi_norm x i) (norm_nonneg _) (pow_nonneg he.le _)

def writing (C : Family G) (d : ℕ) (x : Rowe C d) (j : ℕ×ℕ) :=
  (tied C d j.1).symm ((C.factory d j.1 j.2).terminal.symm (x j))

lemma dollar_iff (x : Rowe C d) : dollar C F x ↔ Score C.S F (fun i=> ‖writing C d x i‖) := by
  rw [accounting]
  refine ⟨fun hx=>?_,fun hg=>?_⟩
  · have he := (warm C F).power (Eventually.of_forall fun i=> (inv_pos.mpr (positive_t C _)).le) d
    exact (he.mul hx (Eventually.of_forall fun _=> norm_nonneg _)).easier (Eventually.of_forall fun i=> pay_back C _ d _)
  apply hg.easier; refine Eventually.of_forall fun i=> ?_
  have ht := issued C i.1 d (writing C d x i); unfold writing at *
  rw [LinearEquiv.apply_symm_apply] at ht; exact ht

-- enlarge from fixed-ref ball only when reference coords themselves grow subexponentially
lemma from_ref (h : C.Makes) (x : Rowe C d) (he : Score C.S F (fun i=> ‖x i‖)) : dollar C F x := by
  rw [accounting]
  intro ε hε
  let T := fun i : ℕ × ℕ=> ((C.factory d i.1 i.2).terminal.symm : C.label d≃ₗ[ℂ]C.label d) -- ?
  have ho : ∀ᶠ i : ℕ×ℕ in F.fuse, ‖((T i).toContinuousLinearEquiv.toContinuousLinearMap)‖ ≤ Real.exp ((ε/2)*C.S.scale i.1) := by
    have hw := Work.D01.terminal_ball C h d 1 (ε/2) (half_pos hε)
    rw [Extraction.Order.fused]
    refine Eventually.of_forall fun p=> (F.mesh.cofinal.eventually hw).mono (fun j hN=>?_)
    let N := F.mesh j
    -- opNorm ≤ via unit sphere
    let f := (T (N,F.per p)).toContinuousLinearEquiv.toContinuousLinearMap
    let B := Real.exp ((ε/2)*C.S.scale N)
    refine f.opNorm_le_bound (Real.exp_pos _).le fun z=>?_
    by_cases hz : z=0
    · simp [hz]
    let c : ℂ := ((‖z‖⁻¹ : ℝ):ℂ)
    have hn : 0<‖z‖ := norm_pos_iff.mpr hz
    have hc : ‖c‖=‖z‖⁻¹ := by unfold c; rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hn).le]
    have hx : ‖c • z‖ ≤ 1 := by rw [norm_smul,hc,inv_mul_cancel₀ hn.ne']
    have hh : ‖f (c • z)‖ ≤ B := hN _ _ hx
    rw [map_smul,norm_smul,hc,mul_comm,← div_eq_mul_inv] at hh
    exact (div_le_iff₀ hn).mp hh
  filter_upwards [ho, he _ (half_pos hε)] with i hi hg
  apply le_trans (((T i).toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm (x i))
  apply (mul_le_mul hi hg (norm_nonneg _) (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]; ring_nf
end YM.Push.Mark
