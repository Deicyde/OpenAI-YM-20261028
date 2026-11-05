import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment
/-!
# Growth invoices. Horizon Y.dim polynomial in B seam, not
 arbitrary Price. Every auxiliary purchase will be post D input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {G : Gauge} {L : Side} {f g H : ℝ→ℝ}

-- polynomial order, explicit time bounds at redemption. Doesn't buy on all s.
structure Bolt (G : Gauge) (L : Side) (f : ℝ→ℝ) : Prop where
  spends : ∃ (d:ℝ) (k:ℕ), 0 ≤ d ∧ ∀ᶠ x in atTop, |f x| ≤ d*Delay.bill G L x^k
namespace Bolt
variable (p : Bolt G L f)
include p
lemma uses : Rate G L 0 f := by
  obtain ⟨d,k,h,H⟩:=p.spends; have ht:= Rate.bill (G:=G) (L:=L) |>.pow k|>.mul_left d; rw [zero_mul] at ht
  exact Rate.compare ht (H.mono fun x hx=> hx.trans (le_abs_self _))
-- slow algebra
omit p in
lemma still (d : ℝ) : Bolt G L (fun _=> d) := ⟨|d|,0,abs_nonneg _,by simp⟩
lemma times (h : Bolt G L g) : Bolt G L (fun x=> f x*g x) := by
  obtain ⟨a,k,ha,H⟩:=p.spends; obtain ⟨b,j,h,he⟩:=h.spends
  refine ⟨a*b,k+j,mul_nonneg ha h,?_⟩; filter_upwards [H,he] with x hx hy
  rw [pow_add,abs_mul]; exact (mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)).trans_eq (by ring)
lemma joins (h : Bolt G L g) : Bolt G L (fun x=> f x+g x) := by
  obtain ⟨a,k,ha,H⟩:=p.spends; obtain ⟨b,j,h,he⟩:=h.spends
  refine ⟨a+b,k+j,add_nonneg ha h,?_⟩; filter_upwards [H,he] with x hx hy; rw [add_mul]
  refine (abs_add_le _ _).trans ((add_le_add hx hy).trans (add_le_add ?_ ?_)); all_goals apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (Delay.bill_ge G L x) (by omega)) (by linarith only [ha,h])
lemma nod (k:ℕ) : Bolt G L (fun x=> f x ^ k) := by
  induction k with
  | zero=> simp only [pow_zero]; exact still 1
  | succ i ih=> simp_rw [pow_succ]; exact ih.times p
lemma listens {e : ℝ} (h : 0 < e) : ∀ᶠ x in atTop, |f x| ≤ Delay.fineMonitor G L x ^ e := by
  obtain ⟨a,k,hA,H⟩:=p.spends; filter_upwards [H,Delay.monitor_pays G L k hA h] with x hx hv using hx.trans hv
omit p
lemma size : Bolt G L (fun x=> (radiusB x:ℝ)) := ⟨1,1,zero_le_one, Eventually.of_forall fun x=> by have hv:=sq_nonneg (Real.log (betaF G x L)); simp [Delay.bill]; linarith⟩
end Bolt

lemma impact (Q : Matrix ι ι ℝ) {D P v p s : ℝ} (h : Q.PosDef) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hq : ∀ z : ι→ℝ,dotProduct z (Q *ᵥ z) ≤ p*dotProduct z z) (hp : (Fintype.card ι:ℝ) ≤ P) (hP : 1≤P) (ht : P*v≤D) :
    1 - (sweep Q).real (closedBall (0:Poll.Body ι) D) ≤ P*(2*Real.exp (-s*v+p*s^2/2)) := by
  let μ:= sweep Q; let Z:=closedBall (0:Poll.Body ι) D; have he : μ.real Zᶜ=1 - μ.real Z := by rw [measureReal_compl (measurableSet_closedBall),probReal_univ]
  let A i := {x : Poll.Body ι| v≤|x i|}
  have hK : Zᶜ ⊆ ⋃ i∈ (Finset.univ:Finset ι), A i := by
    intro x hz; by_contra hx; simp only [A,mem_iUnion,mem_setOf_eq,Finset.mem_univ,true_and,exists_prop] at hx; push Not at hx
    apply hz; rw [mem_closedBall_zero_iff]
    have hh : ‖x‖^2 ≤ P*v^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; apply (Finset.sum_le_sum (f:=fun i=> x i^2) (g:=fun _=> v^2) (fun i _=> by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ((hx i).le) _)).trans
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    apply le_trans _ ht; rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (zero_le_one.trans hP) hv),mul_pow]; exact hh.trans (mul_le_mul_of_nonneg_right (le_self_pow₀ hP (by decide)) (sq_nonneg _)) -- direction
  rw [← he]; apply ((measureReal_mono hK (measure_ne_top (sweep Q) _)).trans (measureReal_biUnion_finset_le _ _)).trans
  have he i : μ.real (A i) ≤ 2*Real.exp (-s*v+p*s^2/2) := by simpa [A] using rectangle h.posSemidef hq ({i}:Finset ι) v s hs
  refine (Finset.sum_le_sum (fun i _=>he i)).trans ?_; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right hp; positivity
lemma walls (G : Gauge) (L : Side) {f : ℝ→ℝ} (hf : Bolt G L f) {c d : ℝ} (hc : 0<c) (h : 0<d) (φ : ℝ) :
    ∀ᶠ x in atTop, ∀ (ι:Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ), (Fintype.card ι:ℝ)≤ f x → Q.PosDef →
    (∀ z : ι→ℝ, dotProduct z (Q*ᵥ z)≤ c* dotProduct z z) → 1 - (sweep Q).real (closedBall (0:Poll.Body ι) (d * Delay.fineMonitor G L x)) ≤ betaF G x L ^φ := by
  let P x:=1+f x; have hP : Bolt G L P:= (Bolt.still 1).joins hf
  have hV := hP.listens (show 0<(1/2:ℝ) by norm_num)
  let r x:= (d*Real.sqrt (Delay.fineMonitor G L x)); let g x:= r x / c
  have hd : Rate G L (φ-1) (fun x=> 2*Real.exp (-g x*r x+c*g x^2/2)) := by
    refine Rate.mul_left ?_ _
    refine Rate.congr (Rate.monitor_cutoff (show 0<d*d/(2*c) by positivity) zero_lt_one) (Eventually.of_forall fun x=>?_)
    simp only [Real.rpow_one]; apply congr_arg Real.exp
    unfold g r
    field_simp; linear_combination -(Real.sq_sqrt (Delay.monitor_pos G L x).le)
  have hh := (hP.uses.mul hd) φ (by linarith); filter_upwards [hV,hh] with x hx hh ι _ _ Q hp hq hy
  have he:= Delay.monitor_pos G L x; have hD:0 ≤ r x := by unfold r; positivity
  have hz:1≤ P x := by unfold P; linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)]
  refine (impact Q hq hD (show 0≤g x from div_nonneg hD hc.le) hy (hp.trans (show f x≤P x from le_add_of_nonneg_left zero_le_one)) hz ?_).trans ((le_abs_self _).trans hh)
  rw [← Real.sqrt_eq_rpow] at hx; apply (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hx) hD).trans; unfold r; exact le_of_eq (by rw [mul_left_comm, ← sq, Real.sq_sqrt he.le])
end YM.PhysicalNext.Repeat.Lantern
