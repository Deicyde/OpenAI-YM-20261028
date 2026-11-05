import YM.Extra.SOURCE_HISTORIES.Birth
import YM.Next.FOUNDATIONS.Primary

/-!
# Entrance cost for one-source birth, at PURCHASED support exponent

Grow exponents, cover sizes, let thresholds tend small. Before any
reconstruction, buy birth costs as stage-local hatted beta gates. Works
for all p. These gates still need to be bought simultaneously with vacuum
& local analytic ones, not supplied by a Bolt alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Doors
open Function Filter Lattice Wilson RG Supply Source Labels Bid Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

def cameras (G : Gauge) (d : ℕ) : ℝ := (full_value_bound G d).choose
lemma cameras_ge (G : Gauge) (d : ℕ) : 1≤cameras G d := (full_value_bound G d).choose_spec.1
lemma cameras_holds (G : Gauge) (d : ℕ) (n : Side) :
    ∀ i, ∀ (o : Site n) (U : Config G n), ‖(localSection G d).places (Size.axis ((frames G).level d) i) o U‖ ≤ cameras G d :=
    fun i => ((full_value_bound G d).choose_spec.2 i).2 n

lemma close_stencil (G : Gauge) (d M : ℕ) (n : Side) (h : minSide G d ≤ M) (o : Site n) :
    coverNumber M ((localSection G d).footprint o) ≤ 1 := by
  let T := localSection G d
  refine le_trans (Corona.list_cost M (D:={o}) ⟨?_,?_⟩) (Finset.card_singleton _).le
  · intro i hi
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    refine halo_spec.mpr ⟨_,Finset.mem_singleton_self o,?_⟩
    rw [separation_comm,separation,add_sub_cancel_right]
    apply Finset.sup_le; intro i _
    refine (Corona.lap x i).trans ?_
    have he := stencil_price G h x hx i
    omega
  refine Corona.ship_halo M ?_
  rintro x hx y hy
  obtain rfl : x=o := Finset.mem_singleton.mp hx
  obtain rfl : y=x := Finset.mem_singleton.mp hy
  exact Relation.ReflTransGen.refl

def stain (x : ℝ) := Real.exp (-(Real.exp (Real.log (Real.log x)^2) ^ ((1:ℝ)/5)))
lemma stain_pos (x : ℝ) : 0 < stain x := Real.exp_pos _
lemma stain_le (x : ℝ) : stain x ≤ 1 := by unfold stain; rw [Real.exp_le_one_iff]; exact neg_nonpos.mpr (by positivity)

/-- The forced divisor gives MORE than any one fixed-beta power. -/
lemma stain_beats (n : ℕ) : ∀ᶠ x : ℝ in atTop, Real.sqrt (stain x) * x^n ≤ 1 := by
  let c : ℝ := 2*(n+1 : ℕ)
  have hc : 0 < c := by unfold c; positivity
  let u := fun x => Real.log (Real.log x)
  have ht : Tendsto u atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually_ge_atTop 10, (Real.tendsto_exp_atTop.comp ht).eventually_ge_atTop c,
    eventually_gt_atTop (1:ℝ)] with x hx hv hr
  let y := Real.exp ((1:ℝ)/5 * u x ^ 2)
  have hx' : (Real.exp (u x ^ 2)) ^ ((1:ℝ)/5) = y := by
    unfold y; rw [← Real.log_exp (u x ^ 2), Real.exp_log (Real.exp_pos _), ← Real.log_rpow (Real.exp_pos _),
      Real.exp_log (by positivity)]
  have hu : 2*(n:ℝ)*Real.log x ≤ y := by
    have hl := Real.log_pos hr
    have h : 2*(n:ℝ)≤c := by unfold c; push_cast; linarith
    have he : Real.exp (u x) = Real.log x := Real.exp_log hl
    calc
      _ ≤ c*Real.log x := mul_le_mul_of_nonneg_right h hl.le
      _ ≤ Real.exp (u x)*Real.log x := mul_le_mul_of_nonneg_right hv hl.le
      _ = Real.exp (u x+u x) := by rw [Real.exp_add,he]
      _ ≤ _ := Real.exp_monotone (by nlinarith)
  have hq : 0 < Real.sqrt (stain x)*x^n := by have := stain_pos x; positivity
  apply (Real.log_le_log_iff hq one_pos).mp
  rw [Real.log_mul (by have := stain_pos x; positivity) (by positivity), Real.log_pow, Real.log_sqrt (stain_pos x).le,
    Real.log_one, stain, Real.log_exp,hx']
  linarith

/-- elementary difference bound incl the all-good cost exactly once. -/
lemma exp_difference (x : ℝ) : Real.exp x-1 ≤ x*Real.exp x := by
  have he := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg x) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at he
  linarith

lemma temp_cheap {x : ℝ} (hx : 1≤x) : (Pressure.temp x)⁻¹ ≤ x := by
  let b := Real.exp (Real.log (Real.log x)^2)
  have hb : 1≤ b := Real.one_le_exp (sq_nonneg _)
  have he : Real.sqrt x ≤ x := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
  unfold Pressure.temp
  rw [mul_inv_rev, inv_inv]
  exact (show b⁻¹*Real.sqrt x ≤ Real.sqrt x by
    conv_rhs => rw [← one_mul (Real.sqrt x)]
    gcongr
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hb)).mpr hb).trans he

/-- Numeric bill fits eventually with *fixed* F, cardinal & exponent
A, as hatBeta x grows. -/
lemma within (n : ℕ) (C R A : ℝ) (hc : 0≤C) (hR : 0≤R) : ∀ᶠ x : ℝ in atTop,
    C*(Pressure.temp x)⁻¹^n * (Real.exp A * (Real.exp (R*stain x)-1)) ≤ Real.sqrt (stain x) := by
  let K := C*Real.exp A * R*Real.exp R
  have hk : 0≤ K := by unfold K; positivity
  filter_upwards [stain_beats (n+1),eventually_gt_atTop (1:ℝ), eventually_ge_atTop K] with x hx hx' hh
  have hw := stain_pos x
  have ht : 0 < Pressure.temp x := Work.E09.temp_pos (by linarith)
  have hu : C*(Pressure.temp x)⁻¹^n ≤ C*x^n := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr ht.le) (temp_cheap hx'.le) n) hc
  have hy : Real.exp (R*stain x) ≤ Real.exp R := Real.exp_monotone (by
    exact (mul_le_mul_of_nonneg_left (stain_le x) hR).trans (mul_one R).le)
  have hz : (Real.exp (R*stain x)-1) ≤ R*stain x*Real.exp R := (exp_difference _).trans
    (mul_le_mul_of_nonneg_left hy (by positivity))
  calc
    _ ≤ C*x^n * (Real.exp A * (R*stain x*Real.exp R)) := mul_le_mul hu
      (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le)
      (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.one_le_exp (by positivity)))) (by positivity)
    _ = K*x^n*stain x := by unfold K; ring
    _ ≤ x^(n+1)*stain x := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq
      (by ring)) hw.le
    _ ≤ Real.sqrt (stain x) := calc
      _ = (Real.sqrt (stain x)*x^(n+1))*Real.sqrt (stain x) := by
        nth_rw 1 [← Real.sq_sqrt hw.le]; ring
      _ ≤ 1*Real.sqrt (stain x) := mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _)
      _ = _ := one_mul _

structure Latch (G : Gauge) (d : ℕ) (K : Levels G) (m : ℕ) : Prop where
  lengths p : minSide G d ≤ (K.S.side m p).val
  receipts p (o : Site (K.S.side m p)) : fee ((frames G).level d) (K.budget m) ((localSection G d).footprint o) (cameras G d)
    (K.clock.forcedAllowance m) ≤ Real.sqrt (K.clock.forcedAllowance m)

/-- BEFORE all periods. j-local, using floors from the current Stage. -/
lemma latch_cost (G : Gauge) (d : ℕ) (A : ℝ) : ∃ k : ℝ, ∀ K : Levels G, ∀ m : ℕ,
    (K.params m).supportExponent=A → k ≤ K.clock.hatBeta m → Latch G d K m := by
  let T := localSection G d
  let C := cameras G d
  let F := (frames G).level d
  have hc : 0≤C := zero_le_one.trans (cameras_ge G d)
  let R := (T.stencil.card:ℝ)
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((within (degree F) C R A hc (Nat.cast_nonneg _)).and
    (Work.E01.radiusB_tendsto.eventually_ge_atTop (minSide G d)))
  refine ⟨k, fun K m h hM => ?_⟩
  let P := K.budget m
  have hu := hk _ hM
  have hp : minSide G d ≤ P.B := hu.2
  refine ⟨fun p => ?_,fun p o => ?_⟩
  · have h := K.fits.sizeT m p
    exact hp.trans (show K.clock.coverSize m ≤ (K.clock.schedule.side m p).val by omega)
  let w := K.clock.forcedAllowance m
  let Y := T.footprint o
  change fullCost F P C*(P.mass Y 1*(Real.exp (Y.card*w)-1))≤Real.sqrt w
  have hw : 0≤ w := (forcedPos ..).le
  refine le_trans ?_ hu.1
  change fullCost F P C*_ ≤ fullCost F P C*_
  apply mul_le_mul_of_nonneg_left _ (by have := P.threshold_pos; unfold fullCost; positivity)
  have hx : P.mass Y 1≤Real.exp A := by
    have hq : (coverNumber P.B Y:ℝ)≤1 := by exact_mod_cast close_stencil G d P.B _ hp o
    unfold BudgetPoint.mass; rw [mul_one]; apply Real.exp_monotone
    have he : P.supportExponent=A := h
    have ha := P.exponent_pos
    nlinarith
  apply mul_le_mul hx (sub_le_sub_right (Real.exp_monotone ?_) _) (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    (Real.exp_pos A).le
  exact mul_le_mul_of_nonneg_right (by unfold R; exact_mod_cast show Y.card ≤ T.stencil.card from Finset.card_image_le) hw

/-- Anticipate all d through j (more than reference rule d+3≤j) in betaEntry,
allow caller to monotonize more. Fits at *m* while `Paid.pays` uses J(m+1),
so anticipates j and previous possibilities together. -/
theorem entrances (P : Sheet G) : ∃ k : ℕ → ℝ, ∀ K : Levels G,
    K.clock.stage=P.profile → (∀ m, k (K.clock.J (m+1)) ≤ K.clock.hatBeta m) →
    ∀ d m, d ≤ K.clock.J m → Latch G d K m := by
  choose b hb using fun d j : ℕ => latch_cost G d (P.profile j).supportExponent
  let u (p : ℕ×ℕ) := max 0 (b p.1 p.2)
  let s (i : ℕ) := (Finset.range (i+1)).product (Finset.range (i+1))
  refine ⟨fun i => ∑ p∈s i,u p,fun K h he d m ht => ?_⟩
  let j := K.clock.J m
  let i := K.clock.J (m+1)
  have hg : j ≤ i := K.fits.mono m.le_succ
  refine hb d j K m ?_ (le_trans ?_ (he m))
  · unfold Levels.params Calendar.params; rw [h]
  have hx : (d,j)∈s i := by
    have hd : d < i+1 := Nat.lt_succ_of_le (ht.trans hg)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hd, Finset.mem_range.mpr (Nat.lt_succ_of_le hg)⟩
  exact (le_max_right 0 _).trans (Finset.single_le_sum (f:=u) (fun _ _ => le_max_left _ _) hx)

end YM.Extra.Histories.Doors
