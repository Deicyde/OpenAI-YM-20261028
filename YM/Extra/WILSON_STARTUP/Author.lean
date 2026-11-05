import YM.Extra.WILSON_STARTUP.Clock
import YM.Extra.WILSON_STARTUP.SourceInk


/-!
# Purchase and feed top `Paper.Clocks` inputs on the retained path

No claims on transfer equations/steps below the cutoff. Threshold/value
computations independent of later extraction orders. Uses the actual
local polynomial stencils (incl repeated slots), honest β representation,
linear in the initially given coefficients, and γ/caps at N. Includes cost
for all (translated) origins and exact bare relation with a_N^{-d}.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Mark
open Function Filter RG Wilson Lattice Source Work Start Timing
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}

def diameter (C : SectionData F) := C.stencil.sup (fun x => Finset.univ.sup fun i => (x i).natAbs)

lemma stencil (C : SectionData F) (b : BudgetPoint) (n : Side) (h : diameter C ≤ b.B) (o : Site n) : Tight b (C.footprint o) := by
  have he (x : Site n) (hx : x ∈ C.footprint o) : separation x o ≤ b.B := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    rw [separation,add_sub_cancel_right]; apply le_trans (b:=diameter C) _ h
    apply Finset.sup_le; intro i hi
    exact (Corona.lap ..).trans ((Finset.le_sup (f:=fun i : YM.Axis => (v i).natAbs) hi).trans (Finset.le_sup
      (f:=fun v : Cover => Finset.univ.sup fun i => (v i).natAbs) hv))
  intro x hx y hy
  apply (separation_triangle x o y).trans
  rw [separation_comm o y]; have := he x hx; have := he y hy; omega

structure Ready (a : Levels G) (C : SectionData F) (N : ℕ) : Prop where
  widths : diameter C ≤ (a.budget N).B
  freedom : a.clock.forcedAllowance N * Mark.scale C (a.budget N) ≤ Real.sqrt (a.clock.forcedAllowance N)

lemma suppression (C : SectionData F) : ∀ᶠ s : ℝ in atTop,∀ b : BudgetPoint, b.threshold=temp s →
    normK s * scale C b ≤ Real.sqrt (normK s) := by
  open Real in
  have hp : 0 < price C := one_pos.trans_le (price_ge_one C)
  let N := slotOrder F
  filter_upwards [hard_growth 2,eventually_ge_atTop ((N:ℝ)+2*Real.log (price C)+1)] with s hs hh b ht
  have hz := Real.log_nonneg (price_ge_one C)
  rw [normK,scale,ht,temp,← Real.exp_neg, ← Real.exp_nat_mul, Real.sqrt_eq_rpow, ← Real.exp_mul,← Real.exp_log hp,
    ← Real.exp_add,← Real.exp_add, Real.exp_le_exp]
  have h : (-(s/2)+(Real.log s)^2) ≥ -(s/2) := by nlinarith
  change -Real.exp _ + ((N:ℝ)*_+_) ≤ _
  nlinarith

lemma attain (C : SectionData F) : ∀ᶠ x : ℝ in atTop, ∀ a : Levels G, ∀ N,
    a.clock.hatBeta N=x → Ready a C N := by
  filter_upwards [Real.tendsto_log_atTop.eventually (suppression C),
    Real.tendsto_log_atTop.eventually (nballs.eventually_ge_atTop (diameter C)),eventually_gt_atTop (0:ℝ)] with x h hs hx a N hN
  rw [← hN] at h hs hx
  have he := h (a.budget N) (by
    unfold Levels.budget Calendar.threshold Calendar.monitor Calendar.hatCoupling temp
    dsimp only; rw [Real.exp_add, Real.exp_neg, Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; ring_nf)
  refine ⟨hs,?_⟩
  unfold Calendar.forcedAllowance Calendar.monitor; rw [← Real.exp_mul]
  unfold normK at he; convert he using 2 <;> ring_nf

def initialData (H : History G) (C : SectionData F) (N p : ℕ) (o : Site (H.S.side N p)) (v : F.Coeff) :=
    entry C o (H.rep N p N) v

structure Prepared (H : History G) (C : SectionData F) (A : Hol G) (N p : ℕ) (o : Site (H.S.side N p)) : Prop where
  uses (v : F.Coeff) : (initialData H C N p o v).Format o A (H.rep N p N)
  bound (v : F.Coeff) : (initialData H C N p o v).remBound o (H.rep N p N) (Real.sqrt (H.levels.clock.forcedAllowance N)) (F.coeffSize (F.core v))
  linear : IsLinearMap ℂ (fun v : F.Coeff => (initialData H C N p o v).forced)
  exact_match (v : F.Coeff) U : (initialData H C N p o v).density o C (H.rep N p N) U =
    ((H.S.a N : ℂ)^d) * ((H.rep N p N).eval U : ℂ) * initial C H N p v o U

theorem issue (H : History G) (C : SectionData F) (N p : ℕ) (h : C.Sound A) (ha : Ready H.levels C N)
    (hH : H.Conv N p N) (hw : Wide (H.rep N p N)) (o : Site (H.S.side N p)) : Prepared H C A N p o := by
  refine ⟨fun v => format C h o _ hH.good.labels.forced v,fun v => fees C h o _ v hH.good.labels.boundK (Real.sqrt_pos.mpr (Real.exp_pos _))
    (by rw [hH.vac]; exact ha.freedom),fee_linear ..,fun v U => ?_⟩
  rw [initialData,Mark.encoding C h o _ hw (by rw [hH.vac]; exact stencil C _ _ ha.widths o)]
  unfold initial; rw [mul_comm ((_ : ℂ)^d), Pi.smul_apply, smul_eq_mul, mul_assoc ((_:ℝ):ℂ), mul_inv_cancel_left₀
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos N).ne'))]
  dsimp only [realMaskFree, LinearMap.comp_apply]; rw [hH.vac]; rfl

open Precision Input RG.Shoot
variable {S : Supply.Sheet G} {D : Supply.Rolls S} {T : Supply.Protection D} {W : Supply.Delays T} {Y : Supply.Bar W}
  {I : Supply.Wait Y} {O : ChartRatio G} {K : MapPrices} {Q : PostCost D}


end YM.WilsonStartup.Mark
