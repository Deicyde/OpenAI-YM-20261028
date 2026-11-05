import YM.Further.GAUSSIAN_SCALAR_LEDGER.Balance
import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.VACUUM_NORMALIZATION.Composition

set_option warningAsError false

/-!
# Output columns and exact scalar update

Single F; the same full tag reference as in the library. B0, base,
etc. are supplied *debits*, not assertions that they suffice for
persistence of prices or output dictionary. Addresses remain with
that same P,k,V,Y. No determination of pressure from a kinetic or
untruncated Hessian. In particular even at identity don't ignore the
interacting correction. The result is per period, no claims of N- or
period-limit estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Function Matrix MeasureTheory Filter Set
open Lattice RG Wilson Tree Precision SectorNext.Vacuum Pressure Push.SectorMeasure
open Next.Fluctuations.Sector
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {c f : Side} {S : StepData c f} {G : Gauge} {x W : ℝ} (F : Forest S.ratio) (O : ChartRatio G)
  {rooms : Type*} [Fintype rooms]

def commonBill (B0 : Wall (Key F G)) (β : ℝ) :=
    -wires c * Real.log (S.penaltyZ β G) +
    nt F * Real.log (gaussLink O β) - Real.log B0.det / 2

lemma commonCost (h : LocalRatio O) (B0 : Wall (Key F G)) (β : ℝ) (hb : 0 < B0.det) (hp : 0 < β) :
    Real.exp (commonBill F O B0 β)=prefactor S G β * flatLine F O β B0 := by
  have hl := link_factor_pos O h β hp
  have he := S.penaltyZ_pos (G:=G) β
  have hs := Real.sqrt_pos.mpr hb
  unfold commonBill flatLine prefactor wires
  rw [Real.exp_sub,Real.exp_add,neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log hl,
      Real.exp_log he, ← Real.log_sqrt hb.le,Real.exp_log hs, inv_pow]; ring

variable {F O} (R : Rep G f) (B0 : Wall (Key F G)) (G0 : Config G c → ℝ) (d : Allocation G S x W)
    (v : Stores S → S.Choices → Config G c → Fiber F O rooms)

def listing (P : Stores S) (V : Config G c) :=
    ∑ k, tagRef k * ((v P k V).till d P k V R (G0 V) B0)

def liftedTally (V : Config G c) := ∑ P, listing R B0 G0 d v P V

structure Scanner (η L q : ℝ) : Prop where
  patches (P k V) : Opened O (v P k V).veil d P k V
  matrixRule (P k V) : (v P k V).Rates η L q
  hermitian : B0.IsHermitian
  logRule : Numeric B0 η L
  -- supply even if no addresses
  pos : 0 < η

variable {η L q : ℝ}

lemma basal (p : Scanner B0 d v η L q) : 0 < B0.det :=
  (Panel.determinant p.hermitian p.logRule p.pos).1

lemma peeled (h : LocalRatio O) (p : Scanner B0 d v η L q)
    (hm : S.patch.Branches S.kernel G) {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w) (hp : 0 < R.beta)
    (P : Stores S) (V : Config G c) :
    output d F R.beta (stripped R) P V = Real.exp (commonBill F O B0 R.beta)*
        Real.exp (-G0 V)*listing R B0 G0 d v P V := by
  rw [balanced_column d F R.beta hm,commonCost F O h B0 R.beta (basal B0 d v p) hp]
  simp only [listing, smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(v P i V).supplies d P i V R (G0 V) h hm (p.matrixRule ..) (p.patches P i V) hR hp B0
    (basal B0 d v p)]
  ring

theorem collects (h : LocalRatio O) (p : Scanner B0 d v η L q)
    (hm : S.patch.Branches S.kernel G) {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w) (hp : 0 < R.beta)
    (V : Config G c) :
    S.push R.beta (stripped R) V = Real.exp (commonBill F O B0 R.beta)*
        Real.exp (-G0 V) * liftedTally R B0 G0 d v V ∧
    S.push R.beta R.eval V = Real.exp (R.scalar + commonBill F O B0 R.beta)*
        Real.exp (-G0 V) * liftedTally R B0 G0 d v V := by
  have he (P : Stores S) := peeled R B0 G0 d v h p hm hR hp P V
  have hg := Presented.lawful_gi hR
  have hl := (R.envelope hR).integrable (prior G f)
  have hv : GaugeInvariant (stripped R) := fun k U => by unfold stripped; rw [hg]
  constructor
  · rw [← push_columns d F _ _ hm (stripped_int R hR) hv]
    unfold liftedTally; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun P _ => he P
  rw [← push_columns d F _ _ hm hl hg, Real.exp_add]; simp_rw [output_factors,←Finset.mul_sum]
  unfold liftedTally; simp_rw [he,← Finset.mul_sum]
  ring

/-- On actual positive input density (e.g. via previous steps).
No transfer assumption needed. Positivity on RAW TOTAL, not each
listing, row or reorganized activity. Also holds separately even
with nonzero G0(1). -/
theorem logarithms (h : LocalRatio O) (p : Scanner B0 d v η L q)
    (hm : S.patch.Branches S.kernel G) {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w) (hp : 0 < R.beta)
    (hn : ∀ a, 0 ≤ R.eval a) (V : Config G c) :
    let T := liftedTally R B0 G0 d v
    0 < T V ∧ Real.log (S.push R.beta R.eval V) =
        R.scalar + commonBill F O B0 R.beta-G0 V+Real.log (T V) := by
  intro T
  have he := (collects R B0 G0 d v h p hm hR hp V).2
  have hl := push_pos S hm R.beta R.eval ((R.envelope hR).integrable _) hn (by
    exact lt_of_lt_of_le (Real.exp_pos _) (R.denominator hR hp.le R.p.threshold R.p.threshold_pos le_rfl hn)) V
  have ht : 0 < T V := pos_of_mul_pos_right (he ▸ hl) (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  refine ⟨ht,?_⟩
  rw [he,Real.log_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' ht.ne',
    ← Real.exp_add,Real.log_exp]; rfl

/-- With output Lawful and push transfer, even without any separate
input positivity clause here. Identity fixes v, not beta or alpha. -/
theorem records (h : LocalRatio O) (p : Scanner B0 d v η L q)
    (hm : S.patch.Branches S.kernel G) {σ C Λ δ w : ℝ} (hR : R.Lawful σ C Λ δ w) (hp : 0 < R.beta)
    (E : Rep G c) {σ' C' Λ' δ' w' : ℝ} (hE : E.Lawful σ' C' Λ' δ' w')
    (hi : E.eval=S.push R.beta R.eval) :
    let Y := liftedTally R B0 G0 d v 1
    0 < Y ∧
      jump E R = commonBill F O B0 R.beta-G0 1+Real.log Y ∧
      E.v = (S.patch.L.val:ℝ)^4*R.v - 4*Real.log (S.penaltyZ R.beta G) +
        (nt F*Real.log (gaussLink O R.beta)-Real.log B0.det/2-G0 1+Real.log Y)/sites c := by
  intro z
  have he := (collects R B0 G0 d v h p hm hR hp 1).1
  rw [reveal S R E hE hi] at he
  have zh : 0 < z := pos_of_mul_pos_right (he ▸ Real.exp_pos (jump E R))
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have ht : jump E R = commonBill F O B0 R.beta-G0 1+Real.log z := by
    have hl := congr_arg Real.log he
    rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' zh.ne', ← Real.exp_add,
      Real.log_exp,Real.log_exp] at hl
    exact hl
  refine ⟨zh,ht,?_⟩
  rw [update S R E hE hi,reveal S R E hE hi, Real.log_exp,ht]
  unfold commonBill; rw [wires_sites]
  have hl := site_pos c
  field_simp; ring



end YM.Further.GaussianScalar
