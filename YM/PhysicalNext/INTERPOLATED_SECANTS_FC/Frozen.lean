import YM.Extra.ITERATION_NO_LOSS.Radius
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Account
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Interpolation
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Layout
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Occurrence
import YM.Push.LOCAL_SPLITTING.Raw
import YM.Push.SECTOR_MEASURE.Presented
import YM.Push.STRESS_FLUX.Haar
import YM.SectorNext.VACUUM_NORMALIZATION.Bulk
import YM.UVNext.COUPLING_RESET.Prices
import YM.UVNext.PRICED_KERNELS.Seats

/-!
Uses an ABSOLUTE localized price on the low residuals (unary & binary tuple,
after pairing with actual coupling powers on original footprint; then aligned
pure-low remainder, each through k, NOT assuming a derivative of either price)
with inputs frozen at every retiming in the physical band.

High tuples from the
first integrated jet prices.

Finite observation interpolation on this same
organization earns a near-no-loss proportional drift, regardless of possible
coupling cancellations needed in the size estimates before multiplying by inverse beta.

Requires high orders only in the scalar RETIMING with all masks/data fixed, never an
extra order in U or V.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Function Filter Finset Set Lattice Wilson RG Push.Local Push.AbsoluteSums Trees Ursell Further.LogJets
open scoped Classical Matrix.Norms.Frobenius Topology BigOperators ContDiff
variable {G : Gauge} {n : Side} {ι κ H : Type*}
namespace Content
variable (f : Content G n ι κ H) (A : Placement G n ι κ) (p : BudgetPoint)

def depth : ℕ := 40
lemma deep : 6 < depth := by decide

structure FrozenOrders (h : H) (y a γ q : ℝ) : Prop where
  charts : ∀ t∈closedTimes, ∀ i U, Healthy p.threshold (A.reads i) U → Chart p.order (f.unforced (encoded y t) h i) U
  priced : ∀ t∈closedTimes, ∃ c : ι → ℝ, Ready A.reads p.B c (a+2) γ 1 q ∧
    ∀ i, p.supBounds (A.site i) (A.reads i) (f.unforced (encoded y t) h i) (c i)
  continuous i (u : Reading G p (A.atom i)) : ContinuousOn (fun t => u.jet (f.unforced (encoded y t) h i)) closedTimes
  retimed : ∀ t∈times, ∃ c : ι → ℝ, Ready A.reads p.B c (a+2) γ 1 q ∧ ∀ i (u : Reading G p (A.atom i)),
    let F := fun t => u.jet (f.unforced (encoded y t) h i)
    ContDiffAt ℝ depth F t ∧ ∀ j ≤ depth, |iteratedDeriv j F t| ≤ c i

structure Deficit (h : H) (y a M : ℝ) : Prop where
  primary (z : Clusters ι) (u : Reading G p (A.cluster z)) (hz : z.1<2) j : Chart p.order (f.approx z j) u.point
  secondary i (u : Reading G p (A.aligned i)) j : Chart p.order (f.fresh i j) u.point
  low : ∀ t∈closedTimes, ∃ c : Clusters ι → ℝ, (∀ z, 0 ≤ c z ∧ (z.1<2 → p.supBounds (A.cluster z).site (A.cluster z).support
    (f.tail A y (encoded y t) h z) (c z))) ∧ Seated A.cluster p.B c a M
  high : ∀ t∈closedTimes, ∃ c : ℕ → ℝ, (∀ i,p.supBounds (A.aligned i).site (A.aligned i).support
    (f.processed y (encoded y t) i) (c i)) ∧ Seated A.aligned p.B c a M

variable {f A p} {h : H} {y a γ q M : ℝ}

lemma ready_widen {Y : ι → Support n} {c : ι → ℝ} (h : Ready Y p.B c a M 1 q) (hr : degreePrice p.B γ 1 ≤ q) (hM : M≤γ) :
    Ready Y p.B c a γ 1 q := ⟨h.1.trans_le hM,h.2.1,hr,h.2.2.2.1,h.2.2.2.2.1,fun x => budget_loosen (h.2.2.2.2.2 x) hM⟩

lemma FrozenOrders.widen {x : H} (h₀ : FrozenOrders f A p x y a (γ/8) q) (hT : degreePrice p.B γ 1 ≤ q) : FrozenOrders f A p x y a γ q := by
  refine ⟨h₀.charts,fun t ht => ?_,h₀.continuous,fun t ht => ?_⟩
  · obtain ⟨c,hc,H⟩ := h₀.priced t ht; exact ⟨_,ready_widen hc hT (by linarith [hc.1]),H⟩
  obtain ⟨c,hc,H⟩ := h₀.retimed t ht; exact ⟨_, ready_widen hc hT (by linarith [hc.1]),H⟩

namespace FrozenOrders
variable (hp : FrozenOrders f A p h y a γ q)
include hp
lemma raw_chart {t : ℝ} (ht : t∈closedTimes) (z : Clusters ι) (u : Reading G p (A.cluster z)) : Chart p.order
    (f.raw A (encoded y t) h z) u.point := by
  rw [raw,cost_eq]; apply scale_chart; exact contDiffAt_prod
    (fun j _ => hp.charts t ht _ _ (Disjoint.mono_left (covered A.reads z j) u.admitted))

lemma raw_continuous (z : Clusters ι) (u : Reading G p (A.cluster z)) : ContinuousOn (fun t => u.jet (f.raw A (encoded y t) h z)) closedTimes :=
  Cluster.part_continuous p (Y:=A.reads) (o:=A.site) z u.admitted (fun t ht i => hp.charts t ht i _) (fun i hi L hL hD => hp.continuous i ⟨_,hi,L,hL,hD⟩)
    u.dirs u.order
lemma raw_cost {t : ℝ} (ht : t∈closedTimes) : ∃ c : ι→ℝ, Ready A.reads p.B c (a+2) γ 1 q ∧
    ∀ z (u : Reading G p (A.cluster z)), |u.jet (f.raw A (encoded y t) h z)| ≤ Cluster.expense p A.reads c 0 z := by
  obtain ⟨c,hc,H⟩ := hp.priced t ht
  refine ⟨c,hc,fun z u => ?_⟩
  let F := f.unforced (encoded y t) h
  have hv := Cluster.mixed_part p (Y:=A.reads) (o:=A.site) (fun i => (A.atom i).anchor) z _ (A.cluster z).anchor u.admitted
    (f:=fun _ => F) (t:=t) 0 hc.2.2.2.2.1 (Eventually.of_forall fun _ i => hp.charts t ht i _)
    (fun i hi l hl hd => ⟨contDiffAt_const, fun j (he : j≤0) => Nat.eq_zero_of_le_zero he ▸ (H i).2 _ hi l hl hd⟩)
    _ u.order u.bounds
  exact hv.2 0 le_rfl
lemma raw_meter {t : ℝ} (ht : t∈times) : ∃ c : ι → ℝ, Ready A.reads p.B c (a+2) γ 1 q ∧
    ∀ z (u : Reading G p (A.cluster z)), let F := fun t => u.jet (f.raw A (encoded y t) h z)
      ContDiffAt ℝ depth F t ∧ ∀ j≤depth, |iteratedDeriv j F t| ≤ Cluster.expense p A.reads c depth z := by
  obtain ⟨c,hc,H⟩ := hp.retimed t ht; refine ⟨_,hc,fun z u => ?_⟩
  exact Cluster.mixed_part p (Y:=A.reads) (o:=A.site) (fun i => (A.atom i).anchor) z _ (A.cluster z).anchor u.admitted depth hc.2.2.2.2.1
    ((show ∀ᶠ v in 𝓝 t, v∈times from isOpen_Ioo.mem_nhds ht).mono fun v hv i => hp.charts v (Ioo_subset_Icc_self hv) i _)
    (fun i hi l hl hd => H i ⟨_,hi,l,hl,hd⟩) _ u.order u.bounds
end FrozenOrders

namespace Deficit
variable (hm : Deficit f A p h y a M)
include hm
lemma peeled_chart (z : Clusters ι) (u : Reading G p (A.cluster z)) (b : ℝ) : Chart p.order (f.peeled y b z) u.point := by
  unfold peeled; split
  · exact polynomial_chart (hm.primary z u ‹_›) _
  exact contDiffAt_const
lemma peels (z : Clusters ι) (u : Reading G p (A.cluster z)) (b : ℝ) : u.jet (f.peeled y b z) =
    if z.1<2 then ∑ i, multiplier i (b/y)*u.jet (f.approx z i) else 0 := by
  unfold Reading.jet peeled; split
  · exact polynomial_left (f.approx z) (hm.primary z u ‹_›) _ _ u.order
  change leftDerivs (fun _ => 0) u.dirs u.point = (0:ℝ); simpa using Work.G07.left_const (0:ℝ) u.dirs u.point
lemma peels_smooth (hy : 0<y) {t : ℝ} (ht : t∈closedTimes) (z : Clusters ι) (u : Reading G p (A.cluster z)) :
    ContDiffAt ℝ depth (fun t => u.jet (f.peeled y (encoded y t) z)) t := by
  simp_rw [hm.peels]; split_ifs
  · exact smooth_sum _ fun i _ => (time_smooth hy.ne' (positive_time ht) i).mul contDiffAt_const
  exact contDiffAt_const
lemma processed_smooth (hy : 0<y) {t : ℝ} (ht : t∈closedTimes) (i : ℕ) (u : Reading G p (A.aligned i)) :
    ContDiffAt ℝ depth (fun t => u.jet (f.processed y (encoded y t) i)) t := by
  unfold Reading.jet processed; simp_rw [polynomial_left _ (hm.secondary i u) _ _ u.order]
  exact smooth_sum _ fun i _ => (time_smooth hy.ne' (positive_time ht) i).mul contDiffAt_const
lemma fee_zero {z} (u : Reading G p (A.cluster z)) (hy : 0<y) {t : ℝ} (ht : t∈times) :
    iteratedDeriv depth (fun t => t^2*u.jet (f.peeled y (encoded y t) z)) t = 0 := by
  unfold peeled; split_ifs
  · exact killed (positive_time (Ioo_subset_Icc_self ht)) hy deep (hm.primary z u ‹_›) _ u.order
  simp [Reading.jet]
end Deficit

lemma charged {Y : ι → RegularAddress n} (ha : 0≤a) {c : ι → ℝ}
    (h : Ready (fun i => (Y i).support) p.B c (a+2) γ 1 q) {Q : Clusters ι → RegularAddress n}
    (he : ∀ i, (Q i).support = foot (fun j => (Y j).support) i) (N m : ℕ) :
    Seated Q p.B (fun z => if m ≤ z.1 then Cluster.expense p (fun j => (Y j).support) c N z else 0)
      a (Cluster.price p 1 γ q N m) := by
  apply Labels.anchor_weaker (fun i => (Q i).support) p.B (fun i => ?_) _ _ (fun i => (Q i).anchor)
  · intro x; convert Cluster.support_tail p (fun i => (show (Y i).support.Nonempty from ⟨_,(Y i).anchor⟩)) zero_lt_one ha (by simpa using h) x N m using 1
    ext i; simp only [he]; split_ifs <;> simp_all [Trees.currency]
  split; exact Cluster.expense_pos p c h.2.2.2.2.1 N i; exact le_rfl

section Retail
variable (hp : FrozenOrders f A p h y a γ q) (hm : Deficit f A p h y a M) (ha : 0 ≤ a) (hy : 0<y)
include hp hm

include ha in
theorem actual_value {t : ℝ} (ht : t∈closedTimes) : ∃ c : Bulk ι → ℝ,
    (∀ z,p.supBounds (A.regular z).site (A.regular z).support (f.logarithm A y (encoded y t) h z) (c z)) ∧
      Seated A.regular p.B c a ((M+Cluster.price p 1 γ q 0 2)+M) := by
  obtain ⟨c,hc,H⟩ := hp.raw_cost ht
  obtain ⟨d,hd,hd'⟩ := hm.low t ht; obtain ⟨v,hv,hv'⟩ := hm.high t ht
  let w (z : Clusters ι) := if 2≤z.1 then Cluster.expense p A.reads c 0 z else 0
  have hw : Seated A.cluster p.B w a (Cluster.price p 1 γ q 0 2) := charged ha hc (Y:=A.atom) (fun _ => rfl) 0 2
  refine ⟨Sum.elim (d+w) v,?_,seated_join (seated_add hd' hw) hv'⟩
  have hz z : 0 ≤ w z := by unfold w; split; exact Cluster.expense_pos p c hc.2.2.2.2.1 0 z; exact le_rfl
  rintro (z|i); swap; exact hv i
  apply (Reading.cost (r:=A.cluster z) _ (add_nonneg (hd z).1 (hz z))).mpr
  intro u
  unfold logarithm; rw [Sum.elim_inl]
  unfold tail peeled; split
  next ht => have he := (Reading.cost _ (hd z).1).mp ((hd z).2 ht) u |>.trans (le_add_of_nonneg_right (hz z)); simpa only [tail,peeled,if_pos ht] using he
  next ht => rw [sub_zero]; exact (H z u).trans ((if_pos (show 2 ≤ z.1 by omega) : w z=_).symm.le.trans (le_add_of_nonneg_left (hd z).1))

abbrev assay (f : Content G n ι κ H) (A : Placement G n ι κ) (p : BudgetPoint) (y : ℝ) (h : H) (i : Bulk ι)
    (u : Reading G p (A.regular i)) (t : ℝ) := u.jet (f.logarithm A y (encoded y t) h i)

private lemma tail_assay (z : Clusters ι) (u : Reading G p (A.cluster z)) {t : ℝ} (ht : t∈closedTimes) :
    assay f A p y h (.inl z) u t = u.jet (f.raw A (encoded y t) h z) - u.jet (f.peeled y (encoded y t) z) :=
  AnalyticBridge.VerifiedReset.left_sub (hp.raw_chart ht z u) (hm.peeled_chart z u _) u.order
include hy in
lemma assay_continuous (i : Bulk ι) (u : Reading G p (A.regular i)) : ContinuousOn (assay f A p y h i u) closedTimes := by
  rcases i with z|i
  · exact ((hp.raw_continuous z u).sub (continuousOn_of_forall_continuousAt fun t ht => (hm.peels_smooth hy ht z u).continuousAt)).congr
      fun t ht => tail_assay hp hm z u ht
  exact continuousOn_of_forall_continuousAt fun t ht => (hm.processed_smooth hy ht i u).continuousAt

set_option maxHeartbeats 600000 in
include ha hy in
lemma assay_meter {t : ℝ} (ht : t∈times) : ∃ c : Bulk ι → ℝ,
    (∀ i (u : Reading G p (A.regular i)), let F := fun t => t^2 * assay f A p y h i u t
        ContDiffAt ℝ depth (assay f A p y h i u) t ∧ |iteratedDeriv depth F t| ≤ c i) ∧
      (roots A.regular p.B a).Credits c ((2^depth * 8)*Cluster.price p 1 γ q depth 0) := by
  obtain ⟨c,hc,H⟩ := hp.raw_meter ht
  let w (z : Clusters ι) := Cluster.expense p A.reads c depth z
  let C : ℝ := (2^depth * 8)
  have hw := charged ha hc (Q:=A.cluster) (Y:=A.atom) (fun _=>rfl) depth 0
  refine ⟨Sum.elim (fun z=> C*w z) (fun _=>0),?_,seated_iff.mpr ⟨?_,?_⟩⟩
  · rintro (z|i) u F
    · let R (t : ℝ) := u.jet (f.raw A (encoded y t) h z)
      let P (t : ℝ) := u.jet (f.peeled y (encoded y t) z)
      have he : assay f A p y h (Sum.inl z) u =ᶠ[𝓝 t] R-P := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with v hv using tail_assay hp hm z u (Ioo_subset_Icc_self hv)
      have he' : F =ᶠ[𝓝 t] (fun t => t^2*R t)-(fun t=>t^2*P t) := he.mono fun x hx => by unfold F; rw [hx]; simp [mul_sub]
      have hR : ContDiffAt ℝ depth R t := (H z u).1
      have hP : ContDiffAt ℝ depth P t := hm.peels_smooth hy (Ioo_subset_Icc_self ht) z u
      have hs : ContDiffAt ℝ depth (fun t : ℝ => t^2) t := by fun_prop
      refine ⟨(hR.sub hP).congr_of_eventuallyEq he,?_⟩
      rw [he'.iteratedDeriv_eq,iteratedDeriv_sub (hs.mul hR) (hs.mul hP), show iteratedDeriv depth (fun x => x^2 * P x) t = 0 from hm.fee_zero u hy ht, sub_zero]
      exact mul_price hs hR (fun j _ => constant_square (Ioo_subset_Icc_self ht) j) (H z u).2
    exact ⟨hm.processed_smooth hy (Ioo_subset_Icc_self ht) i u, (congrArg abs (show iteratedDeriv depth F t=0 from
      killed (positive_time (Ioo_subset_Icc_self ht)) hy deep (hm.secondary i u) u.dirs u.order)).trans_le abs_zero.le⟩
  · rintro (z|i); exact mul_nonneg (by unfold C; positivity) (Cluster.expense_pos p c hc.2.2.2.2.1 _ z); exact le_rfl
  let R := Cluster.price p 1 γ q depth 0
  have hw : Seated A.cluster p.B w a R := by simp only [Nat.zero_le, if_true] at hw; exact hw
  have hv : Seated A.aligned p.B (fun _=>0) a 0 := fun i => by simp [SumBudget]
  simpa only [add_zero] using! seated_join (seated_scale hw (r:=C) (by unfold C; positivity)) hv

end Retail

private lemma interpolant (A B : ℝ) {C r y : ℝ} (_hC : 0 ≤ C) (_hr : 0<r) (hA : 0≤A) (hy : 0<y)
    {f : ℝ→ℝ} (hf : ContinuousOn f closedTimes) (he : ∀ t∈times, |f t| ≤ A)
    (hd : ∀ t∈times, ContDiffAt ℝ depth f t ∧ |iteratedDeriv depth (fun t => t^2*f t) t| ≤ B)
    (hw : ∀ u : ℝ→ℝ, (∀ t∈times, ContDiffAt ℝ depth u t ∧ |u t| ≤ 4*A ∧ |iteratedDeriv depth u t| ≤ B) →
      ∀ t∈times, |deriv u t| ≤ C*(4*A)/r + r^(depth-1)*B) {v w : ℝ} (hv : v∈ Icc (y/2) (2*y)) (hw' : w∈ Icc (y/2) (2*y)) :
    |f (decoded y v) - f (decoded y w)| ≤ |v-w|/y * (4*(C*(4*A)/r+r^(depth-1)*B+4*A)) := by
  let cost := C*(4*A)/r+r^(depth-1)*B
  have h j (hj : j∈times) := positive_time (Ioo_subset_Icc_self hj)
  have ht : ∀ t∈times, |deriv (fun t : ℝ => t^2 * f t) t| ≤ cost := hw _ (fun t ht => ⟨(by fun_prop : ContDiffAt ℝ depth (fun t : ℝ => t^2) t).mul (hd t ht).1,
    by rw [abs_mul,abs_pow]; apply mul_le_mul _ (he t ht) (abs_nonneg _) (by norm_num); rw [abs_of_pos (h t ht)]; nlinarith only [ht.2,interval_numbers.2.2,h t ht], (hd t ht).2⟩)
  have hc : 0≤cost := (abs_nonneg _).trans (ht ((upper+lower)/2) ⟨by linarith only [interval_numbers.2.1],by linarith only [interval_numbers.2.1]⟩)
  apply le_trans (interval_cost (decode hy hw').1 (decode hy hv).1 hf (M:=4*(cost+4*A)) ?_)
    (mul_le_mul_of_nonneg_right (time_dist hy hv hw') (by change 0 ≤ 4*(cost+4*A); positivity))
  intro t ht'
  have hD := (hd t ht').1.differentiableAt (Nat.cast_ne_zero.mpr (by have := deep; omega))
  refine ⟨hD,?_⟩
  have hh := ht t ht'; rw [deriv_fun_mul (by fun_prop) hD,deriv_fun_pow (by fun_prop),deriv_id'',mul_one] at hh
  have hb : |2*t*f t| ≤ 4*A := by rw [abs_mul,abs_of_pos (by positivity [h t ht'] : 0<2*t)]; exact mul_le_mul (by
    linarith only [ht'.2,interval_numbers.2.2]) (he t ht') (abs_nonneg _) (by norm_num)
  have hz : |t^2 * deriv f t| ≤ cost + 4*A := by
    norm_num only [id_eq,Nat.reduceSub,Nat.cast_ofNat,pow_one] at hh
    obtain ⟨h₁,h₂⟩ := abs_le.mp hh; obtain ⟨h₃,h₄⟩ := abs_le.mp hb; exact abs_le.mpr ⟨by linarith only [h₁,h₄],by linarith only [h₂,h₃]⟩
  rw [abs_mul,abs_of_nonneg (sq_nonneg _)] at hz
  nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) (interval_numbers.1.trans ht'.1.le) 2) (abs_nonneg (deriv f t)),hz]

def interCoeff : ℝ := Classical.choose (interpolation depth (by have := deep; omega))
lemma interCoeff_nonneg : 0≤ interCoeff := Classical.choose_spec (interpolation depth (by have := deep; omega)) |>.1

/-- Raw regular and processed-low receipts before varying incoming payload. Frozen on the *whole*
allowed incoming beta band (need not be solving outside the surviving interval). -/
theorem frozen_change : ∀ {f : Content G n ι κ H} {A : Placement G n ι κ} {p y h a γ q M},
    FrozenOrders f A p h y a γ q → Deficit f A p h y a M → 0≤a → 0<y →
    let cost := (2^depth * 8)*Cluster.price p 1 γ q depth 0
    let mass := (M+Cluster.price p 1 γ q 0 2)+M
    ∀ (r v w : ℝ), 0<r → r≤ upper-lower → v∈ Icc (y/2) (2*y) → w∈ Icc (y/2) (2*y) →
      let D := 4*(interCoeff*(4*mass)/r + r^(depth-1)*cost + 4*mass)
      (roots A.regular p.B a).Box (fun i (u : Reading G p (A.regular i)) => u.jet (f.logarithm A y v h i)-u.jet (f.logarithm A y w h i))
        (|v-w|/y * D) := by
  obtain ⟨hc,H⟩ := Classical.choose_spec (interpolation depth (by have := deep; omega))
  intro f A p y h a γ q M hp hm ha hy cost mass r v w hr hl hv hw D; refine Tax.Dual.box (fun o s u e he => ?_)
  let F := fun t => ∑ i∈s,e i * assay f A p y h i (u i) t
  have hA t (ht : t∈times) : |F t| ≤ mass := ((rooted_box _ p).2 (actual_value hp hm ha (Ioo_subset_Icc_self ht))).dual o s u e he
  have hb := (abs_nonneg _).trans (hA _ (show (upper+lower)/2 ∈ times from ⟨by linarith only [interval_numbers.2.1],by linarith only [interval_numbers.2.1]⟩))
  have hF t (ht : t∈times) : ContDiffAt ℝ depth F t ∧ |iteratedDeriv depth (fun t => t^2*F t) t| ≤ cost := by
    obtain ⟨c,h₁,h₂⟩ := assay_meter hp hm ha hy ht
    let g (t : ℝ) i (u : Reading G p (A.regular i)) := t^2*assay f A p y h i u t
    have hg : (roots A.regular p.B a).Box (fun i u => iteratedDeriv depth (fun t => g t i u) t) cost := ⟨c,h₂,fun i u => (h₁ i u).2⟩
    constructor
    · exact smooth_sum s fun i _ => contDiffAt_const.mul (h₁ i (u i)).1
    rw [show (fun t => t^2*F t) = fun t => ∑ i∈s,e i*g t i (u i) by ext; simp [F,g,mul_sum,mul_left_comm (_^2:ℝ)],
      iteratedDeriv_fun_sum (fun i _ => contDiffAt_const.mul ((by fun_prop : ContDiffAt ℝ depth (fun t : ℝ => t^2) t).mul (h₁ i (u i)).1))]
    simp_rw [iteratedDeriv_const_mul_field]; exact hg.dual o s u e he
  have hp' := interpolant _ cost hc hr hb hy (f:=F) (continuousOn_finsetSum _ fun i _ => (assay_continuous hp hm hy i (u i)).const_mul _)
    hA hF (fun _ => H hr hl) hv hw
  rw [show ∑ i∈s, e i * _ = F (decoded y v)-F (decoded y w) from ?_]; exact hp'
  unfold F assay; rw [(decode hy hv).2,(decode hy hw).2]; simp_rw [mul_sub,sum_sub_distrib]
end Content
end YM.PhysicalNext.InterpolatedSecantsFc
