import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Survey
import YM.Extra.WILSON_STARTUP.SourceInk
import YM.Next.MULTISOURCE.Grades
import YM.Next.MULTISOURCE.Journey
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Native
import YM.Progress.STATIONARY_SCENES.Dispatch
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Empirical
import YM.Push.LOCAL_SPLITTING.Delay
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Extras
import YM.SectorNext.VACUUM_NORMALIZATION.Thermal
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Band



/-! # Uniform actual per-jump receipts for the Lease (SectorChange endpoint windows)

At correct flags, held fixed throughout every jet. Offset.residual uses the
smooth branch supplied in the sector estimates, including on equality. No jets
of `physical` with a moving clamped branch. The η and jump bills are uniform
in the *ringed* colors and referred to the very same `meanLog`/`fog` when used
in the density; NOT using an $A_{flat}$ weight as the actual background. Apply
to betaHat + the in-band input beta; aperture B and Chi must be purchased before
this height. Linear amplitude includes the normalized $g^{-1}$. Rank k is a
TOTAL order when these tickets are subsequently applied to words.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.SectorAffine
open Push.SectorMeasure Wisps
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

structure Charges where
  /-- Exponential displacement (on coarse native separation). -/
  speed : ℝ
  /-- Smallness cost for at least one use of a window error OR the linear price. -/
  delay : ℝ
  price : ℝ
  live : 0 < speed
  time_pos : 0 < delay
  paid : 1 ≤ price

variable {G : Gauge} {c f : Side} {S : StepData c f} {k P : ℕ}

abbrev gramAt (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (l : S.Choices) (V : Config G c) :=
  Rows.gram T x V l (shots S x) A F

def defect (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (l : S.Choices) (V : Config G c) :=
  gramAt T x A F l V * fog A F T x V l - 1

def headwind (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (l : S.Choices)
    (q : Chi) (r g : ℝ) (Y : LinkArray G (Frozen A x F)) (V : Config G c) := -g⁻¹ • Offset.residual T x l A F q r Y V

def Charges.levy (v : Charges) (x : ℝ) := rate (-v.delay) (radiusB x)
lemma Charges.levy_pos (v : Charges) (x : ℝ) : 0<v.levy x := rate_pos ..

def Charges.ordinary (v : Charges) (a b : Site c) := v.price * rate (-v.speed) (separation a b)

structure Value (v : Charges) (x r : ℝ) (T : Tube G S) (A : Stores S) (F : Forest S.ratio)
    (l : S.Choices) (V : Config G c) (bp : BudgetPoint) (k : ℕ) (q : Chi) (g : ℝ) : Prop where
  g_pos : 0 < g
  otb : (gramAt T x A F l V).PosDef
  pane : (fog A F T x V l).PosDef
  source (Y) : Offset.mean T x l A F q r Y V = meanLog A F T x V l q r Y ∧
    headwind T x A F l q r g Y V = Rows.eta T x V l (shots S x) A F q r Y (meanLog A F T x V l q r Y) g
  entries (o : Site c) (i j : In (G:=G) x A F) :
    let ti := grade (bp.power*k) o (front A F i); let M := v.ordinary (front A F i) (front A F j)
    Ticket (bp.dirBound o) k V M ti (fun w => gramAt T x A F l w i j) ∧
      Ticket (bp.dirBound o) k V (v.levy x*M) ti (fun w => defect T x A F l w i j)
  moving (o : Site c) (i : In (G:=G) x A F) (Y) :
    let ti := grade (bp.power*k) o (front A F i)
    Ticket (bp.dirBound o) k V (v.price * fiery G x S.patch.L) ti (fun w => Offset.mean T x l A F q r Y w i) ∧
      Ticket (bp.dirBound o) k V (v.levy x * v.price) ti (fun w => headwind T x A F l q r g Y w i)

private lemma subsidy (G : Gauge) (L : Side) {s : ℝ} (hs : 0<s) :
    ∀ᶠ x : ℝ in atTop, ∀ β : ℝ, 0<β → β≤2*betaF G x L →
    (coupling β)⁻¹ * (fiery G x L * rate (-s) (radiusB x)) ≤ rate (-(s/240)) (radiusB x) := by
  filter_upwards [SectorTools.PhysicalGaussianInsertion.Physical.load_limit G L zero_le_one zero_lt_one hs zero_le_one,
    (Work.E09.betaF_growth G L).eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hy hv
  intro β hb hu
  set t := fiery G x L
  have ht : 0<t := Work.E09.temp_pos hy
  apply le_trans ?_ (hx β t hb hu ht (by rw [one_mul])).2
  simp only [SectorTools.PhysicalGaussianInsertion.Physical.load, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr (coupling_pos hb)).le
  rw [mul_comm (Real.exp _)]
  exact mul_le_mul (le_add_of_nonneg_left (Work.E09.temp_pos hv).le) (Real.exp_monotone
    (mul_le_mul_of_nonpos_left (by exact_mod_cast Nat.div_le_self ..) (neg_nonpos.mpr hs.le))) (rate_pos ..).le
    (add_nonneg (Work.E09.temp_pos hv).le ht.le)

theorem capital (G : Gauge) (H : Patch) (Q : Teller G) (hH : H.Branches Q.bind G) (B : ℝ) (hB : 0<B)
    (q : Chi) (k p : ℕ) : ∃ v : Charges, ∀ᶠ x : ℝ in atTop, ∀ β : ℝ, 0<β → β ≤ 2*betaF G x H.L →
      ∀ (bp : BudgetPoint), bp.power=p → bp.threshold=temp x → ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=H →
      100*(1+radiusB x) ≤ c.val → Q.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c),
      A.flags=RG.flags (temp x) V → ∀ l : S.Choices,
        Value v x (B*fiery G x H.L) T A F l V bp k q (coupling β) := by
  obtain ⟨r,d,d',s,M,N,η,u,hr,hd,hd',hs,hM,hN,hη,hu,h⟩ := Offset.prices G H Q B hB q k hH
  let C := activation G k (p*k) d * M
  let C' := activation G k (p*k) d' * N
  have hc : 0 ≤ C := mul_nonneg (zero_le_one.trans (activation_one G k (p*k) hd)) hM.le
  have hc' : 0 ≤ C' := mul_nonneg (zero_le_one.trans (activation_one G k (p*k) hd')) hN.le
  let pen := lieCost G k
  let v : Charges := ⟨d',s/240,max 1 (pen*(C+C')),hd',by positivity,le_max_left ..⟩
  have hP := lieCost_nn G k
  have hMc : pen * C ≤ v.price := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hc') hP).trans (le_max_right ..)
  have hMc' : pen * C' ≤ v.price := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hc) hP).trans (le_max_right ..)
  refine ⟨v,?_⟩
  filter_upwards [h, subsidy G H.L hs] with x hx hx'
  intro β hb hy bp hbp ht c f S T hS hR hQ A F V hV l
  obtain ⟨he,h⟩ := hx.2 S T hS hR hQ A F V hV l
  have hL := he 0 (by simpa using hr.le)
  have hW := hL.toKernelJets.price_bounds hd'.le hη hu
  obtain ⟨-,h1,-,h2,-⟩ := hL.directions (p*k) hd' hN.le
  let i := front A F (G:=G) (x:=x)
  have h0 : 0 < temp x := ht ▸ bp.threshold_pos
  have h01 : temp x ≤ 1 := ht ▸ bp.threshold_le
  let ε := rate (-s) (radiusB x)
  have hA := matrixCoupon (Q:=gramAt T x A F l) (p:=i) h1 (t:=temp x)
  have hE := matrixCoupon (Q:=defect T x A F l) (p:=i) h2 (t:=temp x)
  have hg := coupling_pos hb
  have hf : field (G:=G) V 0 = V := field_zero V
  change SlicePrice (gramAt T x A F l (field V 0)) η N ∧ SlicePrice (fog A F T x (field V 0) l) u N at hW
  rw [hf] at hW
  rw [← hS]
  refine ⟨hg, hW.1.pos, hW.2.pos, fun Y => ?_,fun o i' j' => ?_,fun o i' Y => ?_⟩
  · obtain ⟨-,h,h'⟩ := Offset.reads_actual T x l A F q _ Y V (congr_fun h.okay Y)
    exact ⟨h, (h ▸ h' (coupling β)).symm⟩
  · subst p
    have hε : ε ≤ v.levy x := by
      unfold ε Charges.levy; exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by change -s≤-(s/240); linarith) (by positivity))
    have hb := hA i' j' h0 h01 hc'
    have he := hE i' j' h0 h01 (show 0≤C'*ε from mul_nonneg hc' (rate_pos ..).le)
    let a := rate (-d') (separation (i i') (i j'))
    have ha : 0≤a := (rate_pos ..).le
    refine ⟨(hb.ticket (bp:=bp) o ht (mul_nonneg hc' ha)).mono ?_ le_rfl,
      (he.ticket (bp:=bp) o ht (show 0 ≤ C'*ε*a from mul_nonneg (mul_nonneg hc' (rate_pos ..).le) ha)).mono ?_ le_rfl⟩
    · change pen*(C'*a) ≤ v.price*a
      rw [← mul_assoc]; gcongr
    · change pen*(C'*ε*a) ≤ v.levy x*(v.price*a)
      calc
        _ = ε*(pen*C'*a) := by ring
        _ ≤ _ := mul_le_mul hε (mul_le_mul_of_nonneg_right hMc' ha) (mul_nonneg (mul_nonneg hP hc') ha) (v.levy_pos x).le
  · subst p
    obtain ⟨-, -, -,h1,h2⟩ := h.stipulated hd hM.le h0 _ Y
    let t := fiery G x S.patch.L
    have hT : 0 ≤ t := by unfold t fiery temp; positivity
    have h3 := (pointCoupon h1 i').ticket (bp:=bp) o ht (show 0≤C*t from mul_nonneg hc hT)
    have h4 := (pointCoupon h2 i').ticket (bp:=bp) o ht (show 0≤C*t*ε from mul_nonneg (mul_nonneg hc hT) (rate_pos ..).le)
    refine ⟨h3.mono ((le_of_eq (mul_assoc pen C t).symm).trans (mul_le_mul_of_nonneg_right hMc hT)) le_rfl,
      (h4.indiv (-(coupling β)⁻¹)).mono ?_ le_rfl⟩
    rw [norm_neg,Real.norm_of_nonneg (inv_pos.mpr hg).le]
    have he := hx' β hb hy; rw [← hS] at he
    change _ ≤ v.levy x * v.price
    calc
      (coupling β)⁻¹ * (pen*(C*t*ε)) = ((coupling β)⁻¹ * (t*ε))*(pen*C) := by ring
      _ ≤ _ := mul_le_mul he hMc (mul_nonneg hP hc) (v.levy_pos x).le
end YM.PhysicalNext.JointLoad
