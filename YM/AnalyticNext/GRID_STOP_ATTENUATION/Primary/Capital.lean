import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Ballast
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Folio
import YM.Next.MULTISOURCE.Ledger

set_option warningAsError false

/-!
# Budget the complete ray parse at the actual rep
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Primary
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Finset
open Multi.Couples Pair
open Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {m p d N : ℕ} {o : SiteSpace C m p} {r κ b μ : ℝ}
    {Z : Config G (C.side m p)→ℂ}
    (Y : Folio C o Z d r b) (P : Rep G (C.side m p)) (hr : 0 ≤ r) (hP : P.p=C.path.levels.budget m)

def fence (C : Family G) {m p} (o : SiteSpace C m p) (d : ℕ) (r : ℝ) := burn (C.path.levels.budget m) (r+2) ((C.localSection d).footprint o)

include hr
lemma meter (h : C.Makes) (i) : burn (C.path.levels.budget m) (r+2) (patch Y i) ≤
    fence C o d r * burn (C.path.levels.budget m) (r+2) (Y.zone i) := by
  let S := C.localSection d
  have ho : o∈S.footprint o := mem_image.mpr ⟨0,(h.sections _).anchored,by simp⟩
  unfold patch unionMap fence burn; rw [← Real.exp_add]
  let a := C.path.levels.budget m
  change _ ≤ Real.exp ((a.supportExponent+(r+2))*(coverNumber a.B _)+(a.supportExponent+(r+2))*_)
  rw [← mul_add,add_comm (a:=((coverNumber a.B _):ℝ))]
  apply Real.exp_monotone (mul_le_mul_of_nonneg_left _ (add_nonneg a.exponent_pos.le (by linarith)))
  exact_mod_cast Corona.meets_sum (Y.anchored i) ho a.B

include hP
lemma rem_budget (h : C.Makes) :
    let u := wage C d m
    SumBudget (fun i => burn P.p (r+2) (patch Y i) * (u*Y.fee i)) (u*fence C o d r*b) := by
  rw [hP]; intro u
  let p := C.path.levels.budget m
  have hw := zero_le_one.trans (wage_one C d m)
  have ht : 0 ≤ u*fence C o d r := mul_nonneg hw (burn_pos ..).le
  refine permit_le (permit_mul Y.finiteFee ht) le_rfl fun i => ?_
  have he (i) := Y.pay i
  refine ⟨mul_nonneg (burn_pos ..).le (mul_nonneg hw (he _)),?_⟩
  exact (mul_le_mul_of_nonneg_right (meter Y hr h i) (mul_nonneg hw (he _))).trans_eq (by ring)

-- complete holes through the Pack branch
def corrections (i) := ballast (patch Y i) P (hole Y i)
def investments := fun q U => ∑' i,corrections Y P i q U

def endowment (C : Family G) {m p} (o : SiteSpace C m p) (d : ℕ) (r : ℝ) := cells (C.path.levels.budget m)*4*wage C d m*fence C o d r
omit hr hP in
lemma endowment_price {o : SiteSpace C m p} : 0 ≤ endowment C o d r :=
    mul_nonneg (mul_nonneg (by unfold cells; positivity) (zero_le_one.trans (wage_one ..))) (burn_pos ..).le

structure Priced (κ : ℝ) where
  fee : ℕ → Pack (C.side m p) → ℝ
  legal i q : Legible P.p q (corrections Y P i q) ∧ (corrections Y P i q ≠ 0 → patch Y i ⊆ q.zone) ∧
    0 ≤ fee i q ∧ ∀ U, ‖corrections Y P i q U‖ ≤ fee i q
  total : SumBudget (fun i => ∑ q,burn P.p r q.zone*fee i q) (κ*(endowment C o d r * b))

lemma premium (h : C.Makes) (he : Mint P r μ) (hm : cells P.p*μ ≤ 1) (hκ : μ ≤ κ)
    {τ w : ℝ} (hV : P.activities.Valid P.p τ w) : Nonempty (Priced Y P κ) := by
  have hl (i) : Weight P.p (patch Y i) (hole Y i) := hP.symm ▸ (Y.path i).2.2.2.2.2.1
  let a := wage C d m
  have ha : 0 ≤ a := zero_le_one.trans (wage_one ..)
  have hx (i) : 0 ≤ 4*a*Y.fee i := mul_nonneg (mul_nonneg (by norm_num) ha) (Y.pay _)
  choose f hv hf using fun i => invoice P (patch Y i) (hole Y i) (hl i) hV hκ hm hr he (hx i) ((Y.path i).2.2.2.2.2.2)
  obtain ⟨j,hj,hj'⟩ := he
  let x : SiteSpace C m p := 0
  have hQ : 0 ≤ κ := le_trans ((sum_nonneg (fun i _ => mul_nonneg (burn_pos ..).le (hj i).1)).trans (hj' x)) hκ
  have hb : 0 ≤ κ*cells P.p*4 := by unfold cells; positivity
  have ht := permit_mul (rem_budget Y P hr hP h) hb
  refine ⟨⟨f,hf, permit_le ht (by unfold endowment; rw [hP]; apply le_of_eq; ring) ?_⟩⟩
  intro i
  refine ⟨sum_nonneg fun q _ => mul_nonneg (burn_pos ..).le (hf _ q).2.2.1,(hv i).trans_eq ?_⟩
  unfold a; ring

omit hP in
lemma annuity (F : Priced Y P κ) (q : Pack (C.side m p)) : Summable (fun i => F.fee i q) := by
  refine F.total.2.1.of_nonneg_of_le (fun i => (F.legal i q).2.2.1) fun i => le_trans (b:=burn P.p r q.zone*F.fee i q)
    (le_mul_of_one_le_left ((F.legal i q).2.2.1) (burn_ge _ hr _)) ?_
  exact single_le_sum (f:=fun j : Pack (C.side m p) => burn P.p r j.zone*F.fee i j)
    (fun i _ => mul_nonneg (burn_pos ..).le (F.legal _ _).2.2.1) (mem_univ q)

omit hP in
theorem assigned (F : Priced Y P κ) :
    (∑ q,burn P.p r q.zone*(∑' i,F.fee i q)) ≤ κ*(endowment C o d r * b) ∧
    ∀ q,Legible P.p q (investments Y P q) ∧ (investments Y P q ≠ 0 → o∈q.zone) ∧
      0 ≤ ∑' i,F.fee i q ∧ ∀ U, ‖investments Y P q U‖ ≤ ∑' i,F.fee i q := by
  constructor
  · simp_rw [← tsum_mul_left, ← Summable.tsum_finsetSum (f:=fun q : Pack (C.side m p) => fun i => burn P.p r q.zone*F.fee i q) (s:=univ) (by intro q hq; exact (annuity Y P hr F q).mul_left _)]
    exact F.total.2.2
  intro q
  refine ⟨Multi.Desk.joined P.p q _ (fun _ => (F.legal _ _).1),fun hi => ?_,tsum_nonneg (fun _ => (F.legal _ _).2.2.1),fun U => ?_⟩
  · by_contra he
    apply hi; funext U; refine (tsum_congr (g:=fun _ => 0) (fun i => congr_fun (f:=corrections Y P i q) (g:=0) ?_ U)).trans tsum_zero
    exact not_not.mp fun ht : corrections Y P i q ≠ 0 => he ((F.legal i q).2.1 ht (mem_union_left _ (Y.anchored i)))
  have he i := (F.legal i q).2.2.2 U
  obtain hv := (annuity Y P hr F _).of_nonneg_of_le (fun i => norm_nonneg _) he
  exact (norm_tsum_le_tsum_norm hv).trans (hv.tsum_le_tsum he (annuity Y P hr F _))

/-- Tangents through the complete series (actual unmarked partners) -/
theorem credited (F : Priced Y P κ) (U : Config G (C.side m p)) {τ w : ℝ} (hV : P.activities.Valid P.p τ w) :
    tangent P (0,investments Y P) U=(P.eval U:ℂ)*∑' i,hole Y i U := by
  have hs i : tangent P (0,corrections Y P i) U=(P.eval U:ℂ)*hole Y i U :=
    rough P (patch Y i) _ U (hP.symm ▸ (Y.path _).2.2.2.2.2.1) hV
  rw [←tsum_mul_left]; simp_rw [← hs]; unfold tangent
  simp only [Pi.zero_apply,mul_zero, zero_add,tsum_mul_left]
  congr 1
  unfold investments; simp_rw [← tsum_mul_right]
  have he q : Summable (fun i => corrections Y P i q U) := Summable.of_norm_bounded (annuity Y P hr F q) (fun i => (F.legal _ _).2.2.2 _)
  let g (j : Finset (Pack (C.side m p))) (l) (i : ℕ) := corrections Y P i l U * ∏ v ∈ j.erase l, incumbent P U v
  have ht j l : Summable (g j l) := (he _).mul_right _
  have hg j : Summable (fun i => ∑ l∈j,g j l i) := summable_sum (s:=j) (fun l _ => ht j l)
  change (∑ j∈ _,∑ l∈ j,∑' (i:ℕ),g j l i)=(∑' i,∑ j∈ _,∑ l∈j,g j l i)
  rw [Summable.tsum_finsetSum (f:=fun j i => ∑ l∈j,g j l i) (fun i _ => hg i)]
  exact sum_congr rfl fun i _ => (Summable.tsum_finsetSum (fun l _ => ht i l)).symm

end YM.AnalyticNext.GridStop.Primary
