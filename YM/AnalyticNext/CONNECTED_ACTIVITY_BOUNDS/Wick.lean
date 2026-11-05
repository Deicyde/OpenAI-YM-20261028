import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hair

/-!
# Analytic atom parents, all paths

E atoms of Bel. Here treated still as REAL hard weights, supported
on every mask query. No excursion to V-germ necessary for these fees.
Uses `Faces` lengths, TRULY native so pays even when jumping the same
identification repeatedly. Bounds use same T, overlap with all θ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Calls
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

abbrev Lamps (n : Side) := Signed × (Site n × ℕ)
section paths
variable {k : ℕ} (R : ℕ → Atom G k) (m : BudgetPoint) (γ : ℝ)  -- coefficient indicates weight incl β

def attached (S : StepData c f) (p : Lamps f) : Support c :=
    (priorE S ((R p.2.2).footprint p.2.1)).image p.1.act

def article (S : StepData c f) (x : ℝ) (p : Lamps f) := Calls.extent 120 (attached R S p) x

def axisFee (Y : Mint T F A x) (p : Lamps f) (a : ArrayR G f) :=
    - γ*guards Y (attached R S p) a*(R p.2.2).placed m (pull p.1 0 (Y.build a)) p.2.1

def atomic (Y : Mint T F A x) (p : Lamps f) (a : ArrayR G f) := Real.exp (axisFee R m γ Y p a)-1

def reserveLamp (_S : StepData c f) (p : Lamps f) := without
    (Real.exp 1*(|γ| *m.threshold^k * (R p.2.2).magnitude)) (Vars G f)

lemma holds_lamp (v : ℕ) : 0 ≤ Real.exp 1*(|γ| *m.threshold^k*(R v).magnitude) := by
  have ht := m.threshold_pos; have hp : 0≤(R v).magnitude := by unfold Atom.magnitude; positivity
  positivity

lemma atomic_cost (Y : Mint T F A x) (p : Lamps f) (a : ArrayR G f) (z : ArrayR G f)
    (h : |γ| *m.threshold^k * (R p.2.2).magnitude ≤ 1) : (reserveLamp R m γ S p).Sound ∧
    ‖atomic R m γ Y p a‖ ≤ Ticket (reserveLamp R m γ S p) z := by
  unfold reserveLamp
  rw [door]; let v := (|γ| *m.threshold^k * (R p.2.2).magnitude)
  have hx := holds_lamp R m γ p.2.2; change 0 ≤ Real.exp 1 * v at hx
  have hv : 0 ≤ v := nonneg_of_mul_nonneg_right hx (Real.exp_pos _)
  have hh := healthy_atom (R p.2.2) m (pull p.1 0 (Y.build a)) p.2.1
  have he : |axisFee R m γ Y p a| ≤ v := by
    unfold axisFee; rw [mul_assoc,abs_mul,abs_mul,abs_neg]
    apply le_trans (mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_left (abs_nonneg _) (robe_le Y _ a)).trans hh) (abs_nonneg _)); unfold v; exact le_of_eq (by ring)
  exact ⟨zero_spend hx _, (exp_bound he).trans ((mul_le_mul_of_nonneg_left (Real.exp_monotone h) hv).trans_eq (mul_comm ..))⟩
lemma included (D : Patch) (p : BudgetPoint) (A : ℝ) (x : ℝ) {σ ε Γ : ℝ} (S : StepData c f) (_hS : S.patch=D)
    (γ : ℝ) (h : SumBudget (fun i => (R i).budget σ) Γ) (hσ : 0<σ) (hy : 0<radiusB x) (hP : reserve σ A
      (Paths.legFee S.ratio 125 (radiusB x)) ε) (t : Till) : Ac.Hit (article R S x) (radiusB x)
    (fun i => t.sale (reserveLamp R p γ S i)) A ((Fintype.card Signed:ℝ)*payment (S.ratio.count.val^4)
      (Paths.originFee 125 (radiusB x)) 0 ε (Real.exp 1*(|γ| *p.threshold^k)) Γ A (Paths.baseFee (d:=k) S.ratio 125)) := by
  apply many; intro j
  let b i := t.sale (reserveLamp R p γ S (j,i)); let B := radiusB x; let Y (i : Site f × ℕ) := costE S x ((R i.2).footprint i.1)
  have he i : (Y i).image j.act = article R S x (j,i) := by
    let X := priorE S ((R i.2).footprint i.1)
    ext z; rw [Finset.mem_image,article, extent, halo_spec]
    constructor
    · rintro ⟨v,hv,rfl⟩
      obtain ⟨r,hr,h⟩ := halo_spec.mp hv
      exact ⟨_, Finset.mem_image_of_mem j.act hr,(separation_signed ..).trans_le h⟩
    rintro ⟨v,hv,hk⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨v,rfl⟩ := (show Surjective (j.act (R:=Per c)) from j.actEquiv.surjective) z
    rw [separation_signed] at hk; exact ⟨v, halo_spec.mpr ⟨_,hq,hk⟩,rfl⟩
  have hp' i : 0 ≤ b i := sale_nn t (zero_spend (holds_lamp R p γ _) _)
  change Ac.Hit (fun i => article R S x (j,i)) B b A _; simp_rw [← he]
  apply forged j Y B b A _ hp' hP.1
  have hm : 0 ≤ Real.exp 1*(|γ| *p.threshold^k) := by have ht := p.threshold_pos; positivity
  intro z; let w (i : ℕ) := (R i).magnitude
  have hp := Paths.bundle_hit S.ratio 125 B (fun i => (R i).leg) w hσ (fun i => by unfold w Atom.magnitude; positivity) h Y
    (fun i => Paths.atom_foot i.1 (R i.2) ▸ inspected_price S.ratio 120 B _ hy) hy hm hP 0 b hp' ?_ 0 z
  · simpa only [Nat.zero_le,if_true,pow_zero,mul_one] using hp
  intro i; rw [pow_zero,mul_one]; unfold b reserveLamp
  rw [sway]; exact le_of_eq (by unfold w; ring)
end paths

-- post band, issued for k then ask at k=2,3,4
lemma priced (G : Gauge) (D : Patch) (k : ℕ) (A σ r s : ℝ) (ha : 0≤A) (hc : 0<σ) (hr : 0<r) (hp : s<r) :
    ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (p : BudgetPoint) (T : Tube G S) (t : Till) (R : ℕ → Atom G k) (γ Γ : ℝ),
    S.patch=D → SumBudget (fun i => (R i).budget σ) Γ → (|γ| * p.threshold^k) * Γ ≤ amend G D x r →
      (∀ (F : Forest S.ratio) (A : Stores S) (Y : Mint T F A x) (i : Lamps f) (a z : ArrayR G f),
        (reserveLamp R p γ S i).Sound ∧ ‖atomic R p γ Y i a‖ ≤ Ticket (reserveLamp R p γ S i) z) ∧
          Ac.Hit (article R S x) (radiusB x) (fun i => sale t (reserveLamp R p γ S i)) A ((Fintype.card Signed:ℝ)*amend G D x s) := by
  let b := preCost 125 *10 / D.L.val
  let M := preCost 125+b*(1+k)
  have hx : 0 ≤ M := by unfold M b preCost; positivity
  let ε := σ/4; have he : 0< ε := by unfold ε; positivity
  filter_upwards [Fees.horizons G D.L 125 he ha (by unfold ε; linarith : 2*ε<σ),
    (Work.E09.betaF_growth G D.L).eventually_ge_atTop 1, award G D (D.L.val^4) 126 (Real.exp 1)
      A ε r s M he (Real.exp_pos _).le hp hx]
    with x hx hv hh c f S p T t R γ Γ hS h hj
  have ht := p.threshold_pos
  have hq : 0 ≤ Γ := budget_nonneg h
  constructor
  · intro F C Y i a z; apply atomic_cost R p γ Y i a z
    have hk := (R i.2.2).lower_budget σ hc; apply (mul_le_mul_of_nonneg_left (hk.trans (budget_single h _))
      (show 0 ≤ |γ| * p.threshold^k by positivity)).trans (hj.trans _)
    exact Real.rpow_le_one_of_one_le_of_nonpos hv (by linarith)
  intro y
  have hl : S.ratio.count=D.L := congr_arg Patch.L hS
  have hz := included R D p A x S hS γ h hc hx.1 (hx.2.2 c f _ hl) t y
  have hp : Paths.baseFee (d:=k) S.ratio 125=M := by unfold Paths.baseFee conversion M b; rw [hl]; ring
  refine budget_loosen hz (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  rw [hp,hl]; apply hh _ (by unfold Paths.originFee; omega) _ _ (by positivity) hq
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le
end YM.AnalyticNext.ConnectedActivity.Calls
