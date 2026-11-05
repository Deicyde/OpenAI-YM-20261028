import YM.PhysicalNext.ORDERED_AFFINE_2B.Journeys
import YM.UVNext.FREE_STRESS_CERTIFICATE.FillingRange


/-!
# Assigned B-cover and external field income of ALL coordinates

Before integrating Z or combining log and ratio exponents. Coeffs
in ordered orientation, Issue on true window sizes, χ-free (for this
matrix-ledger part). Epochs fix L before Σ. `Hops` LIVE label range
is a priori (non-hops products identically zero), not restricted by any
realizations. Keep also pairs of positions and `watch * rail`-priced full
supports of all these live labels, both when using unshifted coefficients
and normalized directional derivatives of long chains. Full support not
less even if record evaluates to zero. No spending on field integrals from
its coordinates alone; mark tax and use across *the rest* of the history
is an obligation much stronger than this individual scalar invoice. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole.Currency
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree AnalyticBridge AnalyticBridge.Covariance Terrain
open AnalyticBridge.SectorAffine (Afford)
open Next Next.Fluctuations Next.SectorChange
open Further Further.CurvedGaussianJets Jets ChangeV Tracks MeasureTheory Set
open Push.SectorMeasure Matrix
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {c f : Side} {G : Gauge} {S : StepData c f} {x σ : ℝ} {q n d m : ℕ}
    {F : Forest S.ratio} {A : Stores S} {T : Tube G S} {k : S.Choices} {l : List (Directions G c)} {V : Config G c} {J : Tab}

def extra (q n : ℕ) : ℝ := 2^(q*n)
def priced (J : Tab) (q n : ℕ) (x : ℝ) (d : ℕ) (p : Run (Thing G f) m) := extra q n * ticket (initial G f) J.v J.K (Whole.rail x) d p
lemma priced_pos (J : Tab) (q n : ℕ) (x : ℝ) (d : ℕ) (p : Run (Thing G f) m) : 0≤priced J q n x d p :=
  mul_nonneg (by unfold extra; positivity) (envelope_ge (zero_le_one.trans J.budget) _)






lemma lower_bill (X : Support c) {M N : ℕ} (h : M ≤ N) : coverNumber N X ≤ coverNumber M X := by
  obtain ⟨D,hD,hd⟩ := coverNumber_realized M X; rw [←hd]
  apply Corona.list_cost; refine ⟨fun _ he=>Corona.halo_mono h (Finset.Subset.refl D) (hD.1 he),Corona.ship_halo N
    (fun i hi j hj=>?_ )⟩
  apply Relation.ReflTransGen.mono (r:=Corona.Touch D (M+M+1)) ?_ i j ((Corona.halo_ship _ hD.2) _ hi _ hj)
  rintro i j ⟨h₁,h₂,ht⟩; exact ⟨h₁,h₂,by omega⟩

-- label assigned covers. Short eta, W-tollLine, and D/F0
-- scalar `debit` get Halos.useBox separately (12 * radiusB x).


def sent (J : Tab) (S : StepData c f) (G : Gauge) (q n : ℕ) (σ x : ℝ) (o : Site c) (d m : ℕ) (short : Bool) := ∑ p : Run (Thing G f) m,
  let z := home S (G:=G); let b := watch*rail x; let E := priced J q n x d p
  if Hops z b p ∧ o∈dots z b p then Real.exp (σ * coverNumber (radiusB x) (dots z b p))*(if short then Real.sqrt E else E) else 0

-- payroll before multiplication by weight exponents normalized at
-- learned anchors. σ was bought before using record. `kind` = whether
-- the Q estimate asks for rooted square-root currency.
def payroll (J : Tab) (L : Side) (x σ : ℝ) (q n : ℕ) (kind : Bool) :=
  let D := impact L J.v; let amt (y : ℝ) := if kind then Real.sqrt y else y
  let v := Jets.spare J.v / (if kind then 2 else 1)
  amt (extra q n) * volumeCost watch D (radiusB x) * (mapCost v σ watch J.v.tags * amt J.K)^3 * Real.exp (-(v/400)*radiusB x)

private lemma billed (J : Tab) (L : Side) {B : ℕ} (hs : 0≤σ) {R K : ℝ} (hr : 0<R) (hk : 1≤K) (hb : 120≤B) :
    paidHits L J.v R σ K watch (B/100) d ≤ volumeCost watch (impact L J.v) B *
      (mapCost R σ watch J.v.tags*K)^3 * Real.exp (-(R/400)*B) * ((1/2:ℝ)^d) := by
  have he : (B:ℝ) ≤ 200*((B/100:ℕ):ℝ) := by exact_mod_cast (show B ≤200*(B/100) by omega)
  have hm := map_ge (m:=watch) (L:=J.v.tags) hs hr
  have hv : 0≤volumeCost watch (impact L J.v) B := by unfold volumeCost; positivity
  unfold paidHits
  gcongr (?_ * _ * Real.exp ?_ * _)
  · unfold volumeCost; gcongr <;> omega
  have h := mul_le_mul_of_nonneg_left he hr.le; linarith only [h]

lemma income (h : J.Ships q n σ T F A k x V) (hs : 0≤σ) (o : Site c) {m d : ℕ} (hm : m ≤ d+2) (kind : Bool) :
    0 ≤ sent J S G q n σ x o d m kind ∧ sent J S G q n σ x o d m kind ≤ payroll J S.patch.L x σ q n kind * ((1/2:ℝ)^d) := by
  constructor
  · apply Finset.sum_nonneg; intro i hi; dsimp only; split_ifs
    · positivity
    · exact mul_nonneg (Real.exp_pos _).le (priced_pos ..)
    rfl
  let p := home S (G:=G); let N := Whole.rail x
  let u (E : ℝ) := if kind then Real.sqrt E else E
  let v := Jets.spare J.v / (if kind then 2 else 1)
  let E := ticket (initial G f) J.v J.K N d (m:=m)
  have he : ∀ i,0 ≤ E i := envelope_ge (zero_le_one.trans J.budget)
  have hv : 0<v := by have := spare_pos J.v; unfold v; split_ifs <;> positivity
  have hp {x : ℝ} (hx : 0≤x) : 0 ≤ u x := by unfold u; split <;> first | exact Real.sqrt_nonneg _ | exact hx
  have hK : 1≤u J.K := by unfold u; split; exact Real.one_le_sqrt.mpr J.budget; exact J.budget
  have hB (i : Run (Thing G f) m) : u (priced J q n x d i) = u (extra q n) * u (E i) := by
    unfold u E priced; split; exact Real.sqrt_mul (by unfold extra; positivity) _; rfl
  have H : sent J S G q n σ x o d m kind ≤ meter p σ watch N o (fun i=> u (extra q n)*u (E i)) := by
    refine Finset.sum_le_sum (fun i _=>?_); dsimp only; rw [show u (extra q n)*u (E i)=_ from (hB i).symm]; unfold N p u; split_ifs
    · apply mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ hs)) (Real.sqrt_nonneg _)
      exact_mod_cast lower_bill _ (show N ≤ radiusB x by unfold N Whole.rail; omega)
    · apply mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ hs)) (priced_pos ..)
      exact_mod_cast lower_bill _ (show N ≤ radiusB x by unfold N Whole.rail; omega)
    rfl
  have hy : meter p σ watch N o (fun i=>u (E i)) ≤ paidHits S.ratio.count J.v v σ (u J.K) watch N d := by
    unfold u v; split_ifs; exact h.riders.half d m hm o; rw [div_one]; exact h.riders.hit d m hm o
  rw [meter_mul] at H
  exact H.trans ((mul_le_mul_of_nonneg_left (hy.trans (billed J S.ratio.count hs hv hK h.tall)) (hp (by unfold extra; positivity))).trans_eq (by unfold payroll; dsimp only; simp_rw [←mul_assoc]; rfl))

lemma notes (h : J.Ships q n σ T F A k x V) (hs : 0≤σ) (o : Site c) (kind : Bool) {j : ℕ} (hj : j ≤ 2) : let f d := sent J S G q n σ x o d (d+j) kind
    Summable f ∧ ∑' d,f d ≤ payroll J S.patch.L x σ q n kind * 2 := by
  intro f; have he d := income h hs o (m:=d+j) (d:=d) (by omega) kind
  have hp := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left (payroll J S.patch.L x σ q n kind)
  have hh := hp.summable.of_nonneg_of_le (fun d => (he d).1) (fun d=> (he d).2)
  exact ⟨hh, (hh.tsum_le_tsum (fun d=>(he d).2) hp.summable).trans_eq (hp.tsum_eq.trans (by ring))⟩
end YM.PhysicalNext.OrderedAffine2B.Whole.Currency
