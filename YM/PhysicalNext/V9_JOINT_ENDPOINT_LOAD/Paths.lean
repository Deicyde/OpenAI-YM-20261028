import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Weather
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Entries
import YM.Next.MAXWELL.Silt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Costs
import YM.Progress.JOINT_CALENDAR.Branches
import YM.Push.RELAY_DIFFERENCE.Attaching



/-!
# Full ordered-path root payments

Counts at a physical *Z* coordinate; no estimate of the support size or
of read locality by counting just these endpoints! Complete tag, field,
likelihood, path and matrix data must still be retained to realize these
receipts. Real block coefficients will have the colors summed INSIDE the
log exponent. The counting in the rate conservatively retains their cost
at every step of the underlying walk. Ordered jumps and terminal entry
can return to exactly the same bond, in any positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Matrix Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian
open Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism
open Push.SectorMeasure Wisps Schur
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

/-- Names used for payment. I = accessible endpoints, J = FULL physical
intermediate position set (may not be one of the exhibited Z reads).
One terminal Gram jump, in addition to `n+1` jumps of `-S`.
-/
abbrev Tracks (J : Type) (n : ℕ) := Fin (n+1) → J
abbrev Bends (I J : Type) (n : ℕ) := (I × I) × Tracks J n
abbrev Position (I J : Type) := I ⊕ (Σ n, Bends I J n)
abbrev Full (I : Type) := Position I I

def legs {I J : Type} (p : Position I J) := p.elim (fun i => (i,i)) (fun y => y.2.1)

variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] {c f : Side} {S : StepData c f}
    {A : Stores S} {F : Forest S.ratio} {H : Patch}

abbrev site {x : ℝ} (i : Active A x F) := S.ratio.parent i.val.val.1

-- count INCLUDING bond orientations/projection multiplicity, torus uniform
private lemma sitePrice (s : ℝ) (hs : 0<s) (hH : S.patch=H) (o : Site c) (x : ℝ) :
    (∑ i : Active A x F, rate (-s) (separation o (site i))) ≤ Breeze.storm H s := by
  let R z := rate (-s) (separation o z); let e (i : Active A x F) := i.val.val
  have he : Injective e := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hsite : Fintype.card (Site S.patch.L)=Fintype.card (Site H.L) := by rw [hH]
  have ho : ∑ z,R z ≤ Tier.wealth s := by unfold R; simp_rw [separation_comm o]; exact Tier.land hs o
  calc
    _ ≤ ∑ j : Bond f,R (S.ratio.parent j.1) := by
      rw [← Finset.sum_image (g:=e) (s:=Finset.univ) (f:=fun j : Bond f => R (S.ratio.parent j.1)) he.injOn]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (rate_pos ..).le)
    _ = (Fintype.card Axis:ℝ)*((Fintype.card (Site H.L):ℝ)*∑ z,R z) := by
      rw [Fintype.sum_prod_type]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,
        Work.F01.sum_parent S.ratio R]; rw [← hsite]; rfl
    _ ≤ _ := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ho (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans_eq
      (by unfold Breeze.storm; ring)

omit [Fintype I] [DecidableEq I] in
lemma tread_pos {X Y : Wall I} (hX : ∀ i j, 0<X i j) (hY : ∀ i j, 0<Y i j) (m : ℕ) (i : I) (h : Fin m → I) (j : I) :
    0 < Trail.tread X Y m i h j := by
  induction m generalizing i with
  | zero => exact hY i j
  | succ n ih => exact mul_pos (hX i (h 0)) (ih ..)

private lemma drives {X Y : Wall I} {h : I → Site c} {u v : ℝ} (hX : Pours X h h 0 u) (hY : Pours Y h h 0 v)
    (n : ℕ) : Pours (X^n * Y) h h 0 (u^n * v) := by
  induction n with
  | zero => simpa using hY
  | succ n ih => rw [pow_succ' X,pow_succ' u,mul_assoc,mul_assoc]; exact hX.fuse ih le_rfl

private lemma bendHit {X Y : Wall I} {h : I → Site c} {u v : ℝ} (hX : Pours X h h 0 u) (hY : Pours Y h h 0 v)
    (h1 : ∀ i j, 0 < X i j) (h2 : ∀ i j, 0 < Y i j) (n : ℕ) (i : I) :
    let f (a : Bends I I n) := Trail.tread X Y (n+1) a.1.1 a.2 a.1.2
    (∑ j : Bends I I n, if Arc.meets legs (Sum.inr ⟨n,j⟩) i then f j else 0) ≤ 2*(u^(n+1)*v) := by
  intro f
  let r i j := ∑ t, Trail.tread X Y (n+1) i t j
  have hr i j : 0 ≤ r i j := Finset.sum_nonneg fun t _ => (tread_pos h1 h2 ..).le
  obtain ⟨-,ha,hb⟩ := drives hX hY (n+1)
  simp_rw [← Trail.wheels, show ∀ i j, rate 0 (separation (h i) (h j))=1 from fun i j => by simp [rate], one_mul,
    show ∀ i j, |∑ t, Trail.tread X Y (n+1) i t j|=r i j from fun i j => abs_of_nonneg (hr i j)] at ha hb
  have he := Breeze.pairHit hr ha hb Finset.univ i
  rw [Fintype.sum_prod_type]; unfold Arc.meets legs; simp only [Sum.elim_inr]
  simpa only [Finset.sum_ite_irrel,Finset.sum_const_zero,f,Arc.hits,Arc.meets,r,id_eq] using he

namespace Charges
variable (v : Charges)

def ink (G : Gauge) := v.price*(1+(Fintype.card G.ColorIndex:ℝ))
lemma ink_pos (G : Gauge) : 0 < v.ink G := mul_pos (zero_lt_one.trans_le v.paid) (by positivity)

def toll := v.speed / 2
lemma toll_pos : 0<v.toll := half_pos v.live

def coin (x : ℝ) := rate (-(v.delay/2)) (radiusB x)
lemma coin_pos (x : ℝ) : 0<v.coin x := rate_pos ..
lemma halves (x : ℝ) : v.coin x ^ 2 = v.levy x := by
  unfold coin levy rate; rw [sq,← Real.exp_add]; congr 1; ring

def hop (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge) : Wall (Active A x F) :=
  Matrix.of fun i j => v.ink G * rate (-v.toll) (separation (site i) (site j))

def tap (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge) : Wall (Active A x F) := v.coin x • v.hop x A F G

abbrev walkRate (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge) := Trail.tread (v.tap x A F G) (v.hop x A F G)

def pay (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge) : Full (Active A x F) → ℝ :=
  Sum.elim (fun _ => v.ink G * v.coin x) (fun ⟨m,⟨i,j⟩,h⟩ => v.walkRate x A F G (m+1) i h j)

variable (x : ℝ) (A : Stores S) (F : Forest S.ratio) (G : Gauge)
lemma hop_pos (i j) : 0<v.hop x A F G i j := mul_pos (v.ink_pos G) (rate_pos ..)
lemma tap_pos (i j) : 0<v.tap x A F G i j := mul_pos (v.coin_pos x) (v.hop_pos ..)
lemma walkRate_pos (n i t j) : 0<v.walkRate x A F G n i t j := tread_pos (v.tap_pos x A F G) (v.hop_pos x A F G) n i t j
lemma pay_pos (j) : 0<v.pay x A F G j := by
  cases j
  · exact mul_pos (v.ink_pos G) (v.coin_pos x)
  exact v.walkRate_pos ..

def lifetime (H : Patch) (G : Gauge) := v.ink G * Breeze.storm H v.toll
lemma lifetime_nn (H : Patch) : 0≤v.lifetime H G := mul_nonneg (v.ink_pos G).le (Breeze.storm_nn ..)

lemma hop_pours (he : S.patch=H) : Pours (v.hop x A F G) site site 0 (v.lifetime H G) := by
  have ht (i : Active A x F) := sitePrice (A:=A) (F:=F) v.toll v.toll_pos he (site i) x
  constructor
  · exact lifetime_nn ..
  · intro i; simp only [rate,zero_mul,Real.exp_zero,one_mul,abs_of_pos (v.hop_pos ..)]
    unfold hop; simp only [Matrix.of_apply,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (ht i) (v.ink_pos G).le
  intro i; simp only [rate,zero_mul,Real.exp_zero,one_mul,abs_of_pos (v.hop_pos ..)]
  unfold hop; simp_rw [Matrix.of_apply,separation_comm _ (site i),← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (ht i) (v.ink_pos G).le

-- sup over ALL finite multiplicity-preserving selections of this actual path family.
def audited (i) (j : Full (Active A x F)) := if Arc.meets legs j i then v.pay x A F G j else 0
lemma audited_nn i j : 0 ≤ v.audited x A F G i j := by unfold audited; split; exact (v.pay_pos ..).le; rfl

def top (G : Gauge) (H : Patch) (x : ℝ) := let q := v.coin x * v.lifetime H G
  v.ink G * v.coin x + 2*q*v.lifetime H G * (1-q)⁻¹

private lemma bend_total (he : S.patch=H) (hq : v.coin x*v.lifetime H G < 1) (i) :
    let q := v.coin x * v.lifetime H G
    let f := v.audited x A F G i ∘ Sum.inr
    Summable f ∧ ∑' j,f j ≤ 2*q*v.lifetime H G*(1-q)⁻¹ := by
  intro q f
  have h1 := v.hop_pours x A F G he
  have h2 : Pours (v.tap x A F G) site site 0 q := by
    unfold tap; simpa only [abs_of_pos (v.coin_pos x)] using h1.scale (v.coin x)
  have Hb n := bendHit h2 h1 (v.tap_pos x A F G) (v.hop_pos x A F G) n i
  let r (n : ℕ) := ∑' j, f ⟨n,j⟩
  have hr n : 0≤r n := tsum_nonneg fun i => v.audited_nn ..
  let M := 2*q*v.lifetime H G
  have ht n : r n ≤ M*q^n := (le_trans (b:=2*(q^(n+1)*v.lifetime H G)) (by unfold r; rw [tsum_fintype]; exact (Hb n)) (le_of_eq (by unfold M; ring)))
  have hy := (hasSum_geometric_of_lt_one h2.pos hq).mul_left M
  have h3 : Summable r := hy.summable.of_nonneg_of_le hr ht
  have hf : Summable f := (summable_sigma_of_nonneg (fun j => v.audited_nn ..)).mpr ⟨fun n => (hasSum_fintype _).summable,h3⟩
  exact ⟨hf, hf.tsum_sigma.trans_le ((h3.tsum_le_tsum ht hy.summable).trans_eq hy.tsum_eq)⟩

theorem priced (he : S.patch=H) (hq : v.coin x*v.lifetime H G < 1) (i) :
    Summable (v.audited x A F G i) ∧ ∑' j,v.audited x A F G i j ≤ v.top G H x := by
  obtain ⟨hh,ht⟩ := v.bend_total x A F G he hq i
  have hs := HasSum.sum (f:=v.audited x A F G i) (hasSum_fintype _) hh.hasSum
  have h1 : ∑ j,v.audited x A F G i (.inl j) = v.ink G * v.coin x := by simp [audited,Arc.meets,legs,pay]
  exact ⟨hs.summable,hs.tsum_eq.trans_le (add_le_add h1.le ht)⟩

lemma pay_finite (he : S.patch=H) (hq : v.coin x*v.lifetime H G < 1) (i : Active A x F) (t : Finset (Full (Active A x F))) :
    (∑ j∈t,v.audited x A F G i j) ≤ v.top G H x := by
  obtain ⟨h,ht⟩ := v.priced x A F G he hq i
  exact (h.sum_le_tsum t fun _ _ => v.audited_nn ..).trans ht

lemma pay_alone (he : S.patch=H) (hq : v.coin x*v.lifetime H G < 1) (j) : v.pay x A F G j ≤ v.top G H x := by
  have h := v.pay_finite x A F G he hq (legs j).1 {j}
  simpa only [Finset.sum_singleton,audited,if_pos (show Arc.meets legs j (legs j).1 from Or.inl rfl)] using h

lemma sponsored (H : Patch) {ε : ℝ} (he : 0<ε) : ∀ᶠ x : ℝ in atTop,
    v.coin x * v.lifetime H G < 1 ∧ v.top G H x ≤ ε := by
  have ht : Tendsto v.coin atTop (𝓝 0) := SectorTools.PhysicalGaussianInsertion.Physical.error_limit _ (half_pos v.time_pos)
  let q x := v.coin x * v.lifetime H G
  have hq : Tendsto q atTop (𝓝 0) := by simpa using ht.mul_const (v.lifetime H G)
  have hs : Tendsto (fun x => 1-q x) atTop (𝓝 1) := by simpa using hq.const_sub 1
  have h : Tendsto (v.top G H) atTop (𝓝 0) := by
    unfold Charges.top
    simpa only [mul_zero, zero_mul,add_zero,q] using (ht.const_mul (v.ink G)).add (((hq.const_mul 2).mul_const (v.lifetime H G)).mul (hs.inv₀ one_ne_zero))
  filter_upwards [hq.eventually (gt_mem_nhds zero_lt_one),h.eventually (ge_mem_nhds he)] with x hx hy
  exact ⟨hx,hy⟩
end Charges
end YM.PhysicalNext.JointLoad
