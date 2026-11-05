import YM.Next.ROTATIONS.Stones
/-! # Combined gradients. Flux equals local turn up to sign. No contact trace. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Row OS Ward Table Climb Analysis Work.A01
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Classical
variable {G : Gauge} {L : Register G} {S : Table L} {m : ℕ}

abbrev comps (b : Axis) (V : E4→E4) := fun y : E4 => V y b
lemma roll_smooth (K : Ortho.Skew) (b : Axis) : ContDiff ℝ ∞ (comps b (roll K)) := by rw [rolling]; exact smooth_orbital K 0 b
lemma roll_k (K : Ortho.Skew) : killing (roll K) := by rw [rolling]; exact killing_orbital K 0

abbrev creek (x : Points (m+1)) (q : Fin (m+1)→S.Tag) (J : Stress S) (F : Axis→E4→ℝ) (a b : Axis) (y : E4) :=
    D (basis a) (F b) y • viewed J q x a b y
abbrev river (x : Points (m+1)) (q : Fin (m+1)→S.Tag) (J : Stress S) (F : Axis→E4→ℝ) (y : E4) :=
    ∑ a,∑ b, creek x q J F a b y

def wash (K : Ortho.Skew) (χ : Fin m→E4→ℝ) (b : Axis) := fun y : E4 => ∑ i, χ i y * roll K y b
lemma wash_s (K : Ortho.Skew) (χ : Fin m→E4→ℝ) (b : Axis) (hf : ∀ i,ContDiff ℝ ∞ (χ i)) : ContDiff ℝ ∞ (wash K χ b) := ContDiff.sum fun i _ => (hf i).mul (roll_smooth K b)
lemma wash_short (K : Ortho.Skew) (χ : Fin m→E4→ℝ) (b : Axis) (hf : ∀ i, HasCompactSupport (χ i)) :
    HasCompactSupport (wash K χ b) := by
  let f (i : Fin m) (y : E4) := χ i y * roll K y b; rw [show wash K χ b=∑ i,f i by ext y; simp [wash,f]]
  apply HasCompactSupport.finset_sum
  exact fun i _ => HasCompactSupport.mul_right (hf i)
lemma wash_home (x : Points (m+1)) (χ : Fin (m+1)→E4→ℝ) (K : Ortho.Skew) (w : Quarry x χ) (i : Fin (m+1)) (b : Axis) :
    wash K χ b =ᶠ[𝓝 (x i)] comps b (roll K) := by
  filter_upwards [eventually_all.mpr (fun j => quarry_germ x χ w j i)] with y hy; unfold wash comps
  rw [Finset.sum_eq_single i]
  · rw [hy]; simp
  · intro k _ hk; rw [hy]; simp [Ne.symm hk]
  simp
lemma wash_d (K : Ortho.Skew) (χ : Fin m→E4→ℝ) (w : ∀ i,ContDiff ℝ ∞ (χ i)) (a b : Axis) (y : E4) :
    D (basis a) (wash K χ b) y = ∑ i, (D (basis a) (χ i) y * roll K y b + χ i y * D (basis a) (comps b (roll K)) y) := by
  have hu i : DifferentiableAt ℝ (χ i) y := ((w i).differentiable (by simp) _)
  have hh : DifferentiableAt ℝ (comps b (roll K)) y := (roll_smooth K b).differentiable (by simp) _
  unfold D wash; rw [fderiv_fun_sum,_root_.sum_apply]; swap; · exact fun i _ => (hu i).mul hh
  refine Finset.sum_congr rfl fun i _ => ?_
  change fderiv ℝ (fun z => χ i z * comps b (roll K) z) y (basis a)=_
  rw [fderiv_fun_mul (hu i) hh]; simp [comps]; ring
lemma sands (P : DiffPlan S) (H : S.Hierarchy) (J : Stress S) (C : Conserved P H.spin J) (K : Ortho.Skew)
    (χ : Fin (m+1)→E4→ℝ) (x : Points (m+1)) (w : Quarry x χ) (q : Fin (m+1)→S.Tag) (y : E4) :
    river x q J (wash K χ) y= ∑ i,∑ a,∑ b,loam x q J K (χ i) a b y := by
  let A i a b := (χ i y * D (basis a) (comps b (roll K)) y) • viewed J q x a b y
  have ht (i) : ∑ a, ∑ b, A i a b=0 := by
    have he a b : A i a b= -A i b a := by
      unfold A; rw [show D (basis a) (comps b (roll K)) y=_ from roll_k K a b y, mul_neg,neg_smul]
      unfold viewed; rw [C.symmetric a b]
    let z := ∑ a,∑ b,A i a b
    have hh : z= -z := calc
      _ = ∑ a,∑ b, -A i b a := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => he a b
      _ = -z := by rw [Finset.sum_comm]; simp_rw [Finset.sum_neg_distrib]; rfl
    have hf : 2*z=0 := by
      rw [two_mul]; conv_lhs => lhs; rw [hh]
      exact neg_add_cancel _
    exact (mul_eq_zero.mp hf).resolve_left (by norm_num)
  have he a b : creek x q J (wash K χ) a b y= ∑ i, (loam x q J K (χ i) a b y+A i a b) := by
    unfold creek; rw [wash_d K χ (fun i => (w i).1),Finset.sum_smul]; apply Finset.sum_congr rfl; intro i hi
    rw [add_smul]; rfl
  unfold river; simp_rw [he]
  rw [show (∑ a : Axis, ∑ b : Axis, ∑ i, (loam x q J K (χ i) a b y+A i a b))=∑ i,∑ a,∑ b,(loam x q J K (χ i) a b y+A i a b) by
    rw [Finset.sum_comm];
    rw [Finset.sum_comm (s:=Finset.univ) (f:=fun i a => ∑ b,(loam x q J K (χ i) a b y+A i a b))]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm ]
  refine Finset.sum_congr rfl fun i _ => ?_; simp_rw [Finset.sum_add_distrib,ht,add_zero]

lemma paid_zero (P : DiffPlan S) (H : S.Hierarchy) (hp : P.Derivatives S) (J : Stress S) (C : Conserved P H.spin J) (x : Points (m+1))
    (hx : x∈conf _) (q : Fin (m+1)→S.Tag) (F : Axis→E4→ℝ) (hf : ∀ b,ContDiff ℝ ∞ (F b)) (hv : ∀ b,HasCompactSupport (F b))
    (he : ∀ b i, x i∉tsupport (F b)) : Integrable (river x q J F) ∧ (∫ y,river x q J F y)=0 := by
  have hl (b : Axis) : ∀ y ∈ tsupport (F b), Points.cons y x∈conf _ := fun y hy => conf_cons hx fun i h => he b i (h ▸ hy)
  have hi (b a : Axis) : Integrable (creek x q J F a b) := cutoff_integrable ((hv b).fderiv_apply ℝ (basis a))
    (continuous_iff_continuousAt.mpr fun y => (dSmooth (m:=∞) ((hf b).contDiffAt (x:=y)) (basis a) (by simp)).continuousAt)
    (fun y hy => (smooth_cons S H.smooth _ q (hl b y (tsupport_fderiv_apply_subset ℝ (basis a) hy))).continuousAt)
  constructor
  · exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi b a
  unfold river
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hi b a)]; simp_rw [integral_finsetSum _ (fun b _ => hi b _)]
  rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun b _ => ?_
  have h := cutoff_zero H.smooth P hp J C (fun _ => basis b) (fun _ => contDiff_const) (killing_const (basis b)) x q (F b) (hf b) (hv b) (hl b)
  rw [neg_eq_zero] at h
  have HH (a : Axis) (y : E4) : current J (fun _ => basis b) x q a y=viewed J q x a b y := by
    unfold current viewed; simp
  simp_rw [HH] at h; exact h

lemma flux_value (P : DiffPlan S) (H : S.Hierarchy) (hp : P.Derivatives S) (J : Stress S) (p : Parts S) (Y : SpinRows S) (h : Pre H P J p Y) (K : Ortho.Skew)
    (x : Points (m+1)) (hx : x∈conf _) (q : Fin (m+1)→S.Tag) (F : Axis→E4→ℝ) (hF : ∀ b,ContDiff ℝ ∞ (F b)) (hl : ∀ b,HasCompactSupport (F b))
    (hk : ∀ b i,F b=ᶠ[𝓝 (x i)] comps b (roll K)) :
    Climb.localTurn p Y K q x= -(∫ y,river x q J F y) := by
  obtain ⟨χ,hχ⟩ := quarry x hx
  let u := wash K χ; let v : Axis→E4→ℝ := F-u
  have hs b : ContDiff ℝ ∞ (u b) := wash_s _ _ _ fun i => (hχ i).1
  have hv b : ContDiff ℝ ∞ (v b) := ContDiff.sub (hF b) (hs b)
  have hh b : HasCompactSupport (v b) := HasCompactSupport.sub (hl b) (wash_short K χ b fun i => (hχ i).2.1)
  have hw (b i) : x i ∉ tsupport (v b) := notMem_tsupport_iff_eventuallyEq.mpr (by
    have ht : F b=ᶠ[𝓝 (x i)] u b := (hk b i).trans (wash_home x χ K hχ i b).symm
    filter_upwards [ht] with y hy; change F b y-u b y=0; rw [hy,sub_self])
  obtain ⟨hA,hL⟩ := paid_zero P H hp J h.tensor x hx q v hv hh hw
  have he y : river x q J F y=river x q J v y+river x q J u y := by
    have H (a b : Axis) : creek x q J F a b y=creek x q J v a b y+creek x q J u a b y := by
      unfold creek
      rw [← add_smul]
      congr 1; unfold v D
      rw [Pi.sub_apply,fderiv_sub (show DifferentiableAt ℝ _ y from (hF b).differentiable (by simp) y) ((hs b).differentiable (by simp) y),_root_.sub_apply,sub_add_cancel]
    simp_rw [river,H,Finset.sum_add_distrib]
  have ht := fun i a b => (rub x hx q J H K i (χ i) (hχ i)).1 a b
  have hI : Integrable (river x q J u) := by
    rw [funext (sands P H J h.tensor K χ x hχ q)]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ht i a b
  simp_rw [he]; rw [integral_add hA hI, hL,zero_add]
  simp_rw [show ∀ y, river x q J u y=_ from sands P H J h.tensor K χ x hχ q]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ht i a b),← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change imprint x q p Y K i = _; rw [stroke P H J p Y h x q hx K i _ (hχ i), integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => ht i a b)]
  congr 1; apply Finset.sum_congr rfl; intro a _; rw [integral_finsetSum _ (fun b _ => ht i a b)]
end YM.Outer
