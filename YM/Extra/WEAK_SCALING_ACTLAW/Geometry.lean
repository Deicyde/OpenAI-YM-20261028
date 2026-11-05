import YM.Next.EXTRACTION.Tails

/-!
# Compact weak-test windows and aligned generic sampling

Part of the conditional ActLaw producer. Points n uses the actual Euclidean
4n norm, while displacement separation in `apart` uses the strict version of
the cubedist test. Only `clearance` avoids axis ties; aligned samples even for
configurations with ties can be chosen generic on the k grid (no more than a
bounded number of additional mesh spacings).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Metric Filter Function Extraction Climb
open scoped Topology ContDiff
variable {n : ℕ} {Q R t : ℝ}

def apart (Q : ℝ) (n : ℕ) := {x : Points n | ‖x‖ < Q ∧
  ∀ i j, i ≠ j → ∃ a : Axis, Q⁻¹ < |x j a - x i a|}

def clearance (Q : ℝ) (n : ℕ) := {x : Points n | ‖x‖ < Q ∧
  ∀ i j, i ≠ j → ∀ a : Axis, Q⁻¹ < |x j a - x i a|}

lemma apart_open (Q : ℝ) (n : ℕ) : IsOpen (apart Q n) := by
  rw [show apart Q n = {x : Points n | ‖x‖ < Q} ∩ ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
    ⋃ a : Axis, {x : Points n | Q⁻¹ < |x j a - x i a|} by ext; simp [apart]]
  exact (isOpen_lt continuous_norm continuous_const).inter (isOpen_iInter_of_finite fun _ =>
    isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => isOpen_iUnion fun _ =>
      isOpen_lt continuous_const (by fun_prop))

lemma clearance_open (Q : ℝ) (n : ℕ) : IsOpen (clearance Q n) := by
  rw [show clearance Q n = {x : Points n | ‖x‖ < Q} ∩ ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
    ⋂ a : Axis, {x : Points n | Q⁻¹ < |x j a - x i a|} by ext; simp [clearance]]
  exact (isOpen_lt continuous_norm continuous_const).inter (isOpen_iInter_of_finite fun _ =>
    isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ =>
      isOpen_lt continuous_const (by fun_prop))

lemma clearance_apart : clearance Q n ⊆ apart Q n :=
  fun _ h => ⟨h.1,fun i j e => ⟨timeAxis,h.2 i j e timeAxis⟩⟩
lemma apart_conf (hQ : 0 < Q) : apart Q n ⊆ conf n := by
  intro x hx i j he
  by_contra e
  obtain ⟨a,ha⟩ := hx.2 i j e
  simp only [show x i a=x j a from congrArg (fun u : E4 => u a) he, sub_self, abs_zero] at ha
  exact (inv_pos.mpr hQ).asymm ha
lemma clearance_generic (hQ : 0 < Q) : clearance Q n ⊆ YM.generic n := by
  intro x hx a i j he; by_contra e
  have h := hx.2 i j e a
  change x i a = x j a at he
  rw [he, sub_self, abs_zero] at h; exact (inv_pos.mpr hQ).asymm h

lemma window_inside (hr : 1 ≤ R) (hQ : R < Q) : Scaling.window R n ⊆ apart Q n := by
  intro x hx
  refine ⟨lt_of_le_of_lt hx.2 hQ, fun i j e => ?_⟩
  by_contra! he
  have h0 : 0 < Q := by linarith
  have h : cubedist (x j) (x i) ≤ Q⁻¹ := (dist_pi_le_iff (by positivity)).mpr he
  have hp := hx.1 j i e.symm
  exact ((inv_lt_inv₀ (lt_trans (by linarith) hQ) (by linarith)).2 hQ).not_ge (hp.trans h)

lemma compact_window (R : ℝ) (n : ℕ) : IsCompact (Scaling.window R n) := by
  rw [show Scaling.window R n = closedBall 0 R ∩ ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
    {x : Points n | R⁻¹ ≤ cubedist (x i) (x j)} by ext; simp [Scaling.window, spaced, and_comm]]
  exact (isCompact_closedBall (0 : Points n) R).inter_right (isClosed_iInter fun i =>
    isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_le continuous_const
      (continuous_cubedist.comp (show Continuous (fun x : Points n => (x i,x j)) by fun_prop)))

lemma eventually_clear {K : Set (Points n)} (hK : IsCompact K) (he : K ⊆ YM.generic n) :
    ∀ᶠ Q : ℝ in atTop, K ⊆ clearance Q n := by
  have ha (i j : Fin n) (a : Axis) : ∀ᶠ Q : ℝ in atTop, ∀ x ∈ K, i ≠ j → Q⁻¹ < |x j a-x i a| := by
    by_cases e : i=j
    · subst i; simp
    let f := fun x : Points n => |x j a-x i a|
    have hf : Continuous f := by dsimp [f]; fun_prop
    have h x (hx : x∈K) : 0 < f x := abs_pos.mpr (sub_ne_zero.mpr ((he hx a).ne (Ne.symm e)))
    obtain ⟨B,hB⟩ := (hK.image_of_continuousOn (hf.continuousOn.inv₀ (fun x hx => (h x hx).ne'))).bddAbove
    filter_upwards [eventually_gt_atTop (max 0 B)] with Q hQ x hx _
    exact (inv_lt_comm₀ (lt_of_le_of_lt (le_max_left ..) hQ) (h x hx)).mpr
      ((hB (mem_image_of_mem _ hx)).trans_lt ((le_max_right ..).trans_lt hQ))
  obtain ⟨b,hb⟩ := (hK.image continuous_norm).bddAbove
  have h := eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr (ha i j)
  filter_upwards [h,eventually_gt_atTop b] with Q hQ hu x hx
  exact ⟨(hb (mem_image_of_mem _ hx)).trans_lt hu,fun i j e a => hQ i j a x hx e⟩

lemma smul_tag (c t : ℝ) (u : Fin n → Lattice.Cover) : c • tag t u = tag (c*t) u := by
  ext i a; change c*(t*_)=_; simp [tag, mul_assoc]
lemma smul_generic {x : Points n} (hr : 0 < R) (hx : x ∈ YM.generic n) : R • x ∈ YM.generic n :=
  fun a _ _ h => hx a (mul_left_cancel₀ hr.ne' h)

/-- Round at a coarser multiple then offset the ith copy by i along all axes. -/
def sample (t : ℝ) (x : Points n) (i : Fin n) (a : Axis) : ℤ :=
  (n+1:ℕ)*address (((n+1:ℕ):ℝ)*t) x i a + i.val

lemma sample_clear (ht : 0 < t) (x : Points n) : tag t (sample t x) ∈ YM.generic n := by
  intro a i j h
  change t*((sample t x i a:ℤ):ℝ) = t*((sample t x j a:ℤ):ℝ) at h
  have he : sample t x i a = sample t x j a := by exact_mod_cast mul_left_cancel₀ ht.ne' h
  have hi : sample t x i a % ((n+1:ℕ):ℤ) = (i.val:ℤ) := by
    rw [sample,Int.mul_add_emod_self_left, Int.emod_eq_of_lt] <;> omega
  have hj : sample t x j a % ((n+1:ℕ):ℤ) = (j.val:ℤ) := by
    rw [sample,Int.mul_add_emod_self_left, Int.emod_eq_of_lt] <;> omega
  have e : (i.val:ℤ)=j.val := hi.symm.trans ((congrArg (fun x : ℤ => x % ((n+1:ℕ):ℤ)) he).trans hj)
  exact Fin.ext (by exact_mod_cast e)

lemma sample_bound (ht : 0 < t) (x : Points n) :
    dist (tag t (sample t x)) x ≤ ((4*n:ℝ)*(2*n+1))*t := by
  let e := tag t (sample t x)-x
  have H (i : Fin n) a : |e i a| ≤ (2*n+1)*t := by
    have hu := coord_grid_bound (show 0 < ((n+1:ℕ):ℝ)*t by positivity) x i a
    change |((n+1:ℕ):ℝ)*t*(_ : ℤ)-_| ≤ _ at hu
    change |t*((sample t x i a:ℤ):ℝ)-_| ≤ _
    unfold sample
    push_cast at *
    have h : (0 : ℝ) ≤ i.val*t := by positivity
    have h' : (i.val:ℝ)*t ≤ n*t := by gcongr; exact_mod_cast i.isLt.le
    rw [abs_le] at hu ⊢
    constructor <;> linarith!
  rw [dist_eq_norm]; change ‖e‖ ≤ _
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), ← (Points.flatten.norm_map e), EuclideanSpace.real_norm_sq_eq, mul_assoc]
  calc
    _ ≤ ∑ _k : Fin n × Axis, ((2*n+1)*t)^2 := Finset.sum_le_sum fun i _ => sq_le_sq.mpr
      (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (2*n+1)*t)]; exact H i.1 i.2)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_mul,Nat.cast_ofNat]
      rcases Nat.eq_zero_or_pos n with h|h
      · rw [h]; simp
      rw [mul_pow (4*(n:ℝ))]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hf : (1:ℝ) ≤ n := by exact_mod_cast h
      nlinarith

end YM.Extra.WeakScaling
