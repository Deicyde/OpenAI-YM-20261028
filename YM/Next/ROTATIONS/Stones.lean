import YM.Next.ROTATIONS.Yard
import YM.Work.A01.Conserve
/-!
# Glue back to local shell tests (combined gradients before integration).
Uses only configuration windows & all-spectator StressLaws.
-/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex  Row OS Table Ward Climb
open Analysis Work.A01
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {L : Register G} {S : Table L} {m : ℕ}

abbrev stone (x : Points (m+1)) (i : Fin (m+1)) := Points.rearrange (Equiv.swap 0 i) x
abbrev Quarry (x : Points (m+1)) (χ : Fin (m+1) → E4 → ℝ) := ∀ i, Window (stone x i) (χ i)
lemma quarry (x : Points (m+1)) (hx : x∈conf (m+1)) : ∃ χ, Quarry x χ := by
  have hi i := exists_window (stone x i) (Points.rearrange_in _ hx); choose χ hχ using hi; exact ⟨χ,hχ⟩
lemma quarry_germ (x : Points (m+1)) (χ : Fin (m+1)→E4→ℝ) (h : Quarry x χ) (i j : Fin (m+1)) :
    χ i =ᶠ[𝓝 (x j)] fun _ => if j=i then 1 else 0 := by
  let K := Equiv.swap 0 i; have he : K 0=i := Equiv.swap_apply_left ..
  have hp := h i
  split_ifs with hz
  · subst j; simpa [stone] using hp.2.2.1
  have hh : K.symm j≠0 := by rw [Ne,Equiv.symm_apply_eq]; exact hz
  obtain ⟨k,hk⟩ := Fin.exists_succ_eq_of_ne_zero hh
  have hT := hp.2.2.2 k
  rw [stone, Points.rearrange_at, hk, show Equiv.swap 0 i (K.symm j)=j from K.apply_symm_apply _] at hT
  exact notMem_tsupport_iff_eventuallyEq.mp hT

private def fellows (k : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+1)) :=
  (finSuccEquiv m).trans ((k.optionCongr).trans (finSuccEquiv m).symm)
private lemma necklace (k : Equiv.Perm (Fin m)) (x : Points m) (y) :
    Points.rearrange (fellows k) (Points.cons y x)=Points.cons y (Points.rearrange k x) := by
  ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [fellows,Points.cons]
private lemma viewed_perm (H : S.Symmetric) (J : Stress S) (q : Fin m→S.Tag) (k : Equiv.Perm (Fin m)) (x : Points m) (y)
    (h : Points.cons y (Points.rearrange k x)∈conf _) (d b : Axis) :
    viewed J q x d b y=viewed J (q ∘ k) (Points.rearrange k x) d b y := by
  let F : Fin (m+1)→S.Tag := Fin.cons (tag J d b) q
  have he : Points.cons y x ∈ conf _ := by
    have he := Points.rearrange_in (fellows k).symm h
    have hf : Points.rearrange (fellows k).symm (Points.cons y (Points.rearrange k x))=Points.cons y x := by
      rw [← necklace]; ext1 i; simp
    rwa [hf] at he
  change S.useAt S _ F=_; rw [← S.class_perm S H (fellows k) he F,necklace]; unfold viewed; congr 1
  ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [F,fellows,tag]

abbrev roll (K : Ortho.Skew) := fun p : E4 => M4.move K.val p
lemma rolling (K : Ortho.Skew) : roll K=orbital K 0 := funext fun i => by simp [roll,orbital]

abbrev loam (x : Points (m+1)) (q : Fin (m+1) → S.Tag) (J : Stress S) (K : Ortho.Skew)
    (χ : E4→ℝ) (a b : Axis) (y : E4) := Complex.ofReal (Analysis.D (basis a) χ y * roll K y b) * viewed J q x a b y
lemma rub (x : Points (m+1)) (hx : x∈conf _) (q : Fin (m+1)→ S.Tag) (J : Stress S) (H : S.Hierarchy)
    (K : Ortho.Skew) (i : Fin (m+1)) (χ : E4 → ℝ) (w : Window (stone x i) χ) :
    (∀ a b, Integrable (loam x q J K χ a b)) ∧
    -(∑ a,∑ b,∫ y, loam x q J K χ a b y)=flux J χ (roll K) (stone x i) (fun j : Fin m => q (Equiv.swap 0 i j.succ)) (q i).2 := by
  let r := Equiv.swap 0 i; let v := q ∘ r; let F (j : Fin m) := v j.succ
  have he : Fin.cons (α:=fun _ => S.Tag) ⟨_,(q i).2⟩ F = v := by
    ext1 a; refine Fin.cases ?_ (fun j => ?_) a <;> simp [v,r,F]
  have hf (a b) y : loam x q J K χ a b y=term J χ (roll K) (stone x i) F (q i).2 a b y := by
    by_cases h : Analysis.D (basis a) χ y=0
    · simp [loam,h,term]
    unfold loam term; rw [viewed_perm H.laws.toSymmetric J q r x y (separated_of_D (Points.rearrange_in r hx) w h),he]
  constructor
  · intro a b; rw [funext (hf a b)]
    apply term_integrable J χ (roll K) _ F _ H.smooth (Points.rearrange_in _ hx) w a b
    rw [rolling]; exact (smooth_orbital K 0 b).continuous
  unfold flux; simp_rw [hf]; rfl

private lemma swirl (K : Ortho.Skew) (J : Stress S) (H : S.Hierarchy) (q : Fin m→S.Tag) (x : Points (m+1)) (χ)
    (hx : x∈conf _) (w : Window x χ) (d : ℕ) (B : S.Field d) :
    flux J χ (roll K) x q (B:S.Field d) = shellSpin S J χ K x q B + ∑ b : Axis, (roll K (x 0) b) • shellGrad S J χ b x q B := by
  let u (b : Axis) := roll K (x 0) b
  let T (b : Axis) (a : Axis) y := Complex.ofReal (Analysis.D (basis a) χ y) * viewed J (Fin.cons ⟨d,B⟩ q) x a b y
  have he (b a : Axis) : Integrable (T b a) := by
    unfold T viewed; simpa only [mul_one] using integrableShell hx w H.smooth (S:=S) (Fin.cons (tag J a b) (Fin.cons (⟨d,B⟩:S.Tag) q)) a (fun _ => 1) continuous_const
  let F a b := term J χ (orbital K (x 0)) x q B a b
  have hh (a b : Axis) (y : E4) : term J χ (roll K) x q B a b y= F a b y + u b • T b a y := by
    unfold F T term viewed orbital
    have hp : roll K y b = M4.move K.val (y-x 0) b + u b := congr_fun (f:=fun j => roll K y j) (g:=fun j => M4.move K.val (y-x 0) j + roll K (x 0) j) (by
      have hz : roll K y=M4.move K.val (y-x 0) + roll K (x 0) := by unfold roll M4.move; rw [← map_add,sub_add_cancel]
      exact congr_arg WithLp.ofLp hz) b
    rw [hp]; simp [Complex.real_smul]; ring
  unfold flux
  have hi a b : integral volume (term J χ (roll K) x q B a b)=(∫ y,F a b y) + u b • ∫ y,T b a y := by
    rw [funext (hh a b), integral_add (term_integrable _ _ _ _ _ _ H.smooth hx w _ _ (smooth_orbital _ _ _ |>.continuous)) (show Integrable (fun y => u b • T b a y) from (he b a).smul (u b)), integral_smul]
  simp_rw [hi, Finset.sum_add_distrib, neg_add]
  congr 1; rw [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib ]
  simp only [shellGrad,smul_neg,Finset.smul_sum,← Finset.sum_neg_distrib]; rfl

abbrev imprint (x : Points (m+1)) (q : Fin (m+1)→S.Tag) (p : Parts S) (Y : SpinRows S) (K : Ortho.Skew) (i : Fin (m+1)) :=
    disc (update q i (turns Y K (q i))) x + ∑ b : Axis, roll K (x i) b • disc (update q i (⟨_,p _ b (q i).2⟩:S.Tag)) x
lemma stroke (P : DiffPlan S) (H : S.Hierarchy) (J : Stress S) (p : Parts S) (Y : SpinRows S) (h : Pre H P J p Y)
    (x : Points (m+1)) (q : Fin (m+1)→S.Tag) (hx : x∈conf _) (K : Ortho.Skew) (i : Fin (m+1)) (χ : E4→ℝ) (w : Window (stone x i) χ) :
    imprint x q p Y K i= -(∑ a,∑ b,∫ y,loam x q J K χ a b y) := by
  let r := Equiv.swap 0 i; let F (j : Fin m) := q (r j.succ)
  have hm := Points.rearrange_in r hx
  have hk (v : S.Tag) : disc (update q i v) x=S.useAt S (stone x i) (Fin.cons v F) := by
    unfold disc; rw [← S.class_perm S H.laws.toSymmetric r hx]; congr 1
    ext1 j; refine Fin.cases ?_ (fun k => ?_) j
    · simp [r]
    have he : r k.succ ≠ i := by rw [← show r 0=i from Equiv.swap_apply_left ..]; exact r.injective.ne k.succ_ne_zero
    simp [F,he]
  rw [(rub x hx q J H K i χ w).2, swirl K J H _ _ χ (Points.rearrange_in _ hx) w _ _]
  unfold imprint; rw [h.raw.rotation hm _ w,hk (turns Y K (q i))]; congr 1
  apply Finset.sum_congr rfl; intro b _
  rw [h.raw.translation hm _ w, hk]; simp only [stone,r,Points.rearrange_at,Equiv.swap_apply_left]; rfl
end YM.Outer
