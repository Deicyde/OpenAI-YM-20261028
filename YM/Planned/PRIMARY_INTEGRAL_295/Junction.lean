import YM.Next.WARD_BIN.Lies
import YM.Planned.PRIMARY_INTEGRAL_295.Units


/-!
# E Ju4, testing a normalized b stencil upon each ordered journey

Comparison affine term after continuation on any weighted coarse background
and all derivative rows, not polarized at identity only. No claim yet
that stationary fields meet that cost. Notation: n is the numbers of Lie
increments, r is rate on b (all points on cover; use lifted torus arrays
meeting this at their single actually used period); may be n=0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Junction
open Function Filter Set Metric Labels Lattice RG Place Carrier Source Bloch Precision Next.Free Units
open WardBin.Lies
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {d n j t r : ℕ} {S : Finset Cover} {L : Side}

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma liner (g : E →L[ℝ] F) (w : F) (x : E) : fderiv ℝ (fun z => w + g z) x=g := by
  exact (g.hasFDerivAt.const_add w).fderiv

/-- Cost for an affine map: uniform in all yields used later. -/
lemma straight (w : F) (g : E →L[ℝ] F) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun z=>w+g z) 0‖ ≤ ‖w‖+‖g‖ := by
  let f : E→F := fun z=> w+g z
  match r with
  | 0 => simp
  | 1 => rw [norm_iteratedFDeriv_one]; rw [liner]; exact le_add_of_nonneg_left (norm_nonneg _)
  | r+2 =>
    rw [← norm_iteratedFDeriv_fderiv,funext (liner g w),iteratedFDeriv_const_of_ne (by simp)]
    simp only [Pi.zero_apply,norm_zero]; positivity
end

def shift (v : Fin n → Dev S G) : Panels n →L[ℝ] Dev S G :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

def model (K : Lines L) (S : Finset Cover) (g : Window G.Color) (v : Fin n → Window G.Color) (x : Panels n) : Dev S G :=
    inView S (applyLine K g) + shift (fun i=>inView S (applyLine K (v i))) x

lemma shift_go (v : Fin n → Dev S G) (i : Fin n) : shift v (cart i)=v i := by
  unfold shift; rw [sum_apply]; simp [cart,Pi.single_apply]
lemma shift_cost (v : Fin n → Dev S G) (C : ℝ) (hC : 0≤C) (hv : ∀ i, ‖v i‖ ≤ C) : ‖shift v‖ ≤ n * C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x =>?_;
  unfold shift; rw [sum_apply]; apply (norm_sum_le ..).trans
  have he (i : Fin n) : ‖x i • v i‖ ≤ C*‖x‖ := by rw [norm_smul, mul_comm]; exact mul_le_mul (hv i) (norm_le_pi_norm ..) (norm_nonneg _) hC
  apply (Finset.sum_le_sum (fun i _=> he i)).trans_eq; simp [mul_assoc]

structure Guard (g : Window G.Color) (v : Fin n → Window G.Color) (r : ℕ) (M : ℝ) : Prop where
  once : Carries g r M
  batch : ∀ i, Carries (v i) r M

lemma model_smooth (K : Lines L) (S : Finset Cover) (g : Window G.Color) (v : Fin n → Window G.Color) :
    ContDiff ℝ ω (model K S g v) := by apply ContDiff.add contDiff_const; exact ContinuousLinearMap.contDiff _

lemma predictor (S : Finset Cover) (d n r : ℕ) (hr : d≤r) (hd : d≤j-2) (k : ℝ)
    (hk : 0 < k) (hj : 4 ≤ j) (ht : 4 ≤ t) : ∃ C:ℝ,1 ≤ C ∧ ∀ (P : Flight j t) (M : ℝ) (g : Window G.Color) (v : Fin n → Window G.Color),
    Guard g v r M → ∀ b:ℕ, ‖iteratedFDeriv ℝ b (model (linesOf P k) S g v) 0‖ ≤ C*M := by
  obtain ⟨C,hC,H⟩:=takeRow (G:=G) S d r hr hd k hk hj ht
  let D:=(d+1:ℕ)*C
  have hD: 1≤D := one_le_mul_of_one_le_of_one_le (by simp) hC
  refine ⟨D+n*D, hD.trans (le_add_of_nonneg_right (by positivity)),fun P M g v hv b=>?_⟩
  let K:=linesOf P k
  have hM:=hv.once.1
  have hu : unitStep P.L∈Icc 0 1:=⟨(unitStep_pos _).le,unitStep_le _⟩
  have he (g : Window G.Color) (h : Carries g r M) := (H P g M h).normed hu
  have hy (g : Window G.Color) (h : Carries g r M) : ‖inView S (applyLine K g)‖≤ D*M :=
    (he g h).trans (by rw [←mul_assoc (d+1:ℕ).cast]; exact mul_le_of_le_one_right (by positivity) hu.2)
  unfold model; apply (straight ..).trans
  refine (add_le_add (hy _ hv.once) (shift_cost _ (D*M) (by positivity) (fun i=> hy _ (hv.batch i)))).trans_eq ?_; ring

/-- Unmasked jets of the predicted primary column on raw local paths.
The `V` (not Sound germs of a predicted gauge-invariant operator on
coarse links) inputs local stencil. Other paths tested separately. -/
theorem shadeJourney {F : Labels.Frame G d} (A : Hol G) (B : SectionData F) (h : B.Sound A) (b : Bid.pop B) (i : F.Index) (M : ℝ)
    (hM : 0≤M) (r n : ℕ) (hr : d≤r) (hd : d≤j-2) (k : ℝ)
    (hk : 0 < k) (hj : 4 ≤ j) (ht : 4 ≤ t) : ∃ C:ℝ,0 ≤ C ∧ ∀ (P : Flight j t) (g : Window G.Color) (v : Fin n → Window G.Color),
    Guard g v r M → ∀ f∈Ioc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ n (Tones.tint B i f ∘ model (linesOf P k) B.stencil g v) 0 cart‖ ≤ C*unitStep P.L^(F.grades i).1 := by
  obtain ⟨u,hu,H⟩:=takeRow (G:=G) B.stencil d r hr hd k hk hj ht
  obtain ⟨C,hC,hc⟩:=earns A B h b i n (u*M) (by positivity)
  refine ⟨C,hC,fun P g v hv f hf=>?_⟩
  let y := inView B.stencil (applyLine (linesOf P k) g)
  let z i:=inView B.stencil (applyLine (linesOf P k) (v i))
  let m := shift z
  let F' := Tones.tint B i f
  let w := fun x=> F' (y+x)
  have hw : ContDiff ℝ ω w := (Tones.coat_smooth (column_smooth ..) ..).comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ n (w ∘ m) 0 cart‖ ≤ _
  rw [m.iteratedFDeriv_comp_right hw _ le_top]
  unfold w; rw [map_zero,iteratedFDeriv_comp_add_left,add_zero]; change ‖(iteratedFDeriv ℝ n F' y) (fun i=> shift z (cart i))‖ ≤ _
  simp_rw [shift_go]; rw [show y = (1:ℝ) • y from (one_smul _ _).symm]
  exact hc _ hf _ ⟨(unitStep_pos _).le,unitStep_le _⟩ z (fun i=> H _ _ _ (hv.batch i)) y (H _ _ _ hv.once) 1 (by simp)
end YM.Planned.PrimaryIntegral295.Junction
