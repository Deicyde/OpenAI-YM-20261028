import YM.Push.LOOP_COEFFICIENT.SliceChart
import YM.Push.LOOP_COEFFICIENT.Vector
import YM.Work.F05.Graphs


/-!
# The real slice determinant equals the joint combination on shell

Use all constrained rows including rooted coarse
frames.

No identity discarding a coordinate-change curvature off-shell.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Lattice RG Wilson Precision Exterior Tree Matrix Set Function Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

section algebra
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def shiftFee (N : Matrix m m ℝ) (B : Matrix n n ℝ) := (1/2:ℝ)*Real.log N.det - Real.log B.det

/-- An on-shell full Hessian and generator pair, allowing change of completion. -/
def Stable (Q : Matrix m m ℝ) (R : Matrix m n ℝ) := ∀ L : Matrix n m ℝ,
    IsUnit (L * R) → 0 < (Q + L.transpose * L).det ∧ ∀ L' : Matrix n m ℝ, IsUnit (L' * R) →
      shiftFee (Q + L.transpose * L) (L * R) = shiftFee (Q + L'.transpose * L') (L' * R)

private lemma splitLog {N : Matrix m m ℝ} {B : Matrix n n ℝ} {h j : ℝ} (hh : 0 < h) (hj : j ≠ 0) (hB : IsUnit B)
    (he : N.det * j^2 = B.det^2 * h) : 0 < N.det ∧ shiftFee N B = (1/2:ℝ)*Real.log h - Real.log j := by
  have hb := B.isUnit_iff_isUnit_det.mp hB |>.ne_zero
  have hn : 0 < N.det := pos_of_mul_pos_left (he.symm ▸ mul_pos (sq_pos_of_ne_zero hb) hh) (sq_nonneg _)
  refine ⟨hn,?_⟩
  have hl := congr_arg Real.log he
  rw [Real.log_mul hn.ne' (pow_ne_zero _ hj), Real.log_mul (pow_ne_zero _ hb) hh.ne', Real.log_pow,Real.log_pow] at hl
  dsimp [shiftFee]; push_cast at hl; linarith

lemma stable_split {k : Type} [Fintype k] [DecidableEq k] (Q : Matrix m m ℝ) (R : Matrix m n ℝ)
    (T : Matrix m k ℝ) (H : Matrix k k ℝ) (e : (n ⊕ k) ≃ m) (hh : 0 < H.det) (hj : IsUnit ((sides R T).submatrix e id))
    (he : (sides R T).transpose * Q * sides R T = fromBlocks 0 0 0 H) : Stable Q R := by
  have ht (L : Matrix n m ℝ) (hl : IsUnit (L * R)) := splitLog hh ((isUnit_iff_isUnit_det _).mp hj).ne_zero hl
    (complete_det Q R T H L e he)
  intro L hl; exact ⟨(ht L hl).1,fun L' hL => (ht L hl).2.trans (ht L' hL).2.symm⟩

lemma shiftFee_transfer (Q Q' : Matrix m m ℝ) (R R' : Matrix m n ℝ) (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (hq : A.transpose * Q' * A = Q) (hr : A * R = R' * B) (ha : |A.det| = 1) (hb : |B.det| = 1)
    (hs : Stable Q R) (L L' : Matrix n m ℝ) (hl : IsUnit (L * R)) (hl' : IsUnit (L' * R')) :
    shiftFee (Q + L.transpose * L) (L * R) = shiftFee (Q' + L'.transpose * L') (L' * R') := by
  have hh : IsUnit B := B.isUnit_iff_isUnit_det.mpr <| isUnit_iff_ne_zero.mpr (fun h => by simp [h] at hb)
  have he : (L' * A)*R = L' * R' * B := by rw [Matrix.mul_assoc,hr,Matrix.mul_assoc]
  rw [(hs L hl).2 (L' * A) (he.symm ▸ hl'.mul hh)]
  unfold shiftFee
  congr 1
  · rw [show Q + _ = A.transpose * (Q' + L'.transpose * L') * A by rw [← hq]; simp [Matrix.mul_add, Matrix.add_mul,transpose_mul,Matrix.mul_assoc]]
    congr 2
    rw [det_mul, det_mul,det_transpose,mul_comm A.det,mul_assoc,← sq, ← sq_abs, ha]; simp
  rw [he,det_mul,← Real.log_abs,abs_mul,hb,mul_one,Real.log_abs]
end algebra

variable {c f : Side} {G : Gauge} {S : StepData c f}
variable {F : Forest S.ratio} {p : Clip} {W : PathData G} {σ C Λ : ℝ}
variable (t : S.Choices)
variable {P : ChartRatio G}

lemma rode_fee (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (u : fieldDir G c 1) (z : Pack F G) :
    completed p W t (represent u) (ride F (represent u) z) = tested F t p W u (inField F z) := by
  have he := completed_gauge h hw t (vary 1 (inGauge z)) 1 (represent u) (mounted F (represent u) (inField F z))
  rw [gauge_one] at he
  exact he.trans (by
    rw [completed, Zmap, show auxiliaries (mounted F (represent u) (inField F z))=1 from rfl, gauge_one]; rfl)

def readField (G : Gauge) (F : Forest S.ratio) : Pack F G →L[ℝ] AxisChart G F :=
  ((fromColor G F.Free).symm : _ →L[ℝ] _).comp (ContinuousLinearMap.pi fun i => .proj (.inr i))

lemma readFrame (j : SiteKey G f ⊕ Key F G) : readField G F (Pi.single j 1) = j.elim (fun _ => (0:AxisChart G F)) (frame F) := by
  cases j with
  | inl j =>
    ext x i
    change Pi.single (M:=fun _ : SiteKey G f ⊕ Key F G => ℝ) (.inl j) 1 (.inr (x,i)) = 0
    simp
  | inr j =>
    ext x i
    change Pi.single (M:=fun _ : SiteKey G f ⊕ Key F G => ℝ) (.inr j) 1 (.inr (x,i)) = frame F j x i
    obtain ⟨y,k⟩ := j
    by_cases h : x=y <;> simp [Pi.single_apply,frame, *, Prod.ext_iff]

lemma steered_price (u : fieldDir G c 1) (b : AxisChart G F) (ht : ContDiffAt ℝ ω (tested F t p W u) b)
    (hs : fderiv ℝ (tested F t p W u) b = 0) : bilinearAt (tested F t p W u ∘ readField G F) (arrival b) =
      fromBlocks (0 : Matrix (SiteKey G f) _ ℝ) 0 0 (hessian F t p W u b) := by
  let L := readField G F
  have h : L (arrival b) = b := (paint G F.Free).apply_symm_apply _
  have he := Work.F05.bend_comp_stationary (g:=L) (x:=arrival b) (h.symm ▸ ht) L.contDiff.contDiffAt (h.symm ▸ hs)
  rw [L.fderiv,h] at he
  rw [bilinearAt,he]; ext i j
  rw [LinearMap.toMatrix₂'_apply]; change Work.F05.bend _ _ (readField G F _) (readField G F _) = _
  rw [readFrame,readFrame]; cases i <;> cases j
  · simp
  · simp
  · simp
  exact Work.F05.bend_apply ..

structure AtStation (p : Clip) (W : PathData G) (t : S.Choices) (V : Config G c) (U : Loops.Inputs G c f) : Prop where
  smooth : ContDiffAt ℝ ω (completed p W t V ∘ vary U) 0
  quiet : fderiv ℝ (completed p W t V ∘ vary U) 0 = 0
  stable : Stable (cost (completed p W t V) U) (R_tot S U)

private lemma linearAt_surj {n m : Type} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
    {r : (n → ℝ) → m → ℝ} {z} {e : n ≃ m} (h : IsUnit ((linearAt r z).submatrix e id)) : Surjective (fderiv ℝ r z) := by
  let M := (linearAt r z).submatrix e id
  intro v
  refine ⟨M⁻¹ *ᵥ (v ∘ e),?_⟩
  rw [← linearAt_mulVec]
  funext i
  obtain ⟨i,rfl⟩ := e.surjective i
  change (M *ᵥ (M⁻¹ *ᵥ (v ∘ e))) i = _
  rw [Matrix.mulVec_mulVec,M.mul_nonsing_inv (M.isUnit_iff_isUnit_det.mp h),Matrix.one_mulVec]; rfl

lemma shell_price (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (u : fieldDir G c 1) (b : AxisChart G F)
    (hp : LocalRatio P) (hb : ∀ i, b i ∈ Metric.ball 0 P.radius) (hs : fderiv ℝ (tested F t p W u) b = 0)
    (ht : ContDiffAt ℝ ω (tested F t p W u) b) (hd : 0 < (hessian F t p W u b).det)
    (hu : MatDiffAt (Zmap t ∘ vary (mounted F (represent u) b)) 0)
    (hx : MatDiffAt (Psi t ∘ vary (mounted F (represent u) b)) 0) :
    AtStation p W t (represent u) (mounted F (represent u) b) ∧
      scalar p W t (represent u) (mounted F (represent u) b) =
        (1/2:ℝ) * Real.log (hessian F t p W u b).det - Real.log (∏ i, P.J (b i)) := by
  let V := represent u
  let U := mounted F V b
  let T := steering F V b
  let z := arrival b
  have hT : T z = 0 := steering_zero ..
  let e := pins F G
  have hj : |((steered F V b).submatrix e id).det| = ∏ i, P.J (b i) := steered_det F V b hp hb
  have hj' : ((steered F V b).submatrix e id).det ≠ 0 := fun h =>
    (Finset.prod_pos (fun i _ => hp.pos _ (hb i))).ne' (hj.symm.trans (by rw [h,abs_zero]))
  have hI := (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hj')
  have he : Tendsto (ride F V) (𝓝 z) (𝓝 U) := by simpa only [z,ride_arrive] using! (ride_diff F V z).continuousAt.tendsto
  let A := completed p W t V ∘ vary U
  let R := R_tot S U
  let L := completion t U
  have hA : ContDiffAt ℝ ω A 0 := (Work.F02.mainTerm_contDiffAt hw (A:=positions ∘ vary U) (x:=0) (fun _ => vary_diff _)).add
    (penalty_diff S (matDiffAt_const _) hu)
  let Y := tested F t p W u ∘ readField G F
  have hY := (paint G F.Free).apply_symm_apply b
  change readField G F z = b at hY
  have hf : A ∘ T =ᶠ[𝓝 z] Y := by
    filter_upwards [he.eventually (vary_displacement U)] with w h1
    change completed _ _ _ _ (vary U (displacement U _)) = _
    rw [h1]; exact rode_fee t h hw u w
  have hr := fderiv_comp z (show DifferentiableAt ℝ A (T z) from hT.symm ▸ hA.differentiableAt (by simp))
    ((steering_diff F V b).differentiableAt (by simp))
  rw [hf.fderiv_eq, show fderiv ℝ Y z = 0 by
    unfold Y; rw [fderiv_comp z (show DifferentiableAt ℝ _ ((readField G F) z) from hY.symm ▸ ht.differentiableAt (by simp)) (readField G F).differentiableAt,hY,hs, ContinuousLinearMap.zero_comp], hT] at hr
  have hg : fderiv ℝ A 0 = 0 := ContinuousLinearMap.ext (fun v => by
    obtain ⟨w,rfl⟩ := linearAt_surj hI v
    exact DFunLike.congr_fun hr.symm w)
  have hc : (steered F V b).transpose * cost (completed p W t V) U * steered F V b =
      fromBlocks 0 0 0 (hessian F t p W u b) := by
    change (linearAt T z).transpose * bilinearAt A 0 * linearAt T z = _
    rw [← hT,← bilinearAt_comp (g:=T) (x:=z) (f:=A) (hT.symm ▸ hA) (steering_diff F V b) (hT.symm ▸ hg),
      bilinearAt_congr hf]; exact steered_price t u b ht hs
  rw [steered_eq] at hc hj' hI
  have heq := complete_det _ R _ _ L e hc
  rw [show L * R = _ from completion_brace h t U hx] at heq
  refine ⟨⟨hA,hg,stable_split _ R _ _ e hd hI hc⟩,?_⟩
  change shiftFee _ _ = _
  rw [← hj, steered_eq,Real.log_abs]; exact (splitLog hd hj' (ghost_pos _ (mu S) mu_pos).isUnit heq).2

lemma mounted_home {ρ : fieldDir G c 1 → AxisChart G F} (hr : Critical F p W ρ) :
    Tendsto (fun x => mounted F (represent x) (ρ x)) (𝓝 0) (𝓝 1) := by
  have ht := (mounted_diff F hr.2.1 (x:=0) (V:=represent) (fun i => (Work.F03.represent_smooth i).contDiffAt)).continuousAt.tendsto
  rw [hr.1,link_one] at ht
  have he : mounted F (1:Config G c) (0:AxisChart G F) = 1 := by
    funext x; cases x
    · change lifting F (1:Config G c) 0 _ = _; rw [lifted, replica_one]; rfl
    · rfl
  exact he ▸ ht

lemma smooth_near {m : Type} [Fintype m] {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {f : PatchField G m → H}
    (h : ContDiffAt ℝ ω (f ∘ vary 1) 0) : ∀ᶠ U in 𝓝 (1:PatchField G m), ContDiffAt ℝ ω (f ∘ vary U) 0 := by
  let w := fun U : PatchField G m => displacement 1 U
  have hc : ContinuousAt (fun U : PatchField G m => fun i => delta ((1:PatchField G m) i) (U i)) 1 := by
    refine continuousAt_pi.mpr (fun i => ?_)
    simp only [delta,Pi.one_apply,inv_one,mul_one]
    have ht := G.continuous_mat.comp (continuous_apply (A:=fun _ : m => G.El) i)
    exact ContinuousAt.comp (x:=(1:PatchField G m)) (f:=fun U : PatchField G m => G.mat (U i)) (g:=G.plog)
      G.plog_diff.continuousAt ht.continuousAt
  have he : Tendsto w (𝓝 1) (𝓝 0) := by
    rw [← show w 1=0 from displacement_self _]
    exact ((fromColor G m).continuousAt.comp hc)
  have hz (i : m) : ∀ᶠ U : PatchField G m in 𝓝 1, ContDiffAt ℝ ω G.plog (G.mat (U i)) :=
    ((G.continuous_mat.comp (continuous_apply i)).tendsto (1:PatchField G m)).eventually (by simpa using! G.plog_diff.eventually (by simp))
  filter_upwards [he.eventually (h.eventually (by simp)),eventually_eventually_nhds.mpr (vary_displacement (1:PatchField G m)),eventually_all.mpr hz] with U hu hv hq
  have ht : Tendsto (vary U) (𝓝 0) (𝓝 U) := by simpa only [vary_zero] using (vary_diff (U:=U) (x:=0)).continuousAt.tendsto
  have hD : ContDiffAt ℝ ω (w ∘ vary U) 0 := (fromColor G _).contDiff.contDiffAt.comp
    (f:=fun a i => delta 1 (vary U a i)) _ (contDiffAt_pi.mpr fun i => by
      simp only [delta,inv_one,mul_one]; exact (show ContDiffAt ℝ ω G.plog (G.mat (vary U 0 i)) by rw [vary_zero]; exact hq i).comp (f:=fun a => G.mat (vary U a i)) _ (vary_diff i))
  have hU : ContDiffAt ℝ ω (f ∘ vary 1) ((w ∘ vary U) 0) := by simpa only [Function.comp_apply,vary_zero] using hu
  exact (hU.comp 0 hD).congr_of_eventuallyEq ((ht.eventually hv).mono fun _ he => congr_arg f he.symm)

lemma thermal_eq (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) {a : ℝ} (ha : 0 < a) (hGap : PriceGap F p W a)
    (hp : LocalRatio P) {ρ : fieldDir G c 1 → AxisChart G F} (hr : Critical F p W ρ) : ∀ᶠ x in 𝓝 0,
    AtStation p W t (represent x) (mounted F (represent x) (ρ x)) ∧
      thermal F t p W ρ P x = loop W (positions (mounted F (represent x) (ρ x))) + scalar p W t (represent x) (mounted F (represent x) (ρ x)) := by
  have he (i : F.Free) : ∀ᶠ x in 𝓝 0, ρ x i ∈ Metric.ball 0 P.radius := by
    have he := ((continuous_apply i).continuousAt.comp hr.2.1.continuousAt).tendsto
    rw [Function.comp_apply,hr.1] at he; exact he.eventually (Metric.ball_mem_nhds _ hp.patch)
  have hu : ∀ᶠ x in 𝓝 0, MatDiffAt (Zmap t ∘ vary (mounted F (represent x) (ρ x))) 0 := eventually_all.mpr fun i =>
    (mounted_home hr).eventually (smooth_near (f:=fun U => G.mat (Zmap t U i)) ((Zmap_diff h t (by simp) vary_diff) i))
  have hx : ∀ᶠ x in 𝓝 0, MatDiffAt (Psi t ∘ vary (mounted F (represent x) (ρ x))) 0 := eventually_all.mpr fun i =>
    (mounted_home hr).eventually (smooth_near (f:=fun U => G.mat (Psi t U i)) ((Psi_diff h t (by simp) vary_diff) i))
  filter_upwards [eventually_all.mpr he,(hr.2.2 t).2,(Work.F05.crit_home hr).eventually ((hr.2.2 t).1.eventually (by simp)),Work.F05.hessian_pos ha hGap hr t,hu,hx] with x he hh ht hd hv hX
  obtain ⟨ha,hb⟩ := shell_price t h hw x (ρ x) hp he hh.fderiv (ht.comp (f:=fun y => (x,y)) _ (contDiffAt_const.prodMk contDiffAt_id)) hd hv hX
  exact ⟨ha,by rw [hb]; unfold thermal; rw [add_sub_assoc]; rfl⟩
end YM.Push.Loops
