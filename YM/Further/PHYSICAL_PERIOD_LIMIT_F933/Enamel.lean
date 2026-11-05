import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Inflation
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Shingle
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Withdrawal
import YM.Push.STATIONARY_UNIFORM.Along


/-! # Sealing the matrix entries for fixed unscaled external insertions

About the actual lifted graph. Applies to arbitrary real waves (unit per color/face)
at once. Rate tiny, anchor Ball x=0 at P. Re-readable, unlike a Hilbert bound on all external legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Enamel
open Jacobi Polytrace Withdrawal   Inflation Shingle Push.Uniform
open Function Lattice Gauge RG Tree Matrix Finset Precision Filter Exterior Bid Wilson Set Metric
open scoped Topology ContDiff BigOperators Classical
variable {α ι κ β X : Type} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β] [NormedAddCommGroup X] [NormedSpace ℝ X]
  {n : Side} {N K : ℕ} {a C : ℝ}


section K
variable {l : ι ⊕ κ→Site n} {x : Positions (ι ⊕ κ)} {f : Positions (ι ⊕ κ)→ℝ} {g : X→Positions (ι ⊕ κ)}
local notation "D" => Decay a
local notation "β₀" => l ∘ (@Sum.inr ι κ)
lemma internal (h : Scatter l a N f x C) (hc : ContDiffAt ℝ ω f x) (he : 4≤N) (v w) (i j : κ) :
    |delta (bolt v) (block f) x i j| ≤ C*(D (β₀ i) (β₀ j)*D (β₀ i) (l v)) ∧
    |delta (bolt v) (delta (bolt w) (block f)) x i j| ≤ C*(D (β₀ i) (β₀ j)*D (β₀ i) (l v)*D (β₀ i) (l w)) := by
  rw [echogram₁ hc, echogram₂ hc]
  have h1 := h 3 (le_trans (by norm_num) he) ![v,Sum.inr j, Sum.inr i] 2
  have h2 := h 4 he ![v,w,Sum.inr j, Sum.inr i] 3
  have comp (j : κ) : β₀ j=l (Sum.inr j) := rfl
  simpa [Decay, Real.exp_add,mul_add,Fin.sum_univ_succ,spanSites,Nat.cast_add,mul_left_comm,mul_comm,mul_assoc,comp]
    using And.intro h1 h2

-- uniform implied cash for (lifted) v, w directions supplied through 2
set_option maxHeartbeats 350000 in
lemma borrowed (hm : Multiplicity l K) (hp : 0<a) (hC : 0≤C) {s : X} (Q : Scatter l a N f (g s) C) (hf : ContDiffAt ℝ ω f (g s))
    (hg : ContDiffAt ℝ ω g s) (he : 4≤N) (v w : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : ∀ i, ‖Withdrawal.move v g s i‖ ≤ A)
    (hu' : ∀ i, ‖Withdrawal.move w g s i‖ ≤ A) (hv : ∀ i, ‖rise v w g s i‖ ≤ B) :
    let P := space K a; let F := block f ∘ g
    Faces F s ∧ Sealed β₀ a (delta w F s) (A*C*P) ∧ Sealed β₀ a (delta v (delta w F) s) (A*A*C*P*P+C*B*P) := by
  let F := block f ∘ g
  let P := space K a
  have hP : 0≤P := space_pos K hp
  have hx := echogram hf
  have hd i j k d := internal Q hf he i j k d
  refine ⟨fun i j=> (hx i j).comp _ hg,fun i j=>?_,fun i j=>?_⟩
  · let S (x:Positions (ι ⊕ κ)) := block f x i j
    change |blade _ (S ∘ g) s| ≤ _; rw [entered w hg (hx i j)]; apply le_trans (Finset.abs_sum_le_sum_abs ..)
    let M k := D (β₀ i) (l k); let d := D (β₀ i) (β₀ j)
    have hr (p q : Site n) : 0≤D p q := (decay_pos ..).le
    have hs k : |Withdrawal.move w g s k * blade (bolt k) S (g s)| ≤ A*(C*d)*M k := by
      rw [abs_mul, mul_assoc A, mul_assoc C]; exact mul_le_mul (hu' _) (hd k k i j).1 (abs_nonneg _) hA
    apply le_trans (Finset.sum_le_sum fun k _=>hs k); rw [← Finset.mul_sum]
    have hu := mul_le_mul_of_nonneg_left (hm.count _ hp (β₀ i)) (mul_nonneg hA (mul_nonneg hC (hr (β₀ i) (β₀ j))))
    calc
      _ ≤ A*(C*d)*P := hu
      _ = _ := by unfold d P; ring
  let S (x:Positions (ι ⊕ κ)) := block f x i j
  change |mixed _ _ (S ∘ g) s| ≤ _; rw [torn v w hg (hx i j),add_mul]; apply (abs_add_le ..).trans (add_le_add _ _)
  · let M k := D (β₀ i) (l k); let d := D (β₀ i) (β₀ j)
    have hr (x z : Site n) : 0≤D x z := (decay_pos ..).le
    have h k p : |Withdrawal.move w g s k * (Withdrawal.move v g s p * mixed (bolt p) (bolt k) S (g s))| ≤ A*A*C*d*M k*M p := by
      simp only [abs_mul]; apply (mul_le_mul (hu' k) (mul_le_mul (hu _) (hd p k i j).2 (abs_nonneg _) hA)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hA).trans_eq; change A*(A*(C*(d*M p*M k))) = _; ring
    apply (Finset.abs_sum_le_sum_abs ..).trans (le_trans (Finset.sum_le_sum fun _ _=>Finset.abs_sum_le_sum_abs ..) _)
    apply le_trans (Finset.sum_le_sum (fun k _=> Finset.sum_le_sum (fun p _=>h k p)))
    let V := ∑k:(ι ⊕ κ), M k
    have he : 0 ≤ V := Finset.sum_nonneg fun i _ => (decay_pos ..).le
    calc
      _ = A*A*C*d*(V*V) := by unfold V; rw [← mul_assoc (A*A*C*d)]; simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
      _ ≤ A*A*C*d*(P*P) := by have hz := hr (β₀ i) (β₀ j); have hx : V≤P := hm.count _ hp _; change 0 ≤ d at hz; exact mul_le_mul_of_nonneg_left (mul_le_mul hx hx he hP) (mul_nonneg (by positivity) hz)
      _ = _ := by unfold P d; ring
  let M k := D (β₀ i) (l k); let d := D (β₀ i) (β₀ j)
  have h k : |blade (bolt k) S (g s)*rise v w g s k| ≤ C*d*M k*B := by
    have he (z y : Site n) : 0≤ D z y := (decay_pos ..).le
    rw [abs_mul,mul_assoc C]
    apply mul_le_mul ((hd k k i j).1) (hv k) (abs_nonneg _) (mul_nonneg hC (mul_nonneg (he ..) (he ..)))
  apply le_trans (Finset.abs_sum_le_sum_abs ..)
  apply le_trans (Finset.sum_le_sum fun k _=> h k); simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hD := (decay_pos a (β₀ i) (β₀ j)).le
  have hz : ∑k:(ι ⊕ κ), M k ≤ P := hm.count _ hp _
  calc
    _ ≤ (C*d*P)*B := by change 0 ≤ d at hD; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (mul_nonneg hC hD)) hB
    _ = _ := by unfold d P; ring
end K

-- Using Envelope; bound directions after possibly contracting via repeat.
local notation "π" => Positions
lemma felt {l : ι→Site n} {h : κ→Site n} {g : π ι → π κ} {x : π ι} (he : Envelope l h a 2 g x C)
    (hG : ContDiffAt ℝ ω g x) (hL : Multiplicity l K) (hC : 0 ≤ C) (ha : 0<a) (v w : π ι)
    (hv : ‖v‖≤1) (hw : ‖w‖≤1) (i : κ) :
    ‖Withdrawal.move v g x i‖ ≤ C*space K a ∧ ‖rise v w g x i‖ ≤ C*space K a*space K a := by
  let D (j:ι) := Decay a (h i) (l j)
  have hd j : 0≤D j := (decay_pos ..).le
  let F (x : π ι) := g x i
  have hf : ContDiffAt ℝ ω F x := (contDiffAt_pi.mp hG) i
  have hA : ∑ j:ι,D j ≤ space K a := hL.count _ ha _
  constructor
  · let L := fderiv ℝ F x
    have hr j : ‖L (bolt j)‖ ≤ C * D j := (show ‖(fderiv ℝ F x) (bolt j)‖ ≤ _ from by
      rw [show (fderiv ℝ F x) (bolt j)=(fderiv ℝ g x) (bolt j) i from (turn _ hG _).symm]; simpa only
        [entry,iteratedFDeriv_one_apply,Matrix.cons_val_zero,glaze,spanSites,Fin.sum_univ_one,Decay,D] using he 1 (by decide) (by decide) ![j] i)
    change ‖L v‖ ≤ _; rw [by_row]; apply le_trans (norm_sum_le ..)
    apply le_trans (Finset.sum_le_sum fun j _ => show ‖v j • L (bolt j)‖ ≤ C*D j from by
      rw [norm_smul]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) ((norm_le_pi_norm v _).trans hv)) (hr j))
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hA hC
  let L := fderiv ℝ (fderiv ℝ F) x
  have ht (j k) : L (bolt j) (bolt k) = entry g x ![j,k] i := by
    let M := ContinuousLinearMap.proj (φ:=fun _ : κ=>ℝ) (R:=ℝ) i
    have hh := come (L:=M) (x:=x) (bolt j) (bolt k) _ hG
    rw [iter (bolt j) (bolt k) (show ContDiffAt ℝ ω (M ∘ g) x from hf),iter _ _ hG,iteratedFDeriv_two_apply] at hh
    rw [show L (bolt j) (bolt k)=M (iteratedFDeriv ℝ 2 g x ![bolt j,bolt k]) from hh]
    rw [show ![bolt j,bolt k] = fun s:Fin 2=>bolt (![j,k] s) from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)]; rfl
  have h j k : ‖L (bolt j) (bolt k)‖ ≤ C*D j*D k := by rw [ht,mul_assoc]; simpa [D,Decay,glaze,spanSites,Fin.sum_univ_succ,mul_add,Real.exp_add] using he 2 (by decide) le_rfl ![j,k] i
  rw [rise,iter _ _ hf,iteratedFDeriv_two_apply]; change ‖L v w‖ ≤ _; rw [decomposed]
  refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum fun j _=> ?_) (show ∑ j:ι,C*D j*space K a ≤ C*space K a*space K a from ?_))
  · rw [norm_smul]; refine (mul_le_of_le_one_left (norm_nonneg _) ((norm_le_pi_norm v _).trans hv)).trans ((norm_sum_le ..).trans ?_)
    apply le_trans (Finset.sum_le_sum (fun k _=> show ‖w k • L (bolt j) (bolt k)‖ ≤ C*D j*D k from by
      rw [norm_smul]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) ((norm_le_pi_norm w _).trans hw)) (h ..))); rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hA (mul_nonneg hC (hd _))
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]; gcongr; exact space_pos K ha

section Actual
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {t : S.Choices} {j N : ℕ} {χ : Clip} {R : PathData G} {μ C Λ : ℝ} {Q : KernelChoices}
variable (h : Push.Uniform.Before G μ C j Q N) (hK : Larger (G:=G) S) (hR : R.Bounds χ μ C Λ) (hJ : S.patch.J=j) (ht : S.kernel=Q)
variable (F t)
open Push
variable {g : Push.In G c→AxisChart G F} (he : Push.Uniform.Before.Service F h χ R g) (hk : 4 ≤ N)

abbrev carpet (h : Uniform.Before G μ C j Q N) (χ : Clip) (B : Patch) := h.tables χ B
-- bandwidth for graph H only: may spend on each product then use any for e^{-γ*n}
-- integration caller only, doesn't take any Delay result.
def glue (Z : ChartPrices) := min Z.width Z.rate
def stripe (Z : ChartPrices) (n) := space Z.coords (responseRate Z.coords n Z.value Z.width Z.gap)
abbrev guardU (P : ChartPrices) (n : ℕ) := curveCost P.coords P.value P.width P.gap 2 * stripe P n
abbrev guardV (P : ChartPrices) (n : ℕ) := guardU P n * stripe P n
def punch (P : ChartPrices) (n) := guardU P n*P.value*space P.coords P.width
def pint (P : ChartPrices) (n) := guardU P n*guardU P n*P.value*space P.coords P.width*space P.coords P.width + P.value*guardV P n*space P.coords P.width

abbrev trend (t : S.Choices) (χ : Clip) (R : PathData G) (g : Push.In G c→AxisChart G F) :=
    block (Push.Uniform.priced F t χ R) ∘ curve (Uniform.station g)
local notation "Y" => carpet h χ S.patch
include h hR hK hJ ht F t he hk
lemma current (v w : π (Primary c G)) (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    let L := address F G ∘ Sum.inr; let P := trend F t χ R g
    0<glue Y ∧ 0<(Y).gap ∧ 0≤punch Y N ∧ 0≤pint Y N ∧ Faces P 0 ∧ 0<(P 0).det ∧ Sealed L (glue Y) (P 0)⁻¹ ((Y).gap/2/2)⁻¹ ∧
      Sealed L (glue Y) (delta w P 0) (punch Y N) ∧
      Sealed L (glue Y) (delta v (delta w P) 0) (pint Y N) := by
  let A := address F G; let f₀ := Push.Uniform.priced F t χ R; let z := Uniform.station g; let Z := curve z; let τ := A ∘ (@Sum.inl (Primary c G) (Key F G))
  have hr := (h.receipt F t hR hK hJ ht).1
  have hx := he.series (Metric.mem_ball_self (x:=(0:Positions (Primary c G))) he.x_pos)
  have hH : ContDiffAt ℝ ω Z 0 := along hx
  have h0 : Z 0=0 := by
    have hz : z 0=0 := by unfold z Uniform.station; simp [he.critical.1]
    change meetVar _ _=0; rw [hz]; exact (partSpace _ _).symm.map_zero
  let d := responseRate (Y).coords N (Y).value (Y).width (Y).gap
  let u := curveCost (Y).coords (Y).value (Y).width (Y).gap 2
  have hu : 0≤u := le_trans zero_le_one (curveCost_ge hr _)
  have hd : 0<d := rate_pos hr
  have hp : 0<(Y).width := hr.pos_a
  have hy : 0≤(Y).value := hr.pos_C.le
  have hP := hr.born 0 (Metric.mem_ball_self hr.pos_r)
  obtain ⟨hF,hL,-⟩:= hr.priced_inverse 0 (Metric.mem_closedBall_self hr.reserveH_pos.le)
  have hl : 0<glue Y := lt_min hr.pos_a (tiltWidth_pos _ (half_pos hr.pos_m) hp hy)
  have hA : Envelope τ A d 2 Z 0 u := envelopes hr hx (he.pricing (Metric.mem_ball_self he.x_pos))
    (he.entered hR hK hJ ht (Metric.mem_ball_self he.x_pos) t) (by omega)
  have hh (v w : π (Primary c G)) (hv : ‖v‖≤1) (hw : ‖w‖≤1) := felt hA hH (hr.mult.comp Sum.inl_injective) hu hd v w hv hw
  have hY := hP
  change ContDiffAt ℝ ω f₀ 0 ∧ _ at hP
  have hK : Scatter A (Y).width N f₀ (Z 0) (Y).value := h0 ▸ hY.2
  let b := space (Y).coords (Y).width
  have hb : 0 ≤ b := space_pos _ hp
  have hM : 0 ≤ guardU Y N := mul_nonneg hu (space_pos _ hd)
  have hN : 0 ≤ guardV Y N := mul_nonneg hM (space_pos _ hd)
  obtain ⟨hm,h1,h2⟩:= borrowed hr.mult hp hy hK (h0.symm ▸ hP.1) hH hk v w hM hN (fun i=>(hh v v hv hv i).1)
    (fun i=>(hh w w hw hw i).1) (fun i=>(hh v w hv hw i).2)
  have hU : trend F t χ R g 0=block (Push.Uniform.priced F t χ R) 0 := by change block f₀ (Z 0)=_; rw [h0]
  have hG : 0≤punch Y N := mul_nonneg (mul_nonneg hM hy) hb
  have hΛ : 0≤pint Y N := add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hM hM) hy) hb) hb) (mul_nonneg (mul_nonneg hy hN) hb)
  have hgL := discount hL (inv_nonneg.mpr (half_pos (half_pos hr.pos_m)).le) (show glue Y ≤ (Y).rate from min_le_right ..)
  refine ⟨hl,hr.pos_m,hG,hΛ,hm,(by rw [hU]; exact hF),(by rw [hU]; exact hgL),discount h1 hG (min_le_left ..),discount h2 hΛ (min_le_left ..)⟩
end Actual
end YM.Further.PhysicalPeriodLimitF933.Enamel
