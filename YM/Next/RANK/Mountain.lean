import Mathlib.Analysis.Calculus.Taylor
import YM.Bid.Loan
import YM.Next.RANK.Ray



/-!
# Operator norm receipts on all scales of the actual positive link germ

Use the same resolvent argument as G02, but obtain the quantitative higher derivative
bounds here by comparing to **one** continuous-path operator independent of both the
link location and the supplied `Hol G`. Thus the polynomial Φ stencil is admissible at
these specific charged k. This theorem is about the physical Hol.O, no assuming a
uniform power series radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function ContinuousLinearMap MvPolynomial Normal RG Source Labels Wilson Lattice Beamer CellsInt Filter Set MeasureTheory Asymptotics Drops
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {n d b : ℕ}

-- hide inference of dimension-dependent op norm diamond across phases, always Frobenius data
abbrev slopeCap {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] (i : ℕ) (F : U → V) (x : U) : ℝ := ‖iteratedFDeriv ℝ i F x‖

section
variable {V E Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
private lemma roots (a : V) (G : V→L[ℝ] Q) (j : ℕ) : ∃ k : ℝ, 0≤k ∧ ∀ (L : E→L[ℝ] V→L[ℝ] V) (f : E → V), (∀ x,a+L x (f x)=f x) →
    ∀ b : ℝ, 0 ≤ b → (∀ x v, ‖L x v‖ ≤ b*‖x‖*‖v‖) → AnalyticAt ℝ (G∘f) 0 ∧ slopeCap j (G∘f) 0 ≤ k*b^j := by
  let X:= (V→L[ℝ] V)
  let F (U : X):=G (Ring.inverse (1-U) a)
  let k:= slopeCap j F 0
  have hp : AnalyticAt ℝ F 0 := by
    let U:= ContinuousLinearMap.apply ℝ V a
    have he := U.analyticAt (Ring.inverse (1-0:X))
    exact (G.analyticAt _).comp (he.comp (f:=fun x : X => Ring.inverse (1-x)) (analyticAt_inverse_one_sub ℝ X))
  refine ⟨k,norm_nonneg _,fun L u h b hb ht => ?_⟩
  have hL : ‖L‖ ≤ b := opNorm_le_bound _ hb fun x => opNorm_le_bound _ (mul_nonneg hb (norm_nonneg _)) fun v => (ht x v).trans_eq (by ring)
  have h : (F ∘ L) =ᶠ[𝓝 0] G ∘ u := by
    have hh : Tendsto L (𝓝 0) (𝓝 0):=by simpa using L.continuous.tendsto 0
    filter_upwards [hh.eventually (Metric.ball_mem_nhds _ zero_lt_one)] with x hx
    have hv : IsUnit (1 - (L x)) := isUnit_one_sub_of_norm_lt_one (by simpa using hx)
    have h₁ : (1-L x) (u x)=a := by change u x - L x (u x)=_; rw [sub_eq_iff_eq_add]; exact (h x).symm
    dsimp only [Function.comp_apply,F]; rw [← h₁,← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hv, one_apply_eq_self]
  have h₀ : L 0=0 := map_zero L
  refine ⟨?_,?_⟩; · exact ((show AnalyticAt ℝ F (L 0) from h₀ ▸ hp).comp (L.analyticAt _)).congr h
  have hh : ‖iteratedFDeriv ℝ j (G∘u) 0‖ ≤ k*‖L‖^j := by
    have hd : ContDiffAt ℝ j F (L 0) := h₀ ▸ hp.contDiffAt
    obtain ⟨r,hr,hu⟩ := Metric.mem_nhds_iff.mp (hd.eventually (by simp))
    have hk : L 0∈ Metric.ball (L 0) r := Metric.mem_ball_self hr
    have hz : ContDiffOn ℝ j F (Metric.ball (L 0) r) := fun x hx => (show ContDiffAt ℝ j F x from hu hx).contDiffWithinAt
    have ht : IsOpen (L ⁻¹' Metric.ball (L 0) r):= Metric.isOpen_ball.preimage L.continuous
    have he := L.iteratedFDerivWithin_comp_right hz Metric.isOpen_ball.uniqueDiffOn ht.uniqueDiffOn hk le_rfl
    rw [iteratedFDerivWithin_of_isOpen _ ht (show 0∈L ⁻¹' Metric.ball (L 0) r from hk), iteratedFDerivWithin_of_isOpen _ Metric.isOpen_ball hk,map_zero] at he
    rw [← (h.iteratedFDeriv ℝ j).eq_of_nhds, he]; apply ContinuousMultilinearMap.norm_compContinuousLinearMap_le .. |>.trans; simp [k]
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L) hL _) (norm_nonneg _))
end
section
variable (Z : Type*) [NormedRing Z] [NormedAlgebra ℝ Z] [CompleteSpace Z]
private abbrev S (R : Type*) [TopologicalSpace R] := C(unitInterval,R)

-- Z₂ primitives private; restate the integral operator to pin its quantitative bound here
private def slide  : S Z →L[ℝ] S Z := by
  let m:= projIcc (0:ℝ) 1 zero_le_one
  have hp (x : S Z) (a b : ℝ) : IntervalIntegrable (fun s=> x (m s)) volume a b := (x.continuous.comp continuous_projIcc).intervalIntegrable (μ:=volume) a b
  let L : S Z →ₗ[ℝ] S Z := {
    toFun U := ⟨fun t => ∫ s in 0..(t:ℝ), U (m s), (intervalIntegral.continuous_primitive (hp U) 0).comp continuous_subtype_val⟩
    map_add' x y := ContinuousMap.ext fun t => intervalIntegral.integral_add (hp x 0 t) (hp y 0 t)
    map_smul' v x := ContinuousMap.ext fun t => by
      change (∫ s in 0..(t:ℝ), v • x (m s))=v • ∫ s in 0..(t:ℝ), x (m s); rw [intervalIntegral.integral_smul] }
  refine L.mkContinuous 1 fun U => ?_
  rw [one_mul]; refine (ContinuousMap.norm_le _ (norm_nonneg U)).2 fun t => ?_
  change ‖∫ s in 0..(t:ℝ), U (m s)‖ ≤ ‖U‖
  calc
    _ ≤ ‖U‖* |(t:ℝ)-0| := intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => U.norm_coe_le_norm _
    _ ≤ _ := by rw [sub_zero,abs_of_nonneg t.property.1]; exact mul_le_of_le_one_right (norm_nonneg _) t.property.2

private def air  : S Z→L[ℝ] S Z→L[ℝ] S Z :=
    ((ContinuousLinearMap.compL ℝ (S Z) _ _) (slide Z)).comp (ContinuousLinearMap.mul ℝ (S Z)).flip

-- exact equation on Banach path space, yield a single germ expansion whose constants
-- only involve Z.rep etc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
private lemma ordinary (j : ℕ) : ∃ K : ℝ,0 ≤ K ∧ ∀ (f : E →ₗ[ℝ] ℝ → Z) (u : E → ℝ → Z),
    (∀ x, Continuous (f x)) → (∀ x, u x 0=1) → (∀ x t,HasDerivAt (u x) (u x t * f x t) t) → ∀ c : ℝ, 0 ≤ c →
      (∀ x,∀ t : unitInterval,‖f x t.val‖ ≤ c*‖x‖) →
        AnalyticAt ℝ (fun x => u x 1) 0 ∧ ‖iteratedFDeriv ℝ j (fun x=> u x 1) 0‖ ≤ K*c^j := by
  let A: S Z→L[ℝ] Z:=ContinuousMap.evalCLM ℝ (1:unitInterval)
  let r:= ‖slide Z‖; have hr : 0≤r:=norm_nonneg (slide Z)
  obtain ⟨k,hk,H⟩ := roots (E:=E) (1:S Z) A j
  refine ⟨k*r^j,by positivity,?_⟩
  intro f u hF ht hu c hc' hc
  let U : E →ₗ[ℝ] S Z := {
    toFun x := ⟨fun t => f x t.val,(hF x).comp continuous_subtype_val⟩
    map_add' x y := ContinuousMap.ext fun t=> congr_fun (f.map_add x y) t.val
    map_smul' r x := ContinuousMap.ext fun t=> congr_fun (f.map_smul r x) t.val }
  let L := (air Z).comp U.toContinuousLinearMap
  have hh (J) : Continuous (u J) := continuous_iff_continuousAt.2 fun t=> (hu J t).continuousAt
  let W (J : E) : S Z := ⟨fun t=>u J t,(hh J).comp continuous_subtype_val⟩
  have h (J) : 1+L J (W J)=W J := by
    have hK := ht J
    apply ContinuousMap.ext; intro t
    let π := projIcc (0:ℝ) 1 zero_le_one
    change 1+(∫ s in 0..(t:ℝ), u J (π s).val * f J (π s).val)=u J t
    rw [intervalIntegral.integral_congr (g:=fun s => u J s * f J s) (fun s hs => ?_),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hu J s) (((hh J).mul (hF J)).intervalIntegrable _ _), show u J 0 = 1 from hK]
    · abel
    rw [Set.uIcc_of_le t.property.1] at hs
    dsimp only; have hp : (π s).val=s := by dsimp only [π]; rw [projIcc_of_mem _ (show s∈unitInterval from ⟨hs.1, hs.2.trans t.property.2⟩)]
    rw [hp]
  have he x v : ‖L x v‖ ≤ (r*c)* ‖x‖ * ‖v‖ := by
    change ‖slide Z (v * U x)‖≤ _
    have hs : ‖U x‖ ≤ c * ‖x‖ := (ContinuousMap.norm_le _ (by positivity)).2 (hc x)
    apply ((slide Z).le_opNorm _).trans
    apply (mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg v))) hr).trans_eq; ring
  obtain ⟨hp,hb⟩ := H L W h _ (by positivity) he
  exact ⟨hp, hb.trans_eq (show k*(r*c)^j = _ by ring)⟩
end

private def source (d : ℕ) (e : Edge Cover) (J : Snap G d) (t : ℝ) := partConnection d (expand d J) 1 e t
private lemma source_cont (d : ℕ) (e : Edge Cover) (J : Snap G d) : Continuous (source d e J) := by
  unfold source partConnection; simp only [potential,one_smul]
  apply continuous_finsetSum _; intro k _; exact (Tensor.diag_smooth _ 1).continuous.comp (by fun_prop)

private def loft (d : ℕ) (e : Edge Cover) : Snap G d→ₗ[ℝ] ℝ→G.Mat where
      toFun x t := G.colorMat (source d e x t)
      map_add' x y := funext (fun t => by
        change G.colorMat _=G.colorMat _+ G.colorMat _; rw [← map_add]; congr 1; dsimp only [source,partConnection]
        simp only [potential,one_smul, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i hi=> ?_
        simp only [expand,dif_pos (Finset.mem_range.mp hi)]; rfl)
      map_smul' r x := funext (fun t => by
        change G.colorMat _=r • G.colorMat _; rw [← map_smul]; congr 1; dsimp only [source,partConnection]; simp only [one_smul,potential, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi=>?_ ; simp only [expand,dif_pos (Finset.mem_range.mp hi)];rfl)
private lemma loft_norm (G : Gauge) (d b : ℕ) (e : Edge Cover) (hp : e.1∈box b) (V : Snap G d) (x : unitInterval) : ‖loft (G:=G) d e V x.val‖ ≤ G.colorScale*(d-1:ℕ)*(4*(b:ℝ)+1)^d * ‖V‖ := by
  have hg := G.colorScale_pos
  change ‖G.colorMat _‖≤_
  rw [G.colorMat_norm]; simp only [source,partConnection,one_smul,potential]
  let X := mapZ e.1 + (x:ℝ) • YM.basis e.2
  let r : ℝ := 4*(b:ℝ)+1
  have hz : 1≤r := by dsimp only [r]; simp
  have hv : ‖X‖≤r := by
    have hx : ‖mapZ e.1‖ ≤ (Beamer.street e.1:ℝ) := by
      have he : mapZ e.1=∑ i : Axis,(e.1 i:ℝ) • basis i := by ext1 i; simp [mapZ, apply_ite]
      rw [he]; apply (norm_sum_le ..).trans; simp only [norm_smul,basis_norm,mul_one,Real.norm_eq_abs,← Int.cast_abs, Int.abs_eq_natAbs,Int.cast_natCast,street,Nat.cast_sum]; exact le_rfl
    have he : ‖(x:ℝ) • YM.basis e.2‖≤1 := by rw [norm_smul,Real.norm_of_nonneg x.property.1,YM.basis_norm,mul_one]; exact x.property.2
    have hB : (street e.1:ℝ) ≤ 4*(b:ℝ) := by exact_mod_cast bounded hp
    exact (norm_add_le ..).trans (add_le_add (hx.trans hB) he)
  calc
    _ ≤ G.colorScale*∑ i∈Finset.range (d-1),‖(expand d V i).value e.2 X‖ := mul_le_mul_of_nonneg_left (norm_sum_le ..) hg.le
    _ ≤ G.colorScale*∑ i∈Finset.range (d-1), (‖V‖*r^d) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hg.le
      let j : Fin (d-1) := ⟨i,Finset.mem_range.mp hi⟩
      change ‖Taylor.value _ _ _‖ ≤ _; rw [expand,dif_pos j.isLt]
      let a := (V j).val e.2
      have he : ‖a‖≤‖V‖ := le_trans (norm_le_pi_norm (V j).val _) (norm_le_pi_norm V j)
      refine (show ‖a (fun _ => X)‖ ≤ _ from a.le_opNorm (fun _ => X)).trans ?_
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; refine mul_le_mul he ((pow_le_pow_left₀ (norm_nonneg _) hv _).trans (pow_le_pow_right₀ hz ?_)) (pow_nonneg (norm_nonneg _) _) (norm_nonneg V)
      have := j.isLt; omega
    _ = _ := by rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; unfold r; ring

-- positive oriented locations; unit support size b. output in matrix op norm
lemma windage (H : Hol G) (d j : ℕ) : ∃ C : ℝ, ∃ v : ℕ, 0≤C ∧ ∀ b : ℕ, ∀ e : Edge Cover, e.1∈box b →
    let X := fun J : Snap G d => G.mat (H.links d (expand d J) 1 e)
    AnalyticAt ℝ X 0 ∧ slopeCap j X 0 ≤ C*(1+(b:ℝ))^v := by
  obtain ⟨C,hC,HF⟩ := ordinary (E:=Snap G d) G.Mat j
  let k:= G.colorScale*(d-1:ℕ)
  have hk : 0 ≤ k := mul_nonneg G.colorScale_pos.le (Nat.cast_nonneg _)
  refine ⟨C*(k*(4:ℝ)^d)^j,d*j,by positivity,fun b e he => ?_⟩
  let a:= k*(4*(b:ℝ)+1)^d; let f:= loft d e (G:=G)
  let u (x : Snap G d) (t : ℝ) := G.mat (H.flow d (expand d x) 1 e t)
  have h (x : Snap G d) := H.solves d (expand d x) 1 e
  obtain ⟨hp,hb⟩ := HF f u (fun x=> G.colorMat.continuous_of_finiteDimensional.comp (source_cont _ _ _))
    (fun x=> by unfold u; rw [(h x).1,G.mat_one]) (fun x t=> (h x).2 t) a (by dsimp only [a]; positivity) (fun x t => loft_norm G d b e he x t)
  refine ⟨hp,hb.trans ?_⟩
  have hx : a ≤ k*(4:ℝ)^d*(1+(b:ℝ))^d := by
    unfold a; rw [mul_assoc k,← mul_pow]; apply mul_le_mul_of_nonneg_left _ hk; gcongr; linarith only
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold a; positivity) hx _) hC).trans_eq (by rw [pow_mul,mul_assoc (C),mul_pow])
end YM.Next.Rank.Spindle
