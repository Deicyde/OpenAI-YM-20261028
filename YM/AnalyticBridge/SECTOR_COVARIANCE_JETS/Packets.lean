import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Stead
import YM.Push.FREE_RESOLVENT.Growth


set_option warningAsError false

/-!
# Measure the jet currency with normalized directions & finite differences

No tacit volume factor from a norm of B. Convert complete atom Bills
to direction estimates even under `t'*(1+d)^P` pricing. These are
ordinary derivatives (true left exp chart, components fixed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d ε C r : ℝ}
variable {ι κ α : Type*} [Fintype ι] [Fintype κ]
variable {p : ι → Site c} {q : κ → Site c} {A : Directions G c → Matrix ι κ ℝ} {B : Directions G c}

private lemma straight (l : List α) (v : α → Directions G c)
    (h : ContDiffAt ℝ l.length A B) :
    let L : (Atom G c → ℝ) ≃L[ℝ] Directions G c := gaugeCount
    jet (fun i => L.symm (v i)) (fun y => A (B+L y)) l 0 = jet v A l B := by
  intro L; unfold jet; erw [Next.Foundations.jets_linear L.toContinuousLinearMap
    (f:=fun y => A (B+y)) (show ContDiffAt ℝ l.length (fun y => A (B+y)) 0 from
      ContDiffAt.comp 0 (f:=fun y => B+y) (g:=A) (by simpa only [add_zero]) (contDiffAt_const.add contDiffAt_id))]
  simp [iteratedFDeriv_comp_add_left,Function.comp_def]

-- The t'-normalized derivative prices, no C in the hypothesis besides
-- the slot-by-slot prices; use also for errors needing TWO small factors.
lemma spendDirection (o : Site c) (P : ℕ) (v : α → Directions G c) (l : List α)
    (h : ContDiffAt ℝ l.length A B) (hp : 0≤C) (hd : 0<d) (he : 0≤ε)
    (hh : ∀ i∈l, ∀ e, ‖v i e‖ ≤ ε*hill (native c) o P e.1)
    (hf : ∀ w : Fin l.length → Atom G c, Bill (meterMark G c d) (native c) p q (List.ofFn w) σ C
      (jet atom A (List.ofFn w) B)) :
    Bill (radial α (native c) o P) (native c) p q l σ (sparkCount G (d/2)^l.length *
      ((ε*polynomial (d/2) P)^l.length*C)) (jet v A l B) := by
  let L : (Atom G c → ℝ) ≃L[ℝ] Directions G c := gaugeCount
  let F y := A (B+L y)
  let u (i) := L.symm (v i)
  rw [← straight l v h]
  have hx : ContDiffAt ℝ l.length F 0 := slide_smooth L.toContinuousLinearMap B 0 (by simpa only [map_zero,add_zero])
  refine activated u hx (d:=d) (fun w => ?_) hp he ?_ (half_pos hd) (by linarith) (volume_atom _ (half_pos hd) c G)
  · have ht : (fun i : Atom G c => Pi.single i (1:ℝ))=(fun i : Atom G c => L.symm (atom i)) :=
      funext fun i => (L.symm_apply_apply (Pi.single i 1)).symm
    rw [ht]; rw [show jet _ F _ _ = _ from straight (List.ofFn w) atom (A:=A) (B:=B) (by simpa)]
    exact hf w
  intro i hi e
  change ‖componentG (G:=G) e.2 (v i e.1)‖ ≤ _
  refine ((componentG (G:=G) _).le_opNorm _).trans (le_trans ?_ (hh i hi e.1))
  exact mul_le_of_le_one_left (norm_nonneg _) (tint_price _)

lemma energyDirections (h : RatesPaid p q σ C k A B) (o : Site c) (P : ℕ) (v : α → Directions G c) (l : List α)
    (hp : 0 ≤ C) (hd : 0<σ) (he : 0≤ε) (hl : l.length ≤ k) (hh : ∀ i∈l, ∀ e, ‖v i e‖ ≤ ε * hill (native c) o P e.1) :
    Bill (radial α (native c) o P) (native c) p q l σ (sparkCount G (σ/2)^l.length *
      ((ε*polynomial (σ/2) P)^l.length*C)) (jet v A l B) :=
  spendDirection _ _ _ _ (smooth_of_le h.smooth hl) hp hd he hh fun w => h.bound _ (by rwa [List.length_ofFn])

lemma costSlope {A : Directions G c → Matrix ι κ ℝ} (h : RatesPaid p q σ C k A B) (hk : 1 ≤ k) (hC : 0 ≤ C) (hs : 0 < σ)
    (X : Directions G c) :
    (native c).Schur p q σ (sparkCount G (σ/2)*(‖X‖*C)) (fderiv ℝ A B X) := by
  let v (_ : Unit) := X
  have ht := energyDirections h (o:=0) 0 v [()] hC hs (norm_nonneg X) hk (fun i hi e => by
    unfold hill v; rw [pow_zero,mul_one]; exact norm_le_pi_norm ..)
  have he : jet v A [()] B = fderiv ℝ A B X := by
    rw [jet_step v () [] (smooth_of_le h.smooth hk), show jet v A []=A from funext (zeroth v A)]
    rfl
  rw [he] at ht
  have hr i := ht.row.rows i
  have hl j := ht.col.rows j
  constructor <;> constructor <;> intro i
  · simpa only [payment,hill,List.length_cons,List.length_nil,Nat.zero_add,polynomial,pow_zero,one_pow,
      mul_one,one_mul,inv_one,pow_one] using hr i
  simpa only [payment,hill,List.length_cons,List.length_nil,Nat.zero_add,polynomial,pow_zero,one_pow,
    mul_one,one_mul,inv_one,pow_one] using hl i

/-- Simple *uniform* finite fluctuation-price in the real logarithm
neighborhood (no 1/period in the chart radius!). -/
lemma fluctuate (hC : 0≤C) (hs : 0<σ) (hk : 1≤k) (Z N : ℝ) (hp : (native c).Volume p (σ/2) Z)
    (hq : (native c).Volume q (σ/2) N) (B B' : Directions G c) (he : ‖B‖ ≤ r) (he' : ‖B'‖ ≤ r)
    (h : ∀ b, ‖b‖ ≤ r → RatesPaid p q σ C k A b) :
    let V := max Z N
    let M := sparkCount G (σ/2)
    (native c).Schur p q (σ/2) (V*((M*C)*‖B'-B‖)) (A B'-A B) := by
  intro V M
  have hh : 0≤M := spark_nn ..
  let s := Metric.closedBall (0:Directions G c) r
  have hv (i j) : ‖A B' i j - A B i j‖ ≤ ((native c).weight (-σ) (p i) (q j)*(M*C))*‖B'-B‖ := by
    let v (X) := A X i j
    have hf b (hb : b ∈ s) := h b (by simpa [s] using hb)
    have ht b (hb : b∈s) : DifferentiableAt ℝ A b := ((smooth_of_le (hf b hb).smooth hk).differentiableAt (by simp))
    have hx b (hb : b∈s) : HasFDerivAt v (evaluate i j ∘L fderiv ℝ A b) b :=
      (evaluate i j).hasFDerivAt.comp b (ht b hb).hasFDerivAt
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (hf:=fun b hb => (hx b hb).differentiableAt)
    · intro b hb; rw [(hx b hb).fderiv]
      let u := (native c).weight (-σ) (p i) (q j)
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ((native c).weight_nn ..) (mul_nonneg hh hC)); intro z
      change |fderiv ℝ A _ _ _ _| ≤ _
      exact ((costSlope (hf b hb) hk hC hs z).rows.point i j).trans_eq (by unfold M; ring)
    · exact convex_closedBall ..
    · exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right])
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right])
  have hw : 0 ≤ M*C*‖B'-B‖ := by positivity
  apply Cost.Schur.of_point hw (σ:=σ)
  · intro i j; rw [← mul_assoc]; exact hv i j
  · rw [show σ-σ/2 = σ/2 by ring]; exact hq.le (le_max_right ..)
  rw [show σ-σ/2 = σ/2 by ring]; exact hp.le (le_max_left ..)
end YM.AnalyticBridge.Covariance
