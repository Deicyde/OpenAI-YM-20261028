import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Office
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Payments
import YM.AnalyticNext.QUARTIC_MATCH.Pre.Staged
import YM.Next.FOUNDATIONS.LinkBounds


/-!
# Per-site coarse bond estimates, centered prescription
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Knot Pre.Centered
open Joint Purse Logfee Village
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
namespace Depot
variable {G : Gauge} {c f : Side} (S : StepData c f) {ι : Type} [DecidableEq ι]
local notation "X" => JointSpace G c f
local notation "L" => S.patch.L
local notation "E" => G.Mat

omit [DecidableEq ι] in
/-- Transform ONLY affine arguments into ordinary log jets. -/
lemma lin_rate {E' F' G' : Type*} [NormedAddCommGroup E'] [NormedAddCommGroup F']
    [NormedAddCommGroup G'] [NormedSpace ℝ E'] [NormedSpace ℝ F'] [NormedSpace ℝ G']
    (k : E'→L[ℝ] F') (f : F'→G') (d : ι→ E') (h : ContDiffAt ℝ ω f 0) (T : Finset ι) :
    bill T d (f ∘ k) 0=bill T (k ∘ d) f 0 := by
  unfold bill; rw [Next.Foundations.jets_linear k (h.of_le le_top)]; rfl

lemma simple {X' Z : Type} [NormedAddCommGroup X'] [NormedAddCommGroup Z] [NormedSpace ℝ X'] [NormedSpace ℝ Z]
    (S : Finset ι) (d : ι→X') (L' : X'→L[ℝ] Z) (h : S.card ≠ 1) : bill S d L' 0 = 0 := by
  rcases Finset.eq_empty_or_nonempty S with H|H
  · rw [H,blank,L'.map_zero]
  induction S using Finset.induction_on with
  | empty => simp_all
  | insert i S hi ih =>
    rw [adjoin_budget hi _ _ L'.contDiff.contDiffAt,show Analysis.D (d i) L'=(fun _ => L' (d i)) from funext fun x => by rw [Analysis.D,L'.fderiv]]
    apply mute; rw [Finset.card_insert_of_notMem hi] at h; exact Finset.card_pos.mp (by omega)

lemma linearPay {X' Z : Type} [NormedAddCommGroup X'] [NormedAddCommGroup Z] [NormedSpace ℝ X'] [NormedSpace ℝ Z]
    (S : Finset ι) (d : ι→X') (P : Purse ι (Site c)) (L' : Site c→ X'→L[ℝ] Z)
    (ht : ∀ k, P.Pays {k} (fun i => L' i (d k)) 1) : P.Jets S d (fun i => L' i) 0 1 := by
  unfold Jets; by_cases h : S.card=1
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h
    simp_rw [alone d _ 0 ((L' _).contDiff.contDiffAt), Analysis.D, (L' _).fderiv]; exact ht i
  simp_rw [simple _ _ _ h]; exact Pays.zero zero_le_one

def Income (S : StepData c f) (P : Purse ι (Site f)) (d : ι→JointSpace G c f) : Prop :=
    Linkbill S.patch.L P (fun i => (d i).2.1) ∧ Linkbill 1 (Yard.cap S P) (fun i => (d i).1) ∧
    ∀ i, (Yard.cap S P).Pays {i} ((d i).2.2) 1

def coins (a : S.Choices) (x : Site c) (i : Axis) (z : X) := G.price (discrepancy S a z (x,i))
lemma coin_smooth (a : S.Choices) (h : S.patch.Branches S.kernel G) (i j) :
    ContDiffAt ℝ ω (coins S a i j (G:=G)) 0 := Work.F03.price_smooth (A:=fun z => discrepancy S a z (i,j)) (priced S a h (i,j))

set_option maxHeartbeats 500000 in
theorem pays (G : Gauge) (n j : ℕ) (η : ℝ) (hp : 0<η) : ∃ C : ℝ,0≤C ∧
    ∀ (ι : Type) [DecidableEq ι] (c f : Side) (S : StepData c f) (a : S.Choices),S.patch.J=j →
    S.patch.Branches S.kernel G → ∀ (P : Purse ι (Site f)) (v : ι→JointSpace G c f), tollRate P S.patch.L η →
    P.cap=(S.patch.L.val:ℝ)^2 → Income S P v → ∀ s : Finset ι,s.card ≤ n →
    ∀ i, (Yard.cap S P).Jets s v (fun x => coins S a x i) 0 C := by
  obtain ⟨C,hC,H⟩ := Yard.hires G n j η hp
  let U (x : G.Color) := G.mat (G.lieExp x)
  obtain ⟨D',hD,D⟩ := Purse.ordered U (0:G.Color) G.exp_jet.contDiffAt n 1
  let K := (2:ℝ)^n * (D' * ((2:ℝ)^n * (((2:ℝ)^n*(D'*C))*(Real.exp η^n*D'))))
  have hK : 0 ≤ K := by unfold K; positivity
  let q (x : G.Mat) := (2*G.colorScale^2)⁻¹ * ‖x-1‖^2
  have hq : ContDiffAt ℝ ω q 1 := contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp _ (contDiffAt_id.sub contDiffAt_const))
  obtain ⟨E',hE,Hq⟩ := Purse.ordered q 1 hq n K
  refine ⟨E',hE,?_⟩
  intro ι _ c f S a he h P v ht hv hL s hs i
  let c' := JointSpace G c f; let Z := Yard.cap S P
  let B y (x : c') := G.mat (discrepancy S a x (y,i))
  have hβ (y) : ContDiffAt ℝ ω (B y) 0 := priced S a h _
  have hU' (y : Site c) : B y 0=1 := by unfold B; rw [born S a h]; exact G.mat_one
  let A (p : Site c) := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Body 1 c => G.Color) (p,coord i)) ∘L ContinuousLinearMap.fst ℝ (Dir G c) (Vertical G c f)
  let Z' (p : Site c) : c' →L[ℝ] G.Color :=
    (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Site c=>G.Color) p ∘L
      ContinuousLinearMap.snd ℝ (Dir G f) (LieSpin G c)) ∘L
        ContinuousLinearMap.snd ℝ (Dir G c) (Vertical G c f)
  have hl {T : Finset ι} (hh : T.card ≤ n) (f : Site c→ c' →L[ℝ] G.Color) (h : ∀ k, Z.Pays {k} (fun i => f i (v k)) 1) :
      Z.Jets T v (fun y => U ∘ f y) 0 D' := alonePay (z:=fun y => _) (D _ _ Unit _ (fun y _ => f y) _ _ _ T hh
        (fun i _ => (f i).contDiff.contDiffAt) (fun i _ => map_zero (f i)) (fun p _ => energize (β:=Unit) (linearPay p v Z f h)))
  let M y (p : c') := G.mat (send S a p.2.1 (y,i))
  let J : G.Mat≃L[ℝ]G.Mat := starL ℝ
  let fx (y : Site c) := U ∘ Z' y
  have h1 (y) : ContDiffAt ℝ ω (fx y) 0 := (G.exp_jet.comp (Z' y).contDiff).contDiffAt
  have h2 (y) : ContDiffAt ℝ ω (M y) 0 := (send_smooth S h a (y,i)).comp (f:=fun p : c' => p.2.1) (0:c') (by fun_prop)
  have Hm (T) (hx : T.card ≤ n) : Z.Jets T v M 0 C := by
    let Ls := (ContinuousLinearMap.fst ℝ (Dir G f) (LieSpin G c)) ∘L ContinuousLinearMap.snd ℝ (Dir G c) (Vertical G c f)
    refine (H _ _ _ S a he h P (Ls ∘ v) ht hv hL.1 T hx i).under fun w => ?_
    exact (congr_arg (fun p : G.Mat => ‖p‖) (lin_rate Ls (fun x => G.mat (send S a x (w,i))) v (send_smooth S h a _) T)).le
  have Hf (T) (hx : T.card ≤ n) : Z.Jets T v fx 0 D' := hl hx Z' hL.2.2
  have Hf' (T) (hx : T.card ≤ n) : Z.Jets T v (fun y => fx (y+step i)) 0 (Real.exp η^n*D') := alonePay
    (Yard.relocation S (y:=i) hp ht n hx (Purse.energize (β:=Unit) (Hf _ hx)))
  let φ := ContinuousLinearMap.mul ℝ G.Mat
  let r y z := φ (fx y z) (M y z)
  let F y z := φ (r y z) (J (fx (y+step i) z))
  have hr (y) : ContDiffAt ℝ ω (r y) 0 := (h1 _).mul (h2 _)
  have hF (y) : ContDiffAt ℝ ω (F y) 0 := (hr _).mul (J.contDiff.contDiffAt.comp _ (h1 _))
  have Hb (T) (hx : T.card ≤ n) : Z.Jets T v r 0 (2^n*(D'*C)) := Jets.priced φ (fun _ _ => norm_mul_le ..) h1 h2
    (fun p hp => Hf _ ((Finset.card_le_card hp).trans hx)) (fun _ h => Hm _ ((Finset.card_le_card h).trans hx)) n hx
  have Hr (T) (hx : T.card ≤ n) : Z.Jets T v F 0 (2^n*((2^n*(D'*C))*(Real.exp η^n*D'))) := Jets.priced φ (fun _ _ => norm_mul_le ..) hr
    (fun i => (J.toContinuousLinearMap.contDiff.contDiffAt.comp _ (h1 _))) (fun _ hp => Hb _ ((Finset.card_le_card hp).trans hx)) (fun _ hp =>
      Jets.change_map (Hf' _ ((Finset.card_le_card hp).trans hx)) _ (fun y => h1 (y+step _)) (fun a => (norm_star a).le)) n hx
  have HP (T) (hx : T.card ≤ n) : Z.Jets T v B 0 K := by
    rw [show B=(fun i a => φ (U (A i a)) (J (F i a))) from funext fun y => funext fun q => by
      simp only [B,discrepancy,represent_link,Lattice.gauge,G.mat_mul,G.mat_inv]; rfl]
    have hh k : Z.Pays {k} (fun y => A y (v k)) 1 := by
      have hi := hL.2.1 k (coord i); change Z.Pays {k} _ ((↑(1:ℕ):ℝ))⁻¹ at hi
      rw [Nat.cast_one,inv_one] at hi; exact hi
    exact Jets.priced φ (fun _ _ => norm_mul_le ..) (fun i => (G.exp_jet.comp (A i).contDiff).contDiffAt) (fun i => J.toContinuousLinearMap.contDiff.contDiffAt.comp _ (hF _))
      (fun _ h => hl ((Finset.card_le_card h).trans hx) A hh) (fun _ hp => Jets.change_map (Hr _ ((Finset.card_le_card hp).trans hx)) _ hF (fun a => (norm_star a).le)) n hx
  rw [show (fun x : Site c => coins S a (G:=G) x i)=fun y => q ∘ B y from funext fun i => funext fun u => exp_price ..]
  exact alonePay (z:=fun i => _) (Hq _ _ Unit _ (fun i _ => B i) _ _ _ s hs (fun i _ => hβ i) (fun i _ => hU' i) (fun i hi => Purse.energize (β:=Unit) (HP i ((Finset.card_le_card hi).trans hs))))
end Depot
end YM.AnalyticNext.QuarticMatch.Estimate
