import YM.Analytic.Frame
import YM.Bid.Drops
import YM.Push.STATIONARY_UNIFORM.Travel
import YM.Work.F03.Flat


/-!
# The actual frame score and estimates with stage (pre-L) constants

Pre-L polynomial envelopes; *real* arguments. We do not adjoin independent
cover variables to take the jets. `framed` can take input chart directly in
fine/coarse variables and all patch scores can overlap and share arguments.

The gap to use in counting here is `2 / points²`, NOT `2 / points`.

Includes precise obstruction.

No change to normalization or representations
in consequence of this.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Exterior Pressure Gauge
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge}

section Coords

variable (P : Patch)

/-- Read root-fixed logs. -/
def readLog (i : P.Points) : P.FrameCoordinates G →L[ℝ] G.Color :=
  if h : i = P.center then 0 else
    (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j => PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) (⟨i,h⟩, j))

@[simp] lemma read_center (v : P.FrameCoordinates G) : readLog P P.center v = 0 := by simp [readLog]
lemma read_away {i : P.Points} (hi : i ≠ P.center) (v : P.FrameCoordinates G) (j : G.ColorIndex) :
    readLog P i v j = v (⟨i,hi⟩,j) := by unfold readLog; rw [dif_neg hi]; rfl

lemma frame_read (v : P.FrameCoordinates G) (i : P.Points) :
    P.frameFromCoordinates G v i = G.lieExp (readLog P i v) := by
  by_cases h : i = P.center
  · subst i; simp
  unfold Patch.frameFromCoordinates readLog; rw [dif_neg h,dif_neg h]; rfl

lemma frame_counting (v : P.FrameCoordinates G) :
    ‖v‖^2 = ∑ i, ‖readLog P i v‖^2 := by
  have he (i : {p : P.Points // p ≠ P.center}) (j) : v (i,j) = readLog P i.val v j :=
    (read_away P i.2 v j).symm
  rw [EuclideanSpace.real_norm_sq_eq v,Fintype.sum_prod_type]
  change ∑ i : {p : P.Points // p ≠ P.center}, ∑ j, v (i,j)^2 = _
  simp_rw [he, show ∀ x : G.Color, ∑ j, x j^2 = ‖x‖^2 from fun _ => (EuclideanSpace.real_norm_sq_eq _).symm]
  let f i := ‖readLog P i v‖^2
  rw [← Finset.sum_subtype (F:=inferInstance) (Finset.univ.erase P.center)
      (p:=fun i => i ≠ P.center) (by simp) f]
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ P.center)
  rw [show f P.center = 0 by simp [f], add_zero] at h; exact h

lemma read_short (G : Gauge) (i : P.Points) : ‖readLog P i (G:=G)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; rw [frame_counting P x]
  exact Finset.single_le_sum (f:=fun i => ‖readLog P i x‖^2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)

-- enumeration facts

def points := (Fintype.card P.Points : ℝ)
lemma points_pos : 0 < points P := by unfold points; positivity
lemma points_ge : 1 ≤ points P := by unfold points; exact_mod_cast (Fintype.card_pos (α:=P.Points))
lemma points_cost : points P = (((P.radius+P.radius+1:ℕ):ℝ))^4 := by
  unfold points Patch.Points; rw [Fintype.card_coe]
  unfold Patch.sites; rw [Pressure.box_length, Nat.cast_pow]
  congr 1
  unfold layers
  norm_cast
  rw [Int.card_Icc]; omega

lemma routeLe (x y : P.Points) (l : Lattice.Order) : (route x.val y.val l).length ≤ 8 * P.radius := by
  have he (i : Axis) : (straight i (y.val i-x.val i)).length ≤ 2*P.radius := by
    have h1 := (box_test.mp x.property).1 i; have h2 := (box_test.mp y.property).1 i
    have h3 := (box_test.mp x.property).2 i; have h4 := (box_test.mp y.property).2 i
    rw [straight,List.length_replicate]; omega
  have hL (w : List Axis) : (axisRoute x.val y.val w).length ≤ w.length*(2*P.radius) := by
    induction w with
    | nil => simp [axisRoute]
    | cons i j ih =>
      rw [show axisRoute x.val y.val (i::j) = straight i _ ++ axisRoute x.val y.val j from rfl,
        List.length_append,List.length_cons, Nat.add_mul]; have h := he i; omega
  have h : (route x.val y.val l).length ≤ 4*(2*P.radius) := by simpa [route,allAxes] using hL (allAxes l)
  omega
end Coords

section Score
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : Side} {U : E → Config G f} {r : Site f} (P : Patch)

def framed (r : Site f) (U : E → Config G f) (q : E × P.FrameCoordinates G) :=
  P.score (expandAt r (U q.1)) (P.frameFromCoordinates G q.2)

/-- Fix this cost on the gauge (pre-L). -/
def ExpReceipt (G : Gauge) (n : ℕ) (K : ℝ) : Prop :=
  ∀ x : G.Color, ‖x‖ ≤ 1 → Allows n (fun x : G.Color => G.mat (G.lieExp x)) x K
lemma exp_receipt (G : Gauge) (n : ℕ) : ∃ K : ℝ, 0<K ∧ ExpReceipt G n K := by
  obtain ⟨K,hK,he⟩ := exists_allows (isCompact_closedBall (0:G.Color) 1) (fun x _ => G.exp_jet.contDiffAt (x:=x)) n
  exact ⟨1+K,by positivity,fun x hx => (he x (by simpa using hx)).mono (le_add_of_nonneg_left zero_le_one)⟩

/-- Condition `C` bounds all per-link jets of the input U in its x
chart. -/
def scoreCost (G : Gauge) (n : ℕ) (K C : ℝ) :=
  let e := composeCost n K 1
  priceCost G (2^n * (2^n * e * travelCost G n (8*P.radius) (composeCost n C 1)) * e)

lemma framed_allows {K C : ℝ} {n : ℕ} (hK : ExpReceipt G n K) (p : E × P.FrameCoordinates G)
    (hh : ‖p‖ ≤ 1) (h : ∀ i, Allows n (fun y => G.mat (U y i)) p.1 C) :
    Allows n (framed P r U) p (scoreCost P G n K C) := by
  let T := P.FrameCoordinates G
  let F := ContinuousLinearMap.fst ℝ E T
  let S := ContinuousLinearMap.snd ℝ E T
  have hf : ‖F‖ ≤ 1 := F.opNorm_le_bound zero_le_one fun v => by rw [one_mul]; exact norm_fst_le v
  have hs : ‖S‖ ≤ 1 := S.opNorm_le_bound zero_le_one fun v => by rw [one_mul]; exact norm_snd_le v
  have hv (i : P.Points) : Allows n (fun z : E × T => G.mat (P.frameFromCoordinates G z.2 i)) p (composeCost n K 1) := by
    let R := readLog (G:=G) P i ∘L S
    have hr : ‖R‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_one₀ (read_short P G i) (norm_nonneg _) hs)
    have he : ‖R p‖ ≤ 1 := (R.le_opNorm p).trans (mul_le_one₀ hr (norm_nonneg _) hh)
    simp_rw [frame_read]
    exact (hK (R p) he).comp (f:=R) (allows_linear hr he)
  have hu (i) : Allows n (fun z : E × T => G.mat (U z.1 i)) p (composeCost n C 1) :=
    (h i).comp (f:=F) (allows_linear hf ((norm_fst_le p).trans hh))
  unfold framed Patch.score Patch.via; simp_rw [travel_at]
  apply allows_average (ι:=P.Points); intro i; apply allows_average (ι:=P.Points); intro j
  apply allows_average (ι:=Lattice.Order); intro l
  have hm := travel_jets (U:=fun z : E × T => U z.1) hu (wrap f i.val+r) (routeLe P i j l)
  exact Allows.price (f:=fun z => _) <| ((hv i).times (f:=fun z : E×T => _) (g:=fun z : E×T => _) hm).times
    (f:=fun z => _) (g:=fun z => _) ((hv j).inverse (f:=fun z => _))

open Work.F03

def pairBill (v w : P.FrameCoordinates G) :=
  (points P)⁻¹*((points P)⁻¹*∑ i : P.Points, ∑ j : P.Points,
    inner ℝ (readLog P i v-readLog P j v) (readLog P i w-readLog P j w))

omit [NormedSpace ℝ E] in
lemma frame_vertical (q : E × P.FrameCoordinates G) (hq : q=0) (hU : U 0=1) :
    let F := fun v : P.FrameCoordinates G => framed P r U (q.1,v)
    F 0=0 ∧ HasFDerivAt (𝕜:=ℝ) F 0 0 ∧ ∀ v w, iteratedFDeriv ℝ 2 F 0 ![v,w] = pairBill P v w := by
  subst q
  have he : expandAt r (U 0)=1 := by rw [hU]; rfl
  let e i (v : P.FrameCoordinates G) := G.lieExp (readLog P i v)
  let m (v : P.FrameCoordinates G) := framed P r U (0,v)
  let A i j (v : P.FrameCoordinates G) := G.price (e i v * (e j v)⁻¹)
  have hO : 0 < (Fintype.card Lattice.Order:ℝ) := by positivity
  have ht (v) : m v = (points P)⁻¹ * ((points P)⁻¹ * ∑ i : P.Points, ∑ j : P.Points, A i j v) := by
    unfold m framed Patch.score Patch.average
    simp_rw [he,Patch.via, Pressure.one, mul_one, frame_read,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,inv_mul_cancel_left₀ hO.ne',← Finset.mul_sum]; rfl
  have hf : ContDiffAt ℝ 2 m 0 := by
    simp_rw [funext ht]
    refine contDiffAt_const.mul (contDiffAt_const.mul (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_))
    apply (price_smooth (X:=P.FrameCoordinates G) (A:=fun v => e i v*(e j v)⁻¹) ?_).of_le le_top
    simp only [G.mat_mul,G.mat_inv]
    have hs (i : P.Points) : ContDiff ℝ ω (fun v : P.FrameCoordinates G => G.mat (e i v)) :=
      G.exp_jet.comp (readLog P i).contDiff
    exact (hs i).contDiffAt.mul (((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (hs j)).contDiffAt)
  have hy (v : P.FrameCoordinates G) (i j : P.Points) :=
    Work.F03.price_limit (V:=fun t : ℝ => e i (t • v)*(e j (t • v))⁻¹) (by simp [e]) (c:=readLog P i v-readLog P j v)
  have hlim (v : P.FrameCoordinates G) : Tendsto (fun t : ℝ => m (t • v) / t^2) (𝓝[≠] 0) (𝓝 (pairBill P v v / 2)) := by
    simp_rw [ht,pairBill,mul_div_assoc,Finset.sum_div]
    refine ((tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_).const_mul _).const_mul _
    simp_rw [real_inner_self_eq_norm_sq]; apply hy v i j
    simp only [G.mat_mul,G.mat_inv]
    have hD (i : P.Points) : HasDerivAt (fun t : ℝ => G.mat (e i (t • v))) (G.colorMat (readLog P i v)) 0 := by
      simp only [e,G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat (readLog P i v)) (0:ℝ)
    convert! (hD i).mul (hD j).star using 1
    simp [e, sub_eq_add_neg, colorMat_skew]
  have hadd (x y z : P.FrameCoordinates G) : pairBill P (x+y) z=pairBill P x z+pairBill P y z := by
    unfold pairBill; simp_rw [map_add,add_sub_add_comm,inner_add_left, Finset.sum_add_distrib,mul_add]
  have hs (v w : P.FrameCoordinates G) : pairBill P v w=pairBill P w v := by
    unfold pairBill
    refine congr_arg _ (congr_arg _ ?_)
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; exact real_inner_comm _ _
  obtain ⟨hh,h0,H⟩ := hessian_of_limit hf hlim hadd hs
  have h := (hf.differentiableAt (by simp)).hasFDerivAt; rw [h0] at h
  exact ⟨hh,h,H⟩

def rootGap := 2*(points P)⁻¹^2
lemma rootGap_pos : 0 < rootGap P := by unfold rootGap; have := points_pos P; positivity

lemma pairBill_gap (v : P.FrameCoordinates G) : rootGap P * ‖v‖^2 ≤ pairBill P v v := by
  let H (i j : P.Points) := ‖readLog P i v - readLog P j v‖^2
  have hc : ∑ j : P.Points, H P.center j=‖v‖^2 := by simp_rw [H, read_center, zero_sub,norm_neg]; exact (frame_counting ..).symm
  have he : ∑ i ∈ Finset.univ.erase P.center, H i P.center=‖v‖^2 := by
    have hz := Finset.sum_erase_add _ (fun i => H i P.center) (Finset.mem_univ P.center)
    rw [show H P.center P.center=0 by simp [H], add_zero] at hz
    rw [hz]; simp_rw [H,read_center, sub_zero]; exact (frame_counting ..).symm
  have h : ‖v‖^2+‖v‖^2 ≤ ∑ i, ∑ j, H i j := by
    conv_lhs => rw [← he]; rhs; rw [he,← hc]
    rw [← Finset.sum_erase_add _ (fun i => ∑ j, H i j) (Finset.mem_univ P.center)]
    exact add_le_add_left (Finset.sum_le_sum (fun i _ => Finset.single_le_sum
      (f:=H i) (fun j _ => sq_nonneg _) (Finset.mem_univ P.center))) _
  unfold rootGap pairBill; simp_rw [real_inner_self_eq_norm_sq]
  have hp := points_pos P
  apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)); exact le_of_eq (by ring)

end Score
end YM.Push.Uniform
