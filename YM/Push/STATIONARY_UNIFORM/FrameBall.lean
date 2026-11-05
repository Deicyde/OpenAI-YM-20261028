import YM.Laurent.Rune
import YM.Next.FOUNDATIONS.Primary
import YM.Push.STATIONARY_UNIFORM.BranchJets
import YM.Push.STATIONARY_UNIFORM.FrameMin
import YM.Push.STATIONARY_UNIFORM.Vertical

/-!
# Uniform extension of the native frame branch

Input ball in norm on `E` (`Push.In` uses sup), vertical ball in *counting*.
The proof is not by transferring a continuity radius after picking a volume.
Works also on arbitrary real finite-dimensional input charts at these costs (e.g.
relative copies on other edges); no choosing a representation of the patches.
Use candidate  shared outcomes.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Pressure Gauge
open Next.Fluctuations Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : Side}

/-- Variation price and jets of the literal fine links, Frobenius on G.mat. -/
def Inputs (U : E → Config G f) (n : ℕ) (C : ℝ) := U 0=1 ∧ 0≤C ∧
  ∀ e x, ‖x‖ ≤ 1 → Allows n (fun z => G.mat (U z e)) x C

namespace Inputs
variable {U : E → Config G f} {r : Site f} (P : Patch) {C : ℝ} {n : ℕ}

def variation (G : Gauge) (C : ℝ) := C/G.colorScale

lemma chord (h : Inputs U n C) (hn : 1 ≤ n) {x : E} (hx : ‖x‖ ≤ 1) (i : Bond f) :
    G.chord (U x i) ≤ variation G C * ‖x‖ := by
  let A (x) := G.mat (U x i)
  have he : ‖A x-A 0‖ ≤ C*‖x-0‖ := by
    apply (convex_closedBall (0:E) 1).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
      (fun x hx => ((h.2.2 i x (by simpa using hx)).analytic.differentiableAt (by simp)))
      _ (mem_closedBall_self zero_le_one) (by simpa using hx)
    intro x hx
    rw [← norm_iteratedFDeriv_one A]; exact (h.2.2 i x (by simpa using hx)).norm_le _ hn
  rw [sub_zero, show A 0=1 by simp [A,h.1], show ‖A x-1‖=_ from (chord_dist (U x i)).symm] at he
  apply le_of_mul_le_mul_left _ G.colorScale_pos; rw [← mul_assoc, variation, mul_comm G.colorScale (C/G.colorScale),div_mul_cancel₀ _ G.colorScale_pos.ne']; exact he

def pathChange (G : Gauge) (P : Patch) (C : ℝ) := 1 + 8*P.radius*variation G C

lemma path_pos (G : Gauge) (hc : 0≤C) : 0 < pathChange G P C := by unfold pathChange variation; have := G.colorScale_pos; positivity

lemma closes (h : Inputs U n C) (hn : 1 ≤ n) {x : E} (hx : ‖x‖ ≤ 1) :
    ClosePaths P (expandAt r (U x)) (pathChange G P C*‖x‖) := by
  have ht := G.colorScale_pos
  have he : 0 ≤ variation G C := div_nonneg h.2.1 ht.le
  intro i j l
  rw [travel_at]; apply le_trans (travel_chord _ _ _ _ (h.chord hn hx))
  rw [← mul_assoc]; unfold pathChange
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply le_trans _ (le_add_of_nonneg_left zero_le_one); gcongr
  exact_mod_cast routeLe P i j l
end Inputs

variable {U : E → Config G f} (P : Patch) {r : Site f} {n : ℕ} {K C D δ : ℝ} {Q : KernelChoices}

/-- Hilbert log radius (also used on x variable here as vertical-comparison bound). -/
def hilbertRadius := fun G n K C => min 1 (rootGap P / (2 * (1+scoreCost P G n K C)))

/-- Explicit powers/costs, can pay even when growing L (gauge and KernelChoices data before L).
Min to simplify hierarchies, all legs at worst inverse-polynomial L at fixed n, J. -/
def frameRadius (G : Gauge) (n : ℕ) (K C D δ : ℝ) (Q : KernelChoices) :=
  let R := hilbertRadius P G n K C
  let J := Inputs.pathChange G P C
  let A := alignCost P*J
  min R (min (Q.frame_cut/(3*J)) (min (δ/A) (R/(points P*D*A))))

-- using full n here to match analytic implicit calls. Pay smaller m C optional.
lemma hilbert_supply (hU : Inputs U n C) (hK : ExpReceipt G n K) (_hn : 3 ≤ n) (r : Site f) :
    let R := hilbertRadius P G n K C; let m := scoreCost P G n K C
    0 < R ∧ R ≤ 1 ∧ m * R ≤ rootGap P/2 ∧
    ∀ x ∈ ball 0 R, Allows n (framed P r U) x m := by
  let m := scoreCost P G n K C
  have H (p : E × P.FrameCoordinates G) (hp : ‖p‖ ≤ 1) := framed_allows P (r:=r) hK p hp
    (fun i => hU.2.2 i p.1 ((norm_fst_le _).trans hp))
  let R := hilbertRadius P G n K C; have hr : R ≤ 1 := min_le_left ..
  have hm : 0≤m := (H 0 (by simp)).nonneg; have hc := rootGap_pos P
  have he : R ≤ rootGap P / (2*(1+m)) := min_le_right ..
  refine ⟨lt_min one_pos (div_pos hc (show 0<2*(1+m) by positivity)),hr, ?_, fun x hx => H x ((show ‖x‖<R by simpa using hx).le.trans hr)⟩
  change m*R ≤ _
  apply le_trans (mul_le_mul_of_nonneg_left he hm)
  have hM : 0 < 2*(1+m) := by positivity
  rw [← mul_div_assoc]; apply (div_le_iff₀ hM).mpr; linarith

lemma frame_radius_pos (hU : Inputs U n C) (hK : ExpReceipt G n K) (hn : 3 ≤ n)
    (r : Site f) (hL : LogReceipt G D δ) (Q : KernelChoices) :
    0 < frameRadius P G n K C D δ Q := by
  unfold frameRadius
  have hp := (hilbert_supply P hU hK hn r).1
  have hv := Inputs.path_pos P G hU.2.1
  have he := align_pos P
  exact lt_min hp (lt_min (div_pos Q.frame_cut_pos (by positivity))
    (lt_min (div_pos hL.2.1 (by positivity)) (div_pos hp (mul_pos (mul_pos (points_pos P) hL.1) (by positivity)))))

lemma selects (hU : Inputs U n C) (hK : ExpReceipt G n K) (hn : 3 ≤ n) (hL : LogReceipt G D δ) {x : E}
    (hx : x ∈ ball 0 (frameRadius P G n K C D δ Q)) :
    let R := hilbertRadius P G n K C; let a := Inputs.pathChange G P C
    P.usesMin Q (expandAt r (U x)) ∧ ∀ u, P.minimizing (expandAt r (U x)) u →
      let q := ofFrame P u
      (P.frameFromCoordinates G q = u ∧ ‖q‖ ≤ points P*D*(alignCost P*a)*‖x‖) ∧
      q∈ball 0 R ∧ HasFDerivAt (fun q => framed P r U (x,q)) (0:P.FrameCoordinates G →L[ℝ] ℝ) q := by
  let R := hilbertRadius P G n K C
  let a := Inputs.pathChange G P C
  let Y := alignCost P*a
  have hy' : ‖x‖ < min R (min (Q.frame_cut/(3*a)) (min (δ/Y) (R/(points P*D*Y)))) := by
    change ‖x‖ < frameRadius P G n K C D δ Q
    simpa only [mem_ball,dist_zero_right] using hx
  simp only [lt_min_iff] at hy'
  have hp := Inputs.path_pos P G hU.2.1; have hm := align_pos P
  have ha : 0 < a := hp
  have hY : 0 < Y := mul_pos hm ha
  obtain ⟨_,he,_,h⟩ := hilbert_supply P hU hK hn r
  have hT := Inputs.closes P (r:=r) hU (le_trans (by norm_num) hn) (hy'.1.le.trans he)
  refine ⟨minimizing_used P hT Q ?_,?_⟩
  · have hd := (lt_div_iff₀ (show 0<3*a by positivity)).1 hy'.2.1
    change 3*(a*‖x‖)<_
    linarith
  intro u hu
  obtain ⟨h₁,h₂⟩ := minimizing_writes P hL hu hT <| by
    have he := (lt_div_iff₀ hY).1 hy'.2.2.1
    change alignCost P*(a*‖x‖) ≤ δ
    unfold Y at he; linarith
  let q := ofFrame P u
  have hv : ‖q‖ ≤ points P*D*Y*‖x‖ := h₂.trans (le_of_eq (by unfold Y a; ring))
  have hr : ‖q‖ < R := hv.trans_lt (by rw [mul_comm]; exact (lt_div_iff₀ (mul_pos (mul_pos (points_pos P) hL.1) hY)).1 hy'.2.2.2)
  refine ⟨⟨h₁,hv⟩,by simpa using hr, ?_⟩
  let m (v : P.FrameCoordinates G) := framed P r U (x,v)
  have hz : IsLocalMin m q := Filter.Eventually.of_forall fun i => by
    change P.score _ _ ≤ P.score _ _; rw [show P.frameFromCoordinates G q = u from h₁]
    exact hu.2 _ (P.frameFromCoordinates_center _ _)
  have hh : ContDiffAt ℝ ω (framed P r U) (x,q) := (h _ (by simpa [Prod.norm_def] using And.intro hy'.1 hr)).analytic
  have hf : ContDiffAt ℝ ω m q := hh.comp (f:=fun i => (x,i)) q (contDiffAt_const.prodMk contDiffAt_id)
  rw [← hz.fderiv_eq_zero]; exact (hf.differentiableAt (by simp)).hasFDerivAt

def branchLog (r : Site f) (U : E → Config G f) (x : E) := ofFrame P (P.selected (expandAt r (U x)))

lemma frame_strong (hU : Inputs U n C) (hK : ExpReceipt G n K) (hn : 3 ≤ n) (r : Site f) :
    let R := hilbertRadius P G n K C
    Strong (framed P r U) 0 (rootGap P) ∧ ∀ x∈ball 0 R, Strong (framed P r U) x (rootGap P/2) := by
  obtain ⟨hp,hx,hv,h⟩ := hilbert_supply P hU hK hn r
  have ha : AnalyticAt ℝ (framed P r U) 0 := ((h _ (mem_ball_self hp)).analytic).analyticAt
  have hb : Strong (framed P r U) 0 (rootGap P) := by
    intro v
    have he : vertical (framed P r U) 0 v v = pairBill P v v := by
      change fderiv ℝ (YM.Analytic.slope (framed P r U)) 0 (0,v) v = _
      rw [YM.Analytic.slope_prime _ _ ha]; exact (frame_vertical (r:=r) P 0 rfl hU.1).2.2 v v
    rw [he]; exact pairBill_gap P v
  exact ⟨hb, fun x hx i => le_trans (mul_le_mul_of_nonneg_right (by linarith only [hv]) (sq_nonneg _))
    (hb.near hp (fun x hx => (h x hx).order hn) hx i)⟩

lemma onlyFrame (hU : Inputs U n C) (hK : ExpReceipt G n K) (hn : 3 ≤ n)
    {x : E} (hx : x∈ball 0 (hilbertRadius P G n K C)) {v w : P.FrameCoordinates G}
    (hv : v∈ball 0 (hilbertRadius P G n K C)) (hw : w∈ball 0 (hilbertRadius P G n K C))
    (hj : HasFDerivAt (fun q => framed P r U (x,q)) (0:P.FrameCoordinates G →L[ℝ] ℝ) v)
    (hi : HasFDerivAt (fun q => framed P r U (x,q)) (0:P.FrameCoordinates G →L[ℝ] ℝ) w) : v=w := by
  obtain ⟨hp,_,hh,h⟩ := hilbert_supply P hU hK hn r
  let R := hilbertRadius P G n K C
  have hf (i) (hi : i∈ball 0 R) := YM.Analytic.sliceDrv (framed P r U) (x,i) ((h _ (by
    simp only [mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff] at hx hi ⊢; exact ⟨hx,hi⟩)).analytic.differentiableAt (by simp))
  exact (frame_strong P hU hK hn r).1.unique hp (fun x hx => (h x hx).order hn) (hh.trans_lt (half_lt_self (rootGap_pos P))) hx hv hw (((hf v hv).unique hj).trans (hi.unique (hf w hw)))

variable [FiniteDimensional ℝ E]

lemma branch_jets (hU : Inputs U (n+1) C) (hK : ExpReceipt G (n+1) K) (hn : 2 ≤ n) (hL : LogReceipt G D δ) {x : E}
    (hx : x∈ball 0 (frameRadius P G (n+1) K C D δ Q)) :
    Allows n (branchLog P r U) x (implicitCost 1 (scoreCost P G (n+1) K C) ((rootGap P/2)⁻¹) n) := by
  have ha : 3 ≤ n+1 := by omega
  let R := hilbertRadius P G (n+1) K C
  let I := frameRadius P G (n+1) K C D δ Q
  let F := framed P r U
  let b := branchLog P r U
  have hr : I ≤ R := min_le_left ..
  obtain ⟨hP,hR,hv,h⟩ := hilbert_supply P hU hK ha r
  have hf (x) (hx : x∈ball 0 I) : b x∈ball 0 R ∧ HasFDerivAt (fun v => F (x,v)) (0 : P.FrameCoordinates G →L[ℝ] ℝ) (b x) :=
    ((selects (r:=r) P hU hK ha hL hx).2 (P.selected _) (P.min_exists _).choose_spec).2
  have hs (x : E) (i : P.FrameCoordinates G) (hx : x∈ball 0 I) (hi : i∈ball 0 R) : (x,i)∈ball (0:E×P.FrameCoordinates G) R := by
    have he : ‖x‖<R := (show ‖x‖<I by simpa using hx).trans_le hr
    simpa [Prod.norm_def,he] using hi
  let v := (x,b x)
  have hh := hf x hx
  have he := hs _ _ hx hh.1
  have hol := (h _ he).analytic
  have hpos := (frame_strong P hU hK ha r).2 v he
  have hed := div_pos (rootGap_pos P) (show (0:ℝ)<2 by norm_num)
  have hu : ContDiffAt ℝ ω b x := by
    have hhA : AnalyticAt ℝ F v := hol.analyticAt
    obtain ⟨g,hg,hH,H⟩ := YM.Analytic.param F v hhA hh.2 fun u Hu => by
      rw [← YM.Analytic.slope_prime _ _ hhA]; exact (mul_pos hed (pow_pos (norm_pos_iff.mpr Hu) _)).trans_le (hpos u)
    apply hH.contDiffAt.congr_of_eventuallyEq
    have ht : g ⁻¹' ball 0 R ∈ 𝓝 x := hH.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (hg.symm ▸ hh.1))
    filter_upwards [isOpen_ball.mem_nhds hx,ht,H] with i hi hj hk
    exact onlyFrame P hU hK ha (ball_subset_ball hr hi) (hf i hi).1 hj (hf i hi).2 hk
  let m := scoreCost P G (n+1) K C
  have he' : ‖x‖ ≤ 1 := ((show ‖x‖ < I by simpa using hx).le.trans hr).trans hR
  refine implicit_jets (g:=YM.Analytic.slope F) n he' ((show ‖b x‖<R by simpa using hh.1).le.trans hR) ?_ hu (allows_slope (f:=F) (h _ he)) (inv_pos.mpr hed).le ?_
  · filter_upwards [isOpen_ball.mem_nhds hx] with i hi
    exact (YM.Analytic.sliceDrv F (i,b i) ((h _ (hs _ _ hi (hf i hi).1)).analytic.differentiableAt (by simp))).unique (hf i hi).2
  intro u
  have h := hpos.invert u
  change ‖u‖ ≤ (rootGap P/2)⁻¹ * ‖vertical F v u‖
  rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ hed,mul_comm]; exact h

section Native
omit [FiniteDimensional ℝ E]
variable {c : Side} (S : StepData c f) (y : Site c)



/-- Input to the native estimates, c,f,L arbitrary. Use with uniform cost. -/
lemma represented (h : ExpReceipt G n K) : ∀ m : Side, Inputs (E:=In G m) represent n (composeCost n K 1) := by
  intro m
  have hu (e : Bond m) (x : In G m) (hx : ‖x‖ ≤ 1) : Allows n (fun z => G.mat (represent z e)) x (composeCost n K 1) := by
    let L : In G m →L[ℝ] G.Color := ContinuousLinearMap.proj (e.1,Exterior.coord e.2)
    have hh : ‖L x‖ ≤ 1 := (norm_le_pi_norm x _).trans hx
    simp_rw [Work.F03.represent_link]
    exact (h _ hh).comp (f:=L) (allows_linear (L.opNorm_le_bound zero_le_one (fun y => by rw [one_mul]; exact norm_le_pi_norm y _)) hh)
  exact ⟨link_one,(hu (Classical.arbitrary _) 0 (by simp)).nonneg,hu⟩
end Native
end YM.Push.Uniform
