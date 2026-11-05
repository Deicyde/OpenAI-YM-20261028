import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.Next.EXTRACTION.Tails


/-!
# Uniform open small-field domain for the no-hole affine tests

For use as an extra producer beyond the flat Taylor price. First localize
the branch hypotheses themselves by comparison to a single finite BUT
sufficiently large reference period. Only post-L. All connector choices can
be held simultaneously and the *same frames* are used on both sides of the
connector. Here no holes anywhere; both perturbed (coarse AND fine) positive
arrays are uniformly small globally in the same trivialization.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Bloch Laurent Exterior Precision Tree Bid Filter Function Set Metric
  FreeResolvent Affine View Lifted Work.F08
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {f c f' c' : Side} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {h : f.val=c.val*P.L.val} {h' : f'.val=c'.val*P.L.val}

private lemma area_large (r : ℕ) : 1 < (area r).val := by change 1 < 2*r+2; omega

section watch
variable {R : ℕ} {p : pair G c f} {p' : pair G c' f'} {o : Site c} {o' : Site c'}
  {k : (data h K).Choices} {k' : (data h' K).Choices}
  (hc : 1<c.val) (hc' : 1<c'.val) (H : Reads p p' h h' K o o' R)
include hc hc' H
private def watching (p : pair G c f) (y : Site c) :=
    expandAt ((data h K).ratio.embed y) (unwrapped (data h K) p)

lemma frame_paths {z : Cover} (hx : size z+View.reach P ≤ R) (a b : P.Points) (l : Lattice.Order) :
    travel (watching (h:=h) (K:=K) p (addr o z)) a.val (route a.val b.val l)=
      travel (watching (h:=h') (K:=K) p' (addr o' z)) a.val (route a.val b.val l) := by
  unfold watching; rw [travel_at, travel_at, ground, ground]
  exact H.march hc hc' _ _ _ ((frame_cost P a b l z).trans hx)

lemma usesMin_here {z : Cover} (hx : size z+View.reach P ≤ R) (hp' : Watch (data h' K) k' p') :
    P.usesMin K (expandAt ((data h K).ratio.embed (addr o z)) (unwrapped (data h K) p)) := by
  have hp := hp'.1 (addr o' z)
  change P.usesMin K (watching _ _)
  simp only [Patch.usesMin,Patch.via,Patch.axial,frame_paths hc hc' H hx]
  exact hp

lemma same_frame (z : Cover) (hb : P.Branches K G) (hx : size z+View.reach P ≤ R) (hp' : Watch (data h' K) k' p') :
    (data h K).frames (unwrapped (data h K) p) k.1 (addr o z)=(data h' K).frames (unwrapped (data h' K) p') k'.1 (addr o' z) := by
  let U := watching p (addr o z) (h:=h) (K:=K); let V := watching p' (addr o' z) (h:=h') (K:=K)
  have hh (w : P.Frame G) : P.score U w=P.score V w := by simp only [U,V,Patch.score,Patch.average,Patch.via,frame_paths hc hc' H hx]
  have hU := (P.min_exists U).choose_spec
  have hw : P.minimizing V (P.selected U) := ⟨hU.1,fun h he => by rw [← hh,← hh]; exact hU.2 h he⟩
  have hu : P.usesMin K U := usesMin_here hc hc' H hx hp'
  have hv : P.usesMin K V := hp'.1 _
  change P.frame K U _ = P.frame K V _
  unfold Patch.frame; rw [if_pos hu, if_pos hv]
  exact (hb.frame_unique V hv).unique hw (P.min_exists V).choose_spec

lemma usesBest_here (hb : P.Branches K G) {z : Cover} (hx : size z+View.reach P+1 ≤ R) (hp' : Watch (data h' K) k' p') (i : Axis) :
    P.usesBest K ((data h K).connector (unwrapped (data h K) p) k.1 (addr o z,i)) := by
  let V := unwrapped (data h K) p; let W := unwrapped (data h' K) p'
  have hh : (data h K).connector V k.1 (addr o z,i)=(data h' K).connector W k'.1 (addr o' z,i) := by
    funext w
    unfold StepData.connector
    have hz : size (z+step i) ≤ size z+1 := (size_add ..).trans (Nat.add_le_add_left (by simp [size,apply_ite Int.natAbs]) _)
    rw [travel_at,travel_at]; dsimp only
    have shift (c : Side) (t : Site c) : addr t z+step i=addr t (z+step i) := by simp [addr,add_assoc]
    simp only [shift]
    rw [same_frame hc hc' H z (k:=k) hb (by omega) hp', same_frame hc hc' H (z+step i) (k:=k) hb (by omega) hp',ground,ground]
    congr 2
    have ht : size (z+carry (0:Site P.L) w.val) ≤ size z+haze P := (size_add ..).trans
      (Nat.add_le_add_left ((carry_size ..).trans (Finset.le_sup (f:=fun i : P.Points => size i.val) (Finset.mem_univ w))) _)
    exact H.march hc hc' _ _ (List.replicate P.L.val (posDir i)) (by rw [List.length_replicate]; unfold View.reach at hx; omega)
  change P.usesBest K ((data h K).connector V k.1 (addr o z,i)); rw [hh]; exact hp'.2 _
end watch

lemma holdWatch (P : Patch) (G : Gauge) (K : KernelChoices) (hb : P.Branches K G) : ∃ r : ℝ, 0 < r ∧
    ∀ {c f : Side} {h : f.val=c.val*P.L.val} (_ : 1<c.val) (k : (data h K).Choices) (z : pair G c f), ‖z‖ < r → Watch (data h K) k z := by
  let R := View.reach P+2; let S := refStep P K R; let t := Classical.arbitrary S.Choices
  have hw := watches S t hb
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp hw
  refine ⟨r,hr,?_⟩; intro c f h hc k z hz
  have h' (y : Site c) := transported R y z (G:=G) (h:=h) (K:=K)
  have H y : Watch S t ((sheet G R h K y) z) := he (by
    rw [mem_ball,dist_zero_right]
    exact lt_of_le_of_lt (((sheet G R h K y).le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg _) (transported_size ..))) hz)
  refine ⟨fun y => ?_,fun ⟨y,i⟩ => ?_⟩
  · have hh := usesMin_here hc (area_large R) (h' y) (z:=0) (by unfold R; simp [size]) (H y)
    simpa only [addr,map_zero,add_zero,Lifted.data] using! hh
  have hh := usesBest_here hc (area_large R) (h' y) (k:=k) hb (z:=0) (by unfold R; simp [size]) (H y) i
  simpa only [addr,map_zero,add_zero,Lifted.data] using! hh

section regions
variable {α β X E : Type*} [Fintype α] [Fintype β] [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma local_costs (F : α → E → β → ℝ) (k : ℕ) (hF : ∀ i, ContDiffAt ℝ ω (F i) 0) : ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
    ∀ x : E, ‖x‖ < r → ∀ i, ContDiffAt ℝ ω (F i) x ∧ ∀ b j, j ≤ k → ‖iteratedFDeriv ℝ j (fun y => F i y b) x‖ ≤ C := by
  let f i b (j : Fin (k+1)) := ‖iteratedFDeriv ℝ j.val (fun y => F i y b) 0‖
  let C := (∑ i, ∑ b, ∑ j : Fin (k+1), f i b j)+1
  have h i b j : f i b j < C := by
    unfold C; apply lt_add_of_le_of_pos _ zero_lt_one
    exact (Finset.single_le_sum (f:=f i b) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      ((Finset.single_le_sum (f:=fun b => ∑ j, f i b j) (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f:=fun i => ∑ b, ∑ j, f i b j) (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))) (Finset.mem_univ i)))
  have hx (i b) (j : Fin (k+1)) := ((contDiffAt_pi.mp (hF i) b).continuousAt_iteratedFDeriv le_top).norm.tendsto.eventually (ge_mem_nhds (h i b j))
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp ((eventually_all.mpr (fun i => (hF i).eventually (by simp))).and
    (eventually_all.mpr fun i => eventually_all.mpr fun b => eventually_all.mpr fun j => hx i b j))
  exact ⟨r,C,hr,by unfold C f; positivity,fun x hx i =>
    ⟨(he (mem_ball_zero_iff.mpr hx)).1 i,fun b j hj => (he (mem_ball_zero_iff.mpr hx)).2 i b ⟨j,Nat.lt_succ_of_le hj⟩⟩⟩

omit [Fintype α] in
lemma transferred {r C : ℝ} (F : α → E → β → ℝ) {k : ℕ} (L : X →L[ℝ] E) (h : ‖L‖ ≤ 1)
    (hp : ∀ x : E, ‖x‖ < r → ∀ i, ContDiffAt ℝ ω (F i) x ∧ ∀ b j, j ≤ k → ‖iteratedFDeriv ℝ j (fun y => F i y b) x‖ ≤ C)
    (i : α) (b : β) (x : X) {f : X → ℝ} (hx : ‖x‖ < r) (he : f =ᶠ[𝓝 x] fun y => F i (L y) b) :
    ContDiffAt ℝ ω f x ∧ ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  obtain ⟨h0,hy⟩ := hp (L x) (((L.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) h)).trans_lt hx) i
  have hh := contDiffAt_pi.mp h0 b; exact ⟨(hh.comp _ L.contDiff.contDiffAt).congr_of_eventuallyEq he,fun j hj => by
    rw [(he.iteratedFDeriv ..).eq_of_nhds, show (fun y => F i (L y) b) = (fun y => F i y b) ∘ L from rfl, WardBin.Lies.liner L (hh.of_le le_top)]
    exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le .. |>.trans
      ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => h))).trans (hy b j hj))⟩
end regions
end YM.SelectedOrderedKernels.Small
