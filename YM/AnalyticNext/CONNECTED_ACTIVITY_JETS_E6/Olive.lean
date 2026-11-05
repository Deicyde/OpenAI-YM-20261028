import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Erosion
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lagoon
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rasura
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Turns

/-!
# Free branch smooth request with earned size even when b shell active

Actual unmasked $V$: cost only where crop selected. Use flat probing also
for argument smooth prices. Include χ writes separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Gate
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
open Brush  Frond Gate Scroll Metric
variable {v z r Q s : ℝ} {j : ℕ} {U : E → Config G c} {x : E}

private lemma all_whiteF (S : PathData G) (p : Clip) (R M) (a : Twin c) : plotted S p R M (1: Config G c) a=0 := by
  have he (n : ℕ) : shortenTerm S R M (1:Config G c) a.1 n=0 := by
    unfold shortenTerm; split
    next hv => simp [PathData.ellTerms, Work.F03.atSite_path,faceValue, SliceRows.trivial]
    exact rfl
  unfold plotted; split
  next => simp only [shorten,he,tsum_zero]
  simp [shoot,faceValue, SliceRows.trivial]
private lemma no_claim (h : P.Funds S T) (k : S.Choices) (i : Rod c f) (s : ℝ) : Scroll.freely T s 1 k i=0 := by
  unfold Scroll.freely baseStroke entryCost visual; rw [replica_one]
  have he (u : Twin c) : T.Xn (till s) (1 : Config G c) u=0 := all_whiteF ..
  rw [show S.prediction 1 k=(1:Config G c) from funext fun i=> Push.settled S (funds_branch h) i k]
  rcases i with i|i
  · simp only [Sum.elim,Tube.Xf,all_whiteF,canopyF,zip,he,map_zero,sum_const_zero,sub_zero]
  simp only [Sum.elim,canopyI,zip,Tube.Z,he,Pi.one_apply,inv_one,mul_one,G.curvature_unit,smul_zero,map_zero,sum_const_zero,sub_zero]

private lemma get_zero {k : ℕ} (q : E→Y) (p : E) (w b : ℝ) (hb : ‖p‖≤b) (hk : 1≤ k) (hT : q 0=0)
    (hv : ∀ x, ‖x‖≤b→ Brush k w 1 q x) : ‖q p‖≤w*‖p‖ := by
  have he (x) (h : x∈Metric.closedBall 0 b) := hv x (mem_closedBall_zero_iff.mp h)
  have hx : ∀ x∈Metric.closedBall 0 b, DifferentiableAt ℝ q x := fun i hi=> by
    have h : (1:WithTop ℕ∞) ≤ k := by exact_mod_cast hk
    exact (he i hi).smooth.differentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one h))
  have hg x (h : x∈closedBall 0 b) : ‖fderiv ℝ q x‖≤w := (norm_iteratedFDeriv_one _).symm.trans_le
    ((offer.1 (he _ h)).2 1 hk)
  simpa only [hT,sub_zero] using! (Convex.norm_image_sub_le_of_norm_fderiv_le hx hg (convex_closedBall _ _) (Metric.mem_closedBall_self ((norm_nonneg _).trans hb)) (mem_closedBall_zero_iff.mpr hb))

lemma beam (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) :
    ∃ (R:ℝ), 0<R ∧ ∃ (A : ℝ→ℝ), R≤1 ∧ Rate G L 0 A ∧ ∀ᶠ s : ℝ in atTop,
      ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T→ ∀ (k : S.Choices) (p : Rod c f),
      let g (v : ZipP G c f) := Scroll.freely T s (increment 1 v.1) k p
      ∀ x, ‖x‖≤R → Brush j (A s) 1 g x := by
  obtain ⟨r,v,hr,h1,hv,h⟩:= dressed P D hD j
  let f x:= shadowL P+maxima P L (till x); let g x:= hikeZ G v (till x) (dimLift P (till x) v)
  have hf : Rate G L 0 f := (Rate.const _).add (rateOfs P L (fun _=>shadowL P) (Rate.const _)).1
  let A x:= f x*(1+g x)^j
  refine ⟨r,hr,A,h1,by simpa only [zero_mul,add_zero] using! hf.mul (((Rate.const 1).add (raking P L v)).pow j),
    Eventually.of_forall fun x c f S T hs ht k p x' hX=>?_⟩
  obtain ⟨h₁,-,-,-,h₂⟩:= h _ _ S T ht.funds hs x' hX k
  exact (grove ht.funds ht.length_eq h₁ k h₂ p _).trim

lemma certifiedBranch (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) {v : ℝ→ℝ}
    (h : Rate G L (-(1/2)) v) (hp : ∀ᶠ x in atTop, 0≤v x) : ∃ F : ℝ→ℝ, Rate G L (-(1/2)) F ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D→ Works P L x S T→ ∀ (k:S.Choices) (p:Rod c f)
    (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ Config G c) (z:E), Mode U z j (v x)→
      Clean (U z) x (focus S p) (radiusB x) → Brush j (F x) 1 (fun t=> Scroll.freely T x (U t) k p) z := by
  let J:= j+3
  obtain ⟨R,hr,hV,hR,hv,hP⟩:= beam P L D hD J
  obtain ⟨F,hF,hG⟩:= base_ray P L j h hp
  let t := mist G L; let B x:= F x+ 3*t x
  have ht : Rate G L (-(1/2)) t := mist_rate G L
  have hi := ht.mul_left 3
  have ht' : Rate G L (1/2) (fun x=>(t x)⁻¹) := by simp only [t,mist,inv_inv]; exact Rate.power
  have hB : Rate G L (-(1/2)) B:= hF.add hi
  let Q x:=hV x*(3*t x); have hQ : Rate G L (-(1/2)) Q:= by convert hv.mul hi using 1; ring
  let P' x:=paidHull (t x) (B x) (Q x) (hV x)
  have hM: Rate G L (-(1/2)) P':=recover_price ht hB hQ hv (by norm_num) ht'
  let J' x:= F x+F x
  refine ⟨_,parseRate j hM (hF.add hF) (by norm_num) (show Rate G L (- -(1/2)) _ by rw [neg_neg]; exact ht'),?_⟩
  filter_upwards [softly G L,hG,hP,hB.below (by norm_num) R hr,room G P L] with
    x ht H H' hx hf c f S T hs hh k p E _ _ U z hU hE
  have hp:=hf c f S T hh; have hX:=hp.sight
  let W (x' : Config G c) := Scroll.freely T x x' k p
  let g (v:ZipP G c f):= W (increment 1 v.1)
  obtain ⟨d,b,hθ,hA⟩:= H.2 c f S T hh _ U z (radiusB x/4) _ hU (by omega) (hE.shrink (by rw [separation_self]; omega))
  let V' i := (b i,(0:Directions G f)); let A:= hV x
  have hY : Brush j (J' x) 1 V' z := Brush.pair hθ ((Brush.certified zero_le_one _).climb (show ‖(0:Directions G f)‖≤F x by rw [norm_zero]; exact H.1) le_rfl)
  have he : 0 < t x := ht.1; have hx' := (le_abs_self _).trans hx; have hv' : 3*t x ≤ B x := le_add_of_nonneg_left H.1
  have hr i (hi : i∈closedBall 0 (B x)) : Brush J A 1 g i := H' _ _ _ _ hs hh k p i ((mem_closedBall_zero_iff.mp hi).trans hx')
  have ho: (0:ZipP G c f)∈closedBall 0 (3*t x) := mem_closedBall_self (by positivity)
  have hh' : ‖V' z‖ ≤ F x := by unfold V'; apply max_le hθ.bound; rw [norm_zero]; exact H.1
  have h1 := (hr 0 (closedBall_subset_closedBall hv' ho)).nonneg
  have he := ascend (k:=J) (by unfold J; omega) (u:=Q x) (show 0≤A*(3*t x) by positivity) he (by linarith only [he,hv',hx',hR]) hv' h1 hr (fun y hy=> ?_) (V' z)
    (mem_closedBall_zero_iff.mpr (hh'.trans (le_add_of_nonneg_right (by positivity))))
  swap
  · refine (get_zero g _ A (B x) ((mem_closedBall_zero_iff.mp hy).trans hv') (k:=J) (by unfold J; omega)
      (by unfold g W; dsimp only [Prod.fst_zero]; simp only [Work.G07.at_zero_increment,no_claim hh.funds]) (fun i hi=> hr _ (mem_closedBall_zero_iff.mpr hi))).trans
        (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hy) h1)
  let F' := (G.adjoint (d (focus S p))⁻¹).toContinuousLinearMap
  have hg := ((scaled hY (he.smaller (show j≤J by unfold J; omega))).trim).report F' (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by
     rw [one_mul]; exact (G.norm_adjoint _ _).le)); rw [one_mul] at hg
  apply hg.shimmy
  filter_upwards [hA] with i hi
  have hv : W (gauge d (U i))=g (V' i) := by unfold W g W freely baseStroke; dsimp only [V']; rw [entry_stencil hp _ _ _ _ k p (replica_near hi) hi, shoreVisa hp p hi]
  change W _=G.adjoint _ (g (V' i)); rw [← hv]; unfold W
  rw [peony d hh.funds,← G.adjoint_mul, inv_mul_cancel, G.adjoint_one]
end YM.ConnectedActivityE6.Blaze.Gate
