import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Accounts
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Match


set_option warningAsError false

/-!
# The same weak-branch chart on the frozen annulus

The chart on a held Y link is patched (`Held`), not a true log except
on the appropriate stencils. Buy agreement on those by the *local*
Wide comparisons (enlarging d if needed). `angles` applies where the
compulsory guards are nonzero. No reliance on a nonlocal Allocation
support condition. No requirement on noise partition-plateau k
away from the record. Smoothness of the selected noise branch (for
`Match`) bought at the same local comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree Metric
  YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Motion
open YM.SectorNext.Remainder.Affine
open YM.SectorNext
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (x : ℝ) (V : Config G c) (O A : Stores S) (F : Forest S.ratio) (k : S.Choices)
    (q : Chi) (J : ChartRatio G) (d : ℝ) (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) (D : ℕ)

private lemma back (U : Config G f) (i : Bond f) (s : Signed) (h : Directions G f)
    (hh : pull s 0 U i = increment (replica S.ratio (pull s 0 V)) h i) :
    let j := sendEdge s 0 i; let W := replica S.ratio V
    ∃ v : G.Color, ‖v‖ = ‖h i‖ ∧ U j = G.lieExp v * W j ∧
      ∀ e : Directions G f, e j=v → inChannel s W e i = h i := by
  intro j W
  rw [increment,← replica_turn,turn_read,turn_read] at hh
  cases he : s.flip i.2
  · refine ⟨_,rfl,?_,?_⟩
    · simpa only [he,Bool.false_eq_true,↓reduceIte] using hh
    intro e hx; rw [in_eval,if_neg (by rw [he]; decide)]
    exact hx
  · refine ⟨-G.adjoint (W j) (h i),by rw [norm_neg,G.norm_adjoint],?_,?_⟩
    · have hv : (U j)⁻¹ = G.lieExp (h i) * (W j)⁻¹ := by simpa only [he,↓reduceIte] using hh
      rw [exp_negative,exp_adjoint]
      calc
        U j = ((U j)⁻¹)⁻¹ := by group
        _ = _ := by rw [hv]; group
    intro e hx; rw [in_eval,if_pos he,hx,LinearMap.neg_apply,map_neg,neg_neg,← G.adjoint_mul, inv_mul_cancel, G.adjoint_one]

private lemma same_small {a b : G.Color} (ha : ‖a‖<firstRadius G) (hb : ‖b‖<firstRadius G)
    (he : G.lieExp a=G.lieExp b) : a=b :=
  calc
    a = _ := (over_ball (by simpa only [firstBall,mem_ball,dist_zero_right] using ha)).symm
    _ = b := by rw [he,over_ball (by simpa only [firstBall,mem_ball,dist_zero_right] using hb)]

private lemma keep_angle (j : Bond f) (v : G.Color) (h : ‖v‖ ≤ d) (hd : 0<d) (hr : 2*d < firstRadius G)
    (he : physical A F V Y (tape a) j = G.lieExp v * replica S.ratio V j)
    (hj : S.ratio.parent j.1 ∈ O.dome ((D+104)*radiusB x))
    (hh : jacob J q d (openAt O A D x F) (tape a) ≠ 0) : theta x V A F q d Y a j=v := by
  have hp : d < firstRadius G := by linarith
  have hl := h.trans_lt hp
  let W := replica S.ratio V
  let u := returned A F V Y (tape a)
  change F.drape u j=_*W j at he
  by_cases hy : j∈F.trunks
  · rw [show W j=1 from if_pos (F.trunk_internal hy),mul_one,show F.drape u j=1 from F.on_tree u ⟨_,hy⟩] at he
    have hv : v=0 := same_small hl (by rw [norm_zero]; linarith) (by rw [← he,G.mat_lieExp_zero])
    rw [hv]; simp [theta,Rows.input,Rows.fresh,hy]
  let n : F.Free := ⟨j,hy⟩
  rw [show F.drape u j=u n from F.off_tree u n] at he
  by_cases hg : chill A x F n
  · let b : Frozen A x F := ⟨n,hg⟩
    change freeze .. = _ at he; rw [freeze_held (cold:=chill A x F) (j:=b)] at he
    have hx : autoShell q d V Y b=v := by
      unfold autoShell; rw [he]; change patched q d ((G.lieExp v*W j)*(W j)⁻¹)=v
      rw [mul_inv_cancel_right,patched_agrees q hd hp h]
    change chill A x F ⟨j,hy⟩ at hg
    unfold theta Rows.input Rows.fresh; simp only [Pi.add_apply,dif_pos hy,dif_pos hg,dif_neg (not_not.mpr hg),add_zero]; exact hx
  let b : Active A x F := ⟨n,hg⟩
  change freeze .. = _ at he
  rw [freeze_regular (cold:=chill A x F) (j:=b)] at he
  change G.lieExp (tape a b)*W j=_ * W j at he
  have ho : b∈openAt O A D x F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.ratio.parent j.1, by simp [Next.SectorChange.points,b,n],hj⟩
  have hx : tape a b=v := same_small ((jacob_keeps _ _ _ _ _ _ ho hd hh).trans hr) hl (mul_right_cancel he)
  change ¬ chill A x F ⟨j,hy⟩ at hg
  unfold theta Rows.input Rows.fresh; simp only [Pi.add_apply,dif_pos hy,hg,dif_pos,not_false_eq_true,dif_neg,zero_add]; exact hx

/-- Even on every thin patch of the annulus caller, the requested a are
the actual displacements read by the Gaussian reference. -/
theorem angles (s : Signed) (p : Site c) (C : ℝ) (hB : 1 ≤ radiusB x)
    (hd : 0<d) (hr : 2*d < firstRadius G) (hc : C*fiery G x S.patch.L ≤ d)
    (hp : p∈(turnStore s O).dome (D*radiusB x))
    (hh : jacob J q d (openAt O A D x F) (tape a) ≠ 0) :
    let U := physical A F V Y (tape a)
    ∀ h : Directions G f, PatchInputs (S:=S) (pull s 0 U) (pull s 0 V) h C x p →
      PatchInputs (S:=S) (pull s 0 U) (pull s 0 V) (angle x V A F q d Y a s) C x p := by
  intro U h hx i hi
  let j := sendEdge s 0 i
  obtain ⟨h1,h2⟩ := hx i hi
  obtain ⟨b,hb,he,ht⟩ := back V U i s h h1
  have hj : S.ratio.parent j.1 ∈ O.dome ((D+104)*radiusB x) := by
    have hl := spin_separation (S:=S) i s p
    refine enter_dome O ((turn_dome ..).mp hp) ?_
    unfold j; unfold thin at hi; rw [add_mul]; omega
  have ha : angle x V A F q d Y a s i=h i := ht _ (keep_angle x V O A F q J d Y a D _ b (hb.trans_le (h2.trans hc)) hd hr he hj hh)
  unfold increment at *; rw [ha]; exact ⟨h1,h2⟩

section forecast
open Filter Remainder.Affine Remainder.Scales Next.Fluctuations

variable (Q : Patch) (P : Teller G) (w C x : ℝ)

/-- One charged chart size & weak-input rule; also authorizes the
actual output prediction Hessian branches used in the subtraction.
Valid with all x beyond one price. -/
def Accepts : Prop :=
    span Q x ≤ radiusB x / 50 ∧ 1 ≤ radiusB x ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=Q → 100*(1+radiusB x) ≤ c.val →
      P.Funds S T → ∀ (D : ℕ) (F : Forest S.ratio) (O A : Stores S) (U : Config G f)
        (k : S.Choices) (V : Config G c), SliceSet S F U → Wide O A D x w U k V →
        ∀ p : Site c, inSweep O A D (radiusB x) p →
        (∃ h : Directions G f, PatchInputs (S:=S) U V h C x p) ∧
        (∀ i : Bond c, i.1=p → ContDiffAt ℝ ω (bTest (replica S.ratio V) k i) 0)

/-- Cost with only local V/fine guard obligations. -/
theorem forecasts (hw : 0<w) (hQ : Q.Branches P.bind G) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ x : ℝ in atTop, Accepts Q P w C x := by
  obtain ⟨C,hC,H⟩ := cleans_at P Q.L w hw
  obtain ⟨l,δ,-,hδ,hq⟩ := LocalJet.Block.block_comparison G Q P.bind hQ (ε:=1) (by norm_num)
  have hm : Tendsto (fun x => Remainder.weakRadius (G:=G) C Q.L x) atTop (𝓝 0) := by
    have ht := (tally_g G Q.L 5 1).const_mul C
    rw [mul_zero] at ht; refine ht.congr fun x => ?_
    rw [Remainder.weakRadius,fi]; ring
  refine ⟨C,hC,?_⟩
  filter_upwards [H,hm.eventually (ge_mem_nhds hδ),small_span Q,Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx hl hv ht
  refine ⟨hv,ht,?_⟩
  intro c f S T hp hz hf D F O A U k V he hA p hP
  obtain ⟨a,-,H⟩ := hx c f S T (congr_arg Patch.L hp) hz hf D F O A U k V he hA
  obtain ⟨hm,z,hz,-⟩ := H p hP
  refine ⟨⟨a,fun i hi => ⟨(hm i hi).1,(hm i hi).2.1⟩⟩,?_⟩
  intro i hi
  let a := z∘S.ratio.parent; let W := replica S.ratio V
  let u := Lattice.gauge a W
  have hb (j : Bond f) (h : separation i.1 (S.ratio.parent j.1) ≤ predReach Q) : G.chord (u j) ≤ δ := by
    change G.chord ((Lattice.gauge (constantGauge z S.ratio) (replica S.ratio V)) j) ≤ _
    rw [copied _ S.patch.odd_side V z]; unfold replica; split
    · rw [G.chord_one]; exact hδ.le
    rw [← hp] at hl hv h
    exact (hz (S.ratio.parent j.1,j.2) (by rw [hi] at h; unfold thin; unfold span at hv; dsimp only; omega)).trans hl
  have hv := hq S hp hf.knobs k u i hb
  exact (b_auth (funds_branch hf) a W i k hv.2.1).1
end forecast

/-- Input licences to the annulus application, for the same retained
packet. Assumes no global eligibility of deleted portions. -/
theorem suffices_for (s : Signed) {Q : Patch} {P : Teller G} (w C : ℝ) (hQ : S.patch=Q)
    (hS : 100*(1+radiusB x) ≤ c.val) (hP : P.Funds S T)
    (hC : Accepts Q P w C x) {r : ℕ} (ho : Clearance O A r) (hu : (D+100)*radiusB x ≤ r)
    (hd : 0<d) (hr : 2*d < firstRadius G) (hc : C*fiery G x S.patch.L ≤ d)
    (hh : jacob J q d (openAt O A D x F) (tape a) ≠ 0)
    (hw : Wide (turnStore s O) (turnStore s A) D x w (pull s 0 (physical A F V Y (tape a))) (choice s k) (pull s 0 V)) :
    let X := rim O D x s
    Ensures (physical A F V Y (tape a)) V O (rim O D x) (fun s => selectFrom (rim O D x s) A F x s) x k
      (angle x V A F q d Y a) w C D F A s ∧ AtBranches x V k A F s X := by
  intro X
  let U := physical A F V Y (tape a)
  let u := turnStore s O; let b := turnStore s A; let g := choice s k
  have hi : (rim O D x s).annulus u b D (radiusB x) := rim_located O A x s ho
    ((Nat.mul_le_mul_right _ (show D+2≤D+100 by omega)).trans hu)
  let JX := selectFrom X A F x s
  have hX : JX.selects X := selects ..
  have he : SliceSet S F U := fun i hi => F.on_tree _ ⟨i,hi⟩
  have hl := hC.2.2 S T hQ hS hP D (turnForest s F) u b _ g _ (turn_sliced s F U he) hw
  have ha p (hg : inSweep u b D (radiusB x) p) : PatchInputs (S:=S) (pull s 0 U) (pull s 0 V)
      (angle x V A F q d Y a s) C x p := by
    obtain ⟨e,hv⟩ := (hl p hg).1
    exact angles x V O A F q J d Y a D s p C hC.2.1 hd hr hc hg.2 hh e hv
  have H : (5:ℕ)*radiusB x ≤ r := (Nat.mul_le_mul_right _ (show 5≤D+100 by omega)).trans hu
  refine ⟨⟨(ho.turn s).owns x H,hw,hX,hi,fun i hp => ha _ (hi.1 i (hX.1 hp)),
    fun i hp => ha _ (hi.2.1 i (hX.2 hp))⟩,?_⟩
  intro i hh
  rw [replica_turn]
  exact (hl _ (hi.2.1 i (hX.2 hh))).2 i rfl
end YM.AnalyticBridge.Annulus
