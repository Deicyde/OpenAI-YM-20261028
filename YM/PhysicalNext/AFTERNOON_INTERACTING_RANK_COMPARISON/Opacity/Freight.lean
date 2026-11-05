import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Pairing
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Group


/-!
# A value gain for the true local Fsct log-determinant pair

Use only the mark-atlas on the *no hole* plate. Equip it with a log ray at
trivial field with tag stencil fixed. Lift the gauge on the outside;
the sum of all colors on the true address sees exactly the vacant stencil
at the *end* of this ray. Same F/k. Does not claim invariance of any single
key or that a whole determinant is close to the one at another tag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Barge
open Lattice Wilson Pressure RG RG.Supply Laurent Bloch Matrix Finset Filter Tree
    Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Pressure.Stores
    Function AnalyticBridge.RelativeLogdet Physical Paint AnalyticNext.ConnectedActivity
    EndpointLoadF16.DetLong Fund Next.Rank AnalyticBridge.LocalGaussianLaws PhysicalGuard7f546.Curved Precision Bid Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {s : S.Choices} {P : Teller G} {D : Patch} {q : Fund} {T : Tube G S} {i : Site c} {x a v C η b : ℝ}

-- auxiliary budget point for marking the 1-jet BEFORE field and sector.
def billPoint : BudgetPoint := ⟨2,6,1,1,1,by omega,by omega,zero_lt_one,by decide,zero_lt_one,le_rfl⟩
lemma intro_nn (G : Gauge) (q : Fund) : 0≤ q.introCost G 2 1 := by
  apply mul_nonneg zero_le_two; refine Finset.sum_nonneg fun j _=>?_ ; unfold baseTicket; have := q.amplitude G 2 1
  have hh :0≤ q.D:= zero_le_one.trans q.coin; positivity
lemma quote {r : ℝ} (hq : q.Stock P D 20 2 1 a x) (hS : S.patch=D) (hT : P.Funds S T)
    (hL :100*(1+radiusB x) ≤ c.val) {w : Directions G c}
    (hw : ‖w‖ ≤ 1) (F : Forest S.ratio) (s : S.Choices) (i : Bond f) (hr : 0≤r) (hd : r ≤ q.width G 1) :
    |EndpointLoadF16.DetLong.prelude x T (voidStore S) F s i (increment 1 (r • w))| ≤ q.introCost G 2 1*r := by
  let J:= q.introCost G 2 1; let g:=EndpointLoadF16.DetLong.prelude x T (voidStore S) F s i
  let φ:= fun u : ℝ=> g (increment 1 (u • w)); let I:= Set.Icc 0 r
  have H₀:= hq.recite hS hT hL (Export.no_seeds G S x) (show ‖(0:Directions G c)‖ ≤ _ by rw [norm_zero]; exact (q.valid ..).le) s F
  let o:= EndpointLoadF16.DetLong.locus S i
  have he : billPoint.dirBound o w:= by
    intro j; apply ((norm_le_pi_norm _ _).trans hw).trans
    change 1≤1*_; rw [one_mul]; refine one_le_pow₀ ?_; simp
  have h u (hu:u ∈ I) : AnalyticBridge.LocalGaussian.Ticket (billPoint.dirBound o) 1 (increment (1:Config G c) (u • w)) J 1 g := by
    have hX:= hq.recite hS hT hL (Export.no_seeds G S x) (show ‖u • w‖≤ q.width G 1 from by rw [norm_smul,Real.norm_of_nonneg hu.1]; exact (mul_le_of_le_one_right hu.1 hw).trans (hu.2.trans hd)) s F
    have hQ:= hX.bound_prelude (bp:=billPoint) rfl o H₀ i
    convert! hQ
    change 1=(1+(↑(separation o o):ℝ))^2; simp
  have hf u (hu:u∈ I) : DifferentiableAt ℝ φ u ∧ ‖deriv φ u‖ ≤ J:= by
    have ha:=h u hu
    have ht:=ha.legal w (l:=[]) (by simp)
    have hx:HasDerivAt (fun s : ℝ=>s-u) 1 u:=(hasDerivAt_id' u).sub_const u
    have hs:HasDerivAt φ (leftDerivs g [w] (increment 1 (u • w))) u:= by
      rw [← sub_self u] at ht; dsimp only [leftDerivs] at ht ⊢
      simpa only [φ, Function.comp_def, ← Spindle.progress, add_sub_cancel, mul_one, sub_self] using ht.comp (h:=fun s=>s-u) u hx
    refine ⟨hs.differentiableAt,?_⟩; rw [hs.deriv]; simpa only [one_pow,mul_one] using ha.price [w] (by simp) (by simpa)
  have ht:=Convex.norm_image_sub_le_of_norm_deriv_le (fun u hu=> (hf u hu).1) (fun u hu=> (hf u hu).2) (convex_Icc (0:ℝ) _) (Set.left_mem_Icc.mpr hr) (Set.right_mem_Icc.mpr hr)
  have hz : φ 0=0:= by unfold φ g EndpointLoadF16.DetLong.prelude contrast; rw [zero_smul,Work.G07.at_zero_increment,Pi.sub_apply,sub_self,mul_zero]
  rwa [hz,sub_zero,sub_zero,Real.norm_of_nonneg hr] at ht

lemma zero_plate {Z : Support c} (hi : ∀ j∈Z,j∉ A.place) {V' : Config G c} (he : Agrees Z V V') : Physical.Reads Z A (voidStore S) F F V V' s s := by
  refine ⟨he,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>Iff.rfl,fun i hx=>?_,fun i hx=>?_,fun i hx=>?_⟩
  · change _ ↔ i∈(∅:Finset _); simp only [notMem_empty,iff_false]; intro hv; exact hi i (hx (mem_union_left _ (mem_singleton_self _))) (mem_union_right _ hv)
  · have hv : S.ratio.parent i.1∈ startPos S i:= mem_image_of_mem _ (Work.E01.base_touched ..)
    change _ ↔ i∈(∅:Finset _); simp only [notMem_empty,iff_false]; intro h; exact hi _ (hx hv) (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨_,h,hv⟩)))
  have hv : i.1∈ pinPos i:= by simp [pinPos];
  change _ ↔ i∈(∅:Finset _); simp only [notMem_empty,iff_false]; intro h; exact hi _ (hx hv) (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨_,h,hv⟩)))

lemma intro_paid (P : Teller G) (D : Patch) (q : Fund) : ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S) {a v C η b : ℝ},
    S.patch=D → P.Funds S T → 100*(1+radiusB x) ≤ c.val → q.Stock P D 20 2 1 a x → Physical.Certified S T x v C η b →
    ∀ (A : Stores S) (V : Config G c) (s : S.Choices) (F : Forest S.ratio), Positioned x A V → ∀ i : Bond f, S.ratio.parent i.1∉ A.dome (30*radiusB x) →
      |EndpointLoadF16.DetLong.prelude x T A F s i V| ≤ x^(-(1/4):ℝ) := by
  filter_upwards [Milk.full_pose G D,Milk.trim_rate G D 1 7 (1/6) (by norm_num),const_allow (intro_nn G q) (show -(1/3:ℝ) < -(1/4) by norm_num), (tendsto_rpow_neg_atTop (show 0< (1/3:ℝ) by norm_num)).eventually (ge_mem_nhds (q.valid G 1)), eventually_gt_atTop (0:ℝ)] with x hP hD h0 hu hx c f S T a v C η b hS hT hL hq hc A V s F hp i hi
  let o:=EndpointLoadF16.DetLong.locus S i; let z:=Spindle.fingers V o; let V':= gauge z V
  obtain ⟨y,H,hy,-,-⟩:= hP S A V hS hL hp o hi
  let B:=radiusB x; let r:=x^(-(1/3):ℝ)
  have hh : ‖collect G y‖ ≤ r:= by
    apply le_trans ((pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr (show ∀ i, ‖collect G y i‖ ≤ ‖y‖ from fun i => norm_le_pi_norm y (i.1,coord i.2)))
    exact hy.trans (hD.trans_eq (by unfold r; push_cast; norm_num))
  have hr :0<r:= Real.rpow_pos_of_pos hx _
  let w:= r⁻¹ • collect G y
  have hw : ‖w‖≤1:= by unfold w; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]; exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hr.le)).trans_eq (inv_mul_cancel₀ hr.ne')
  let I:= increment (1:Config G c) (r • w); have hI:I=represent y:= by unfold I w; rw [smul_inv_smul₀ hr.ne']; rfl
  have he : EndpointLoadF16.DetLong.prelude x T A F s i V=EndpointLoadF16.DetLong.prelude x T (voidStore S) F s i I:= by
    unfold EndpointLoadF16.DetLong.prelude contrast; simp only [Pi.sub_apply, chapters,Sum.elim_inl,bolus_read]
    apply congr_arg ((-(1/2:ℝ)) * ·); apply congr_arg (· - _)
    let W:= windows S x (G:=G)
    obtain ⟨a',b',hf,-⟩:=hT.feeds
    change batch (letterBase W (AFull T A F x V s)) _=batch (letterBase W (AFull T (voidStore S) F x I s)) _
    rw [(gilded F s hc z (funds_branch hT) (V:=V) (A:=A) hp hf).1]
    refine sum_congr rfl fun j _=> ?_
    let Z:= lens (EndpointLoadF16.DetLong.locus S) 20 B i
    apply (aligned T (Z:=Z) (zero_plate ?_ ?_) (funds_branch hT) hc.basis hc.geometry).local_value (l:=20) (by decide) (i,j) (Finset.Subset.refl _)
    · intro j hj h
      exact hi (halo_spec.mpr ⟨_,h,(separation_comm ..).trans_le (((lens_spec _).1 hj).trans (by unfold B; omega))⟩)
    intro j hj hh
    exact hI.symm ▸ (H j ((lens_spec _).1 (show _∈Z from hj)))
  rw [he]
  exact (quote hq hS hT hL hw _ _ i hr.le hu).trans h0
end YM.PhysicalNext.InteractingRank.Barge
