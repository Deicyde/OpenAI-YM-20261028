import YM.AnalyticBridge.VERIFIED_RESET_STEP.Placement
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Squares
import YM.Push.LOCAL_SPLITTING.Transport
import YM.Push.PRICE_COMPILER.Continuity

/-! Common orientation averages on the true channel reads. `layer` is a
convenient notation for the early alpha charge and the reattached terms at
the output. Not rechoosing orientations of the kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG Precision UVNext.PricedKernels Push.BetaTransport
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {ι : Type*} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ : ℝ}

def factor := (Fintype.card Signed:ℝ)⁻¹
lemma card_pos : 0 < (Fintype.card Signed:ℝ) := by exact_mod_cast Fintype.card_pos
lemma factor_pos : 0 < factor := inv_pos.mpr card_pos
lemma factor_card : factor * Fintype.card Signed = 1 := inv_mul_cancel₀ card_pos.ne'
lemma factor_le : factor ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α:=Signed))

def layer (f : ι → Pot G n) (U : Config G n) := factor * ∑ x : Seat n, ∑' i, f i (x.view U)
lemma layer_total (f : ι → Pot G n) (U : Config G n) (h : ∀ W, Summable fun i => f i W) :
    layer f U = ∑' i : Seat n × ι, factor * f i.2 (i.1.view U) := by
  let g (x : Seat n × ι) := f x.2 (x.1.view U)
  have he : Summable g := Summable.of_norm ((summable_prod_of_nonneg fun i => norm_nonneg (g i)).mpr ⟨fun i => (h (i.view U)).norm, Summable.of_finite⟩)
  change layer f U = ∑' i, factor * g i
  rw [tsum_mul_left,he.tsum_prod, tsum_fintype]; rfl
lemma layer_scale (f : ι → Pot G n) (b : ℝ) (U : Config G n) : layer (fun i W => b * f i W) U = b * layer f U := by
  simp only [layer,tsum_mul_left,← Finset.mul_sum]; ring
lemma layer_combine {f g : ι → Pot G n} (hf : ∀ W, Summable fun i => f i W) (hg : ∀ W, Summable fun i => g i W) (U : Config G n) :
    layer (fun i W => f i W+g i W) U = layer f U + layer g U := by
  simp only [layer,(hf _).tsum_add (hg _),Finset.sum_add_distrib,mul_add]

private lemma views (s : Signed) (o : Site n) (U : Config G n) : Seat.view (s,s.act o) U = translate o (pull s 0 U) := by rw [← pull_one,pull_pull,mul_one,affine,add_zero]; rfl
private lemma rebased (f : Site n → Pot G n) (U : Config G n) (hf : ∀ x W, f 0 (Lattice.translate x W) = f x W) :
    ∑ x : Seat n, f 0 (x.view U) = ∑ s : Signed, ∑ x : Site n, f x (pull s 0 U) := by
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Equiv.sum_comp s.actEquiv.toEquiv (fun b => f 0 (Seat.view (s,b) U))]; exact Finset.sum_congr rfl fun x _ => by change f 0 (Seat.view (s,s.act x) U) = _; rw [views,hf]

private lemma kept_translate (x : Site n) (U : Config G n) (b : ℝ) : PathData.kept c b 0 (Lattice.translate x U) = PathData.kept c b x U := by
  let e : Equiv.Perm (Face (Per n)) := (Equiv.addRight x).prodCongr (Equiv.refl _)
  unfold PathData.kept; symm; rw [← e.forall_congr_right]; apply propext; refine forall_congr' fun i => ?_
  simp [faceValue,← pull_one,travel_pull,affine,e,separation]
private lemma face_translate (x : Site n) (U : Config G n) (a : PlaqAxes) : faceValue (Lattice.translate x U) (0,a) = faceValue U (x,a) := by
  rw [faceValue,← pull_one,travel_pull,faceValue]; simp [affine]
private lemma ell_translate (x : Site n) (U : Config G n) (a : PlaqAxes) : R.ell (Lattice.translate x U) (0,a) = R.ell U (x,a) := by
  simp only [PathData.ell,PathData.ellTerms,Slot.atSite,Push.Local.expand_translate,zero_add]
private lemma placed_translate {k : ℕ} (a : Atom G k) (x : Site n) (U : Config G n) : a.placed p (Lattice.translate x U) 0 = a.placed p U x := by
  unfold Atom.placed
  rw [← pull_one,Push.Local.masked_pull]
  have he : (a.footprint 0).image (Push.Local.turnSites 1 x) = a.footprint x := by
    unfold Atom.footprint; simp [Finset.image_image,comp_def,show ⇑(Push.Local.turnSites 1 x) = affine 1 x from rfl,affine]
  have hf : ((fun V => a.unmasked V 0) ∘ pull 1 x) = fun V => a.unmasked V x := by ext V; simp [comp_apply,pull_one,Atom.unmasked,Slot.atSite,Push.Local.expand_translate]
  rw [he,hf]

def summit (R : PathData G) (p : BudgetPoint) (d : High) (o : Site n) : Pot G n := masked p.threshold (d.home R o) (d.plain R o)
lemma summit_sum (h : R.Bounds c σ C Λ) (p : BudgetPoint) (U : Config G n) (o : Site n) : Summable (fun d => summit R p d o U) :=
    Summable.sum _ ((PathData.atom_dominated R.cubic p o h.width h.three).summable U) ((PathData.atom_dominated R.quartic p o h.width h.four).summable U)
lemma true_base (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ) (U : Config G n) :
    layer (fun i : Low => i.live R c p (0:Site n)) U + layer (fun d => summit R p d 0) U = kinetic R c p U := by
  let a x (V : Config G n) := ∑ b : PlaqAxes, R.baseTerm c p V (x,b)
  have ha x V : a 0 (Lattice.translate x V) = a x V := by
    simp only [a,PathData.baseTerm,kept_translate,face_translate,ell_translate]
  let z x (V : Config G n) := PathData.atomSeries R.cubic p V x + PathData.atomSeries R.quartic p V x
  have hz x V : (∑' d, summit R p d x V) = z x V := (summit_sum h p V x).comp_injective Sum.inl_injective |>.tsum_sum
      ((summit_sum h p V x).comp_injective Sum.inr_injective)
  have hZ x V : z 0 (Lattice.translate x V) = z x V := by simp_rw [z,PathData.atomSeries,placed_translate]
  simp_rw [layer, show ∀ W, (∑' i : Low, i.live R c p 0 W) = a 0 W from Low.live_total h hw 0, hz 0, rebased a U ha, rebased z U hZ]
  simp only [kinetic,z,a,Fintype.sum_prod_type (f:=fun b => R.baseTerm _ _ _ b),Finset.sum_add_distrib,mul_add]; rfl
lemma allGoodPrice (h : R.Bounds c σ C Λ) (U : Config G n) (hU : flags p.threshold U = ∅) :
    layer (fun d : Low => d.maskedPlain R c 0 p) U = secondTerm c R U := by
  let a x (V : Config G n) := ∑ b : PlaqAxes, (c.direct * G.price (faceValue V (x,b)) + ‖R.ell V (x,b)‖^2 / 2)
  have hu (x : Seat n) (i : Low) : Healthy p.threshold (i.home R p 0) (x.view U) :=
    (Seat.healthy ..).mp (by simp only [Healthy,hU,Finset.disjoint_empty_right])
  have he (x : Seat n) : (∑' d : Low, d.maskedPlain R c 0 p (x.view U)) = a 0 (x.view U) := by simp_rw [Low.maskedPlain,masked_eq _ _ _ _ (hu ..)]; exact Low.plain_total h ..
  simp_rw [layer,he,rebased a U (fun x V => by simp only [a,face_translate,ell_translate])]
  simp only [secondTerm,Precision.quadratic,Patch.average,Fintype.sum_prod_type]; rfl

lemma reframe_norm (s : Signed) (w : Flux G) (b : PlaqAxes) : ‖reframe w s b‖ = ‖w (PlaqAxes.transform s b)‖ := by
  unfold reframe
  let i := s.perm b.val.1; let j := s.perm b.val.2
  have hn : |StressFlux.sign s b.val.1 * StressFlux.sign s b.val.2| = 1 := by unfold StressFlux.sign; split_ifs <;> norm_num
  rw [norm_smul,Real.norm_eq_abs, hn,one_mul]
  rcases lt_or_gt_of_ne (show i ≠ j from s.perm.injective.ne b.property.ne) with h|h
  · change ‖orderedDir w i j - orderedDir w j i‖ = _; simp only [orderedDir,h,not_lt_of_gt h,↓reduceDIte, sub_zero]
    apply congrArg (fun b => ‖w b‖); apply Subtype.ext; change (i,j) = (min i j,max i j); simp [h.le]
  change ‖orderedDir w i j - orderedDir w j i‖ = _; simp only [orderedDir,h,not_lt_of_gt h,↓reduceDIte, zero_sub,norm_neg]; apply congrArg (fun b => ‖w b‖); apply Subtype.ext; change (j,i)=(min i j,max i j); simp [h.le]

def heads (p : BudgetPoint) (o : Site n) : Pot G n := masked p.threshold {o} fun U => (∑ i, ‖petals U o i‖^2) / 2
def sketch (R : PathData G) (c : Clip) (p : BudgetPoint) (o : Site n) (i : Low) : Pot G n := fun U => i.mark R c * masked p.threshold {o} (i.proxy R o) U
lemma sketch_sum (h : R.Bounds c σ C Λ) (p : BudgetPoint) (U : Config G n) :
    layer (sketch R c p 0) U = ∑ x, heads p x U := by
  have he (x : Seat n) : (∑' d, sketch R c p 0 d (x.view U)) = heads p x.2 U := by
    have h' : x.spread {0} = {x.2} := by unfold Seat.spread; simp [affine]
    have ht := x.healthy p.threshold {0} U; rw [h'] at ht
    by_cases hv : Healthy p.threshold {x.2} U
    · rw [heads,masked_eq _ _ _ _ hv]; simp_rw [sketch,masked_eq _ _ _ _ (ht.mp hv), Low.proxy,Low.analogue_total h]
      rw [Seat.view, petals_moves]; simp only [affine,Signed.act_zero,zero_add,reframe_norm]; rw [Equiv.sum_comp _ (fun i => ‖petals U x.2 i‖^2)]
    simp [heads,masked_ne _ _ _ _ hv,sketch, masked_ne _ _ _ _ (mt ht.mpr hv)]
  rw [layer]; simp only [he,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,factor_card,one_mul]
end YM.AnalyticBridge.VerifiedReset
