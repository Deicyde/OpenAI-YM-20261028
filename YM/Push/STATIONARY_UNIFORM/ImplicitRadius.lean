import YM.Push.STATIONARY_UNIFORM.Slope

/-!
# Uniform sup-radius implicit function theorem specialized to score tensors

Includes how to interpret the stationary value branch vs. a function
picked on some germ. Does NOT need a size bound on the value of the score
function; works for genuine analytic costs extensive in volume. Sup on
input array real components, key in the physical application for a common
radius, and for the Hessian inverse does not pay for a sup/L² equivalence
on the torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical NNReal

variable {n : Side} {ι τ : Type} [Fintype ι] [Fintype τ] {C a r m : ℝ} {K N : ℕ}
variable {l : ι ⊕ τ → Site n} {f : Positions (ι ⊕ τ) → ℝ}

/-- Transfer window, analytic scatter hypothesis (period-independent input
estimate to prove on each actual branch, **not** asserting it is free). -/
structure Receipt (l : ι ⊕ τ → Site n) (a : ℝ) (N K : ℕ) (C r m : ℝ) (f : Positions (ι ⊕ τ) → ℝ) : Prop where
  mult : Multiplicity l K
  pos_m : 0<m
  pos_r : 0<r
  pos_a : 0<a
  pos_C : 0<C
  order : 3≤N
  born x : x∈ball 0 r → ContDiffAt ℝ ω f x ∧ Scatter l a N f x C
  gap : Charge (block f 0) m
  alone : Slope f 0=0

def reserveH (K : ℕ) (C a r m : ℝ) :=
  min (r/2) (m/(2*(1+C*((K:ℝ)*countCost a)^2)))

def inversePrice (K : ℕ) (C a m : ℝ) := 1+(m/2/2)⁻¹*((K:ℝ)*countCost (tiltWidth K (m/2) a C))

def reserveV (K : ℕ) (C a r m : ℝ) := min (reserveH K C a r m) (1/(4*inversePrice K C a m*(1+C*((K:ℝ)*countCost a)^2)))

def reserveX (K : ℕ) (C a r m : ℝ) := min (reserveV K C a r m) (reserveV K C a r m /
  (4*inversePrice K C a m*(1+C*((K:ℝ)*countCost a))))

namespace Receipt
variable (h : Receipt l a N K C r m f)
include h

lemma reserveH_pos : 0 < reserveH K C a r m := by
  unfold reserveH; have hp := h.pos_C; have hr := h.pos_r; have hm := h.pos_m; positivity
lemma reserveH_lt : reserveH K C a r m < r := lt_of_le_of_lt (min_le_left ..) (half_lt_self h.pos_r)
lemma inverse_pos : 0 < inversePrice K C a m := by
  have hp := h.pos_C
  have hm := h.pos_m
  have hz : 0<countCost (tiltWidth K (m/2) a C) := count_pos (tiltWidth_pos K (half_pos h.pos_m) h.pos_a h.pos_C.le)
  unfold inversePrice; positivity
lemma reserveV_pos : 0 < reserveV K C a r m := by
  unfold reserveV; have := h.reserveH_pos; have hx := h.inverse_pos; have hp := h.pos_C; positivity
lemma reserveX_pos : 0 < reserveX K C a r m := by
  unfold reserveX; have := h.reserveV_pos; have hz := count_pos h.pos_a; have hx := h.inverse_pos; have hp := h.pos_C; positivity

lemma snaps (p : Positions (ι ⊕ τ)) (hp : p∈closedBall 0 (reserveH K C a r m)) : Charge (block f p) (m/2) := by
  let D := (K:ℝ)*countCost a
  let R := reserveH K C a r m
  have hR : 0<R := h.reserveH_pos
  have hh : p∈ball (0:Positions (ι⊕τ)) r := closedBall_subset_ball h.reserveH_lt hp
  have hd : 0 ≤ D := mul_nonneg (by positivity) (count_pos h.pos_a).le
  have hc := h.pos_C
  have hm := block_near h.pos_a hc.le h.mult (convex_ball _ _) h.born (mem_ball_self h.pos_r) hh
    (show ‖0-p‖ ≤ R by simpa using hp) h.order
  have he := h.gap.transfer h.pos_a (show 0 ≤ R*(C*D) by positivity) hm (h.mult.comp Sum.inr_injective)
  have hu : R ≤ m/(2*(1+C*D^2)) := min_le_right ..
  have hv : m/2 ≤ m - (R*(C*D))*D := by
    rw [le_div_iff₀ (show 0 < 2*(1+C*D^2) by positivity)] at hu
    linarith
  exact fun v => le_trans (mul_le_mul_of_nonneg_right hv (by positivity)) (he v)

section inv
variable [DecidableEq τ]
lemma priced_inverse (p : Positions (ι ⊕ τ)) (hp : p∈closedBall 0 (reserveH K C a r m)) :
    0 < (block f p).det ∧
    Sealed (l ∘ Sum.inr) (tiltWidth K (m/2) a C) (block f p)⁻¹ ((m/2/2)⁻¹) ∧
    ∀ v, ‖((block f p)⁻¹ *ᵥ v)‖ ≤ inversePrice K C a m*‖v‖ := by
  have hA := h.snaps p hp
  have hg := h.born p (closedBall_subset_ball h.reserveH_lt hp)
  have ht : 0 < (block f p).det := (hA.positive (block_hermitian hg.1) (half_pos h.pos_m)).det_pos
  have hb := block_rows hg.2 (le_trans (by norm_num) h.order)
  have hm' := half_pos h.pos_m
  have hk : Multiplicity (l ∘ (Sum.inr : τ → ι ⊕ τ)) K := h.mult.comp Sum.inr_injective
  have hh := inverse_sealed hb hm' h.pos_a hA h.pos_C.le hk (isUnit_iff_ne_zero.mpr ht.ne')
  exact ⟨ht,hh,rows_test (fun i => (hh.row (tiltWidth_pos K hm' h.pos_a h.pos_C.le)
    (inv_pos.mpr (half_pos hm')).le hk i).trans (le_add_of_nonneg_left zero_le_one)) h.inverse_pos.le⟩
end inv

omit h in
lemma holds {x : Positions ι} {v : Positions τ} (hx : x∈ball 0 (reserveX K C a r m))
    (hv : v∈closedBall 0 (reserveV K C a r m)) : meetVar x v∈closedBall 0 (reserveV K C a r m) := by
  rw [mem_closedBall,dist_zero_right,norm_meet]; exact max_le (le_trans (show ‖x‖ < reserveX K C a r m by simpa using hx).le
    (min_le_left ..)) (by simpa using hv)

lemma adjusted (x : Positions ι) (hx : x∈ball 0 (reserveX K C a r m)) :
    ∃ v : Positions τ, ‖v‖ ≤ reserveV K C a r m/2 ∧ Slope f (meetVar x v)=0 ∧
      ∀ w∈closedBall 0 (reserveV K C a r m), Slope f (meetVar x w)=0 → w=v := by
  let R := reserveV K C a r m
  let T := reserveX K C a r m
  let s := closedBall (0:Positions τ) R
  have hR : 0<R := h.reserveV_pos
  have ht : T ≤ R := min_le_left ..
  have hu : R ≤ reserveH K C a r m := min_le_left ..
  have hs : 0∈s := mem_closedBall_self hR.le
  have hh i (hi : i∈s) : meetVar x i∈ball (0:Positions (ι ⊕ τ)) r := closedBall_subset_ball (hu.trans_lt h.reserveH_lt) (Receipt.holds hx hi)
  let D : ℝ := K*countCost a
  have hc := h.pos_C; have hd : 0 ≤ D := mul_nonneg (by positivity) (count_pos h.pos_a).le
  have hm i (hi : i∈s) := slope_block (h.born _ (hh _ hi)).1
  let H := block f 0
  let J := inversePrice K C a m
  have hp : 0<J := h.inverse_pos
  obtain ⟨HZ,_,HG⟩ := h.priced_inverse 0 (mem_closedBall_self h.reserveH_pos.le)
  have hI : IsUnit H.det := isUnit_iff_ne_zero.mpr HZ.ne'
  let L := (Matrix.toLin' H⁻¹).toContinuousLinearMap
  have hL (z) : L z = H⁻¹ *ᵥ z := Matrix.toLin'_apply ..
  let Y v := v - L (Slope f (meetVar x v))
  have hY (v) (hv : v∈s) : HasFDerivAt Y (ContinuousLinearMap.id ℝ _ - L.comp (fderiv ℝ (Slope f ∘ meetVar x) v)) v := by
    have ha : DifferentiableAt ℝ (Slope f ∘ meetVar x) v :=
      ((hm v hv).1.differentiableAt (by simp)).comp v (meet_derivative x v).differentiableAt
    exact (hasFDerivAt_id _).sub (L.hasFDerivAt.comp v ha.hasFDerivAt)
  have hP : J*(R*(C*D)*D) ≤ 1/4 := by
    have hz := (le_div_iff₀ (show 0 < 4*J*(1+C*D^2) by positivity)).mp (show R ≤ 1/(4*J*(1+C*D^2)) from min_le_right ..)
    linarith [mul_pos hR hp]
  have hV (v) (hv : v∈s) (w) : ‖(fderiv ℝ Y v) w‖ ≤ (1/4:ℝ)*‖w‖ := by
    let z := meetVar x v
    have hz : ‖0-z‖ ≤ R := by simpa using Receipt.holds hx hv
    let B := H-block f z
    have hB := block_near h.pos_a hc.le h.mult (convex_ball _ _) h.born (mem_ball_self h.pos_r) (hh _ hv) hz h.order
    rw [(hY _ hv).fderiv]; change ‖w - L (fderiv ℝ (Slope f ∘ meetVar x) v w)‖ ≤ _
    rw [(hm v hv).2]; rw [show w - L (block f z *ᵥ w) = H⁻¹ *ᵥ (B *ᵥ w) from by
      dsimp only [L,z, B]; rw [hL, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec w H⁻¹ H,H.nonsing_inv_mul hI,one_mulVec]]
    have he : ‖(B *ᵥ w)‖ ≤ R*(C*D)*D*‖w‖ := rows_test (S:=B) (hB.row h.pos_a
      (mul_nonneg hR.le (mul_nonneg hc.le hd)) (h.mult.comp Sum.inr_injective)) (by positivity) w
    apply (HG _).trans; apply (mul_le_mul_of_nonneg_left he hp.le).trans; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hP (norm_nonneg w)
  have hy (v) (hv : v∈s) (w) (hw : w∈s) : ‖Y v - Y w‖ ≤ (1/4:ℝ)*‖v-w‖ := (convex_closedBall (0:Positions τ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun i hi => (hY _ hi).differentiableAt) (fun i hi => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hV _ hi)) hw hv
  have hZ : ‖Y 0‖ ≤ R/4 := by
    let z := meetVar x (0 : Positions τ)
    have he := slope_range h.pos_a hc.le h.mult (convex_ball _ _) h.born (hh _ hs)
      (mem_ball_self h.pos_r) (le_trans (by norm_num) h.order)
    rw [h.alone,sub_zero,sub_zero,norm_meet,norm_zero,max_eq_left (norm_nonneg _)] at he
    change ‖0-L (Slope f z)‖ ≤ _; rw [zero_sub,norm_neg,hL]
    apply (HG _).trans; apply (mul_le_mul_of_nonneg_left he hp.le).trans
    have hv : ‖x‖ < R/(4*J*(1+C*D)) := lt_of_lt_of_le (show ‖x‖<T by simpa using hx) (min_le_right ..)
    rw [lt_div_iff₀ (show 0<4*J*(1+C*D) by positivity)] at hv
    change J * (‖x‖ * (C*D)) ≤ _; linarith [mul_nonneg (norm_nonneg x) hp.le]
  have hG v (hv : v∈s) : ‖Y v‖ ≤ R/2 := by
    have hx := norm_sub_le_norm_sub_add_norm_sub (Y v) (Y 0) 0
    rw [sub_zero,sub_zero] at hx
    have ht := hy v hv 0 hs; rw [sub_zero] at ht
    have he : ‖v‖ ≤ R := by simpa [s] using hv
    linarith
  have hw v : (Y v=v) ↔ Slope f (meetVar x v)=0 := by
    unfold Y; constructor
    · intro ht
      have he : L (Slope f (meetVar x v))=0 := by simpa using ht
      rw [hL] at he
      rw [← one_mulVec (Slope f (meetVar x v)), ← H.mul_nonsing_inv hI, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_zero]
    rintro he; rw [he,map_zero,sub_zero]
  haveI : Nonempty s := ⟨⟨_,hs⟩⟩
  haveI : CompleteSpace s := isClosed_closedBall.completeSpace_coe
  let g : s → s := fun x => ⟨Y x,by simpa [s] using (hG _ x.property).trans (half_lt_self hR).le⟩
  have H : ContractingWith (1/4:ℝ≥0) g := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun i j => ?_⟩
    simpa only [Subtype.dist_eq, g,dist_eq_norm,NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one] using hy i.val i.property j j.property
  let v := ContractingWith.fixedPoint g H
  have HH : Y v.val=v.val := congr_arg Subtype.val H.fixedPoint_isFixedPt
  refine ⟨v.val, HH ▸ hG _ v.property,(hw v).1 HH,fun w hW h => ?_⟩
  let i : s := ⟨w,hW⟩
  exact congr_arg Subtype.val (show i=v from H.fixedPoint_unique (Subtype.ext ((hw w).2 h)))

/-- One analytic graph on the stationarity corridor. No extrapolation outside it. -/
theorem throughout :
    let X := reserveX K C a r m; let V := reserveV K C a r m
    ∃ g : Positions ι → Positions τ, g 0=0 ∧ ∀ x∈ball 0 X, ContDiffAt ℝ ω g x ∧ ‖g x‖ ≤ V/2 ∧
      ∀ v∈closedBall 0 V, HasFDerivAt (fun y => f (meetVar x y)) (0 : Positions τ →L[ℝ] ℝ) v ↔ v=g x := by
  let X := reserveX K C a r m; let V := reserveV K C a r m
  let s := ball (0:Positions ι) X; let t := closedBall (0:Positions τ) V
  have hX := h.reserveX_pos; have hV := h.reserveV_pos
  let g : Positions ι → Positions τ := fun x => if e : x∈s then (h.adjusted x e).choose else 0
  have hg (x) (hx : x∈s) : ‖g x‖ ≤ V/2 ∧ Slope f (meetVar x (g x))=0 ∧ ∀ w ∈ t, Slope f (meetVar x w)=0 → w=g x := by
    unfold g; rw [dif_pos hx]; exact (h.adjusted x hx).choose_spec
  have hz : (0:Positions ι)∈s := mem_ball_self hX
  have hf x (hx : x∈s) y (hy : y∈t) : ContDiffAt ℝ ω f (meetVar x y) := (h.born _ (closedBall_subset_ball ((show V≤_ from min_le_left ..).trans_lt h.reserveH_lt) (Receipt.holds hx hy))).1
  refine ⟨g, ((hg _ hz).2.2 0 (mem_closedBall_self hV.le) (show Slope f (meetVar 0 0)=0 from ?_)).symm, fun x hx => ⟨?_, (hg x hx).1,fun i hi => ?_⟩⟩
  · exact (show meetVar (0:Positions ι) (0:Positions τ)=0 from (partSpace _ _).symm.map_zero).symm ▸ h.alone
  · let y := g x
    let F := Slope f ∘ (partSpace ι τ).symm
    have hy : y ∈ ball (0:Positions τ) V := by simpa using (hg x hx).1.trans_lt (half_lt_self hV)
    have ha := hf x hx _ (ball_subset_closedBall hy)
    have hA := slope_block (x:=x) (v:=y) ha
    have hh : ContDiffAt ℝ ω F (x,y) := hA.1.comp (x,y) (((partSpace ι τ).symm.contDiff (n:=ω)).contDiffAt)
    have he := (hh.differentiableAt (by simp)).hasFDerivAt.comp y (show HasFDerivAt (fun i => (x,i)) (ContinuousLinearMap.inr ℝ (Positions ι) (Positions τ)) y from (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y))
    let L := (fderiv ℝ F (x,y)).comp (ContinuousLinearMap.inr ℝ (Positions ι) (Positions τ))
    have hv (i : Positions τ) : L i=block f (meetVar x y)*ᵥ i := by
      rw [show L=_ from (show HasFDerivAt (Slope f ∘ meetVar x) L y from he).fderiv.symm]; exact hA.2 _
    have hi : Injective L := (injective_iff_map_eq_zero _).mpr fun i hi => by
      rw [hv] at hi
      have hd := (h.priced_inverse _ (closedBall_subset_closedBall (show V ≤ _ from min_le_left ..) (Receipt.holds hx (ball_subset_closedBall hy)))).1
      rw [← Matrix.one_mulVec (α:=ℝ) i, ← (block f (meetVar x y)).nonsing_inv_mul (isUnit_iff_ne_zero.mpr hd.ne'), ← Matrix.mulVec_mulVec,hi,Matrix.mulVec_zero]
    have hi' : L.IsInvertible := ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi,LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv,rfl⟩
    let u := hh.implicitFunction (by simp) hi'
    have hx' : u x=y := hh.implicitFunction_apply_self (by simp) hi'
    have hH : ContDiffAt ℝ ω u x := hh.contDiffAt_implicitFunction (by simp) hi'
    apply hH.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hx, hH.continuousAt.preimage_mem_nhds (show ball (0:Positions τ) V∈𝓝 (u x) from hx'.symm ▸ isOpen_ball.mem_nhds hy), hh.eventually_apply_implicitFunction (by simp) hi'] with i hi hJ hk
    exact ((hg i hi).2.2 (u i) (ball_subset_closedBall hJ) (hk.trans (hg x hx).2.1)).symm
  rw [← slope_zero_test (hf x hx i hi)]
  exact ⟨(hg x hx).2.2 i hi, fun hi => hi.symm ▸ (hg x hx).2.1⟩
end Receipt
end YM.Push.Uniform
