import YM.Next.FLUCTUATIONS.Charts

/-!
# Local evaluation and quantitative Z linearization

The proof of `z_chart_cost` needs constants uniform over the torus size,
even though period & tag array are large. Transfer each bond read, with
*its actual tags*, to a single big-enough finite torus, using a finite
patch stencil. Use `qderiv` (`Push.prices`) there and compare actual prediction
(not an unrooted mean), so normalization and branch choices in the data
are unchanged. Everything post-L. .
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

section locality

variable (P : Patch) (o : Axis)

-- No particular geometric efficiency needed for this fixed-patch receipt.
private def frameSites : Finset Cover := univ.biUnion fun x : P.Points => univ.biUnion
  fun y : P.Points => univ.biUnion fun l : Lattice.Order => (visits x.val (route x.val y.val l)).toFinset

private def alongBond := List.replicate P.L.val (posDir o)
private def bondShift : Cover := centerRoot P (step o)

private def predSites := (frameSites P ∪ (frameSites P).image (· + bondShift P o)) ∪
  univ.biUnion (fun x : P.Points => (visits x.val (alongBond P o)).toFinset)

private lemma frame_eq (K : KernelChoices) (hb : P.Branches K G)
    (U W : CoverConfig G) (h : ∀ i : Edge Cover, i.1 ∈ frameSites P → U i = W i)
    (t : P.FrameTag) : P.frame K U t = P.frame K W t := by
  have he (x y : P.Points) (l : Lattice.Order) : travel U x.val (route x.val y.val l) =
      travel W x.val (route x.val y.val l) := by
    apply travel_local _ _ U W
    exact fun i hi _ => h i (mem_biUnion.mpr ⟨x,mem_univ x, mem_biUnion.mpr ⟨y,mem_univ y,
      mem_biUnion.mpr ⟨l,mem_univ l,List.mem_toFinset.mpr hi⟩⟩⟩)
  have hax (x : P.FrameTag) : P.axial U x = P.axial W x := funext fun i => he x.1 i x.2
  have hv (f : P.Frame G) : P.via f U = P.via f W := by funext x y l; rw [via, via, he]
  have hs : P.score U = P.score W := by funext r; simp only [score,hv]
  have hm : P.usesMin K U ↔ P.usesMin K W := by simp only [usesMin,hax,hv]
  unfold Patch.frame
  by_cases hh : P.usesMin K W
  · rw [if_pos hh, if_pos (hm.mpr hh)]
    have h' : P.minimizing W (P.selected U) := by
      simp only [minimizing, ← hs]
      exact (P.min_exists U).choose_spec
    exact (hb.frame_unique W hh).unique h' (P.min_exists W).choose_spec
  · rw [if_neg hh, if_neg (fun h => hh (hm.mp h)), hax]

-- Make the different evaluation origins into explicit finite-cover reads.
private def predictionAt (K : KernelChoices) (U : CoverConfig G) (l r : P.FrameTag) (j : P.Points) :=
  P.predict K (fun x => P.frame K U l x * travel U x.val (alongBond P o) *
    (P.frame K (translate (bondShift P o) U) r x)⁻¹) j

private lemma predAt_eq (K : KernelChoices) (hb : P.Branches K G) (U W : CoverConfig G)
    (h : ∀ i : Edge Cover, i.1 ∈ predSites P o → U i = W i)
    (l r : P.FrameTag) (j : P.Points) : predictionAt P o K U l r j = predictionAt P o K W l r j := by
  have he : P.frame K U l = P.frame K W l := frame_eq P K hb U W
    (fun i hi => h i (mem_union_left _ (mem_union_left _ hi))) l
  let y := bondShift P o
  have hh : P.frame K (translate y U) r = P.frame K (translate y W) r := frame_eq P K hb _ _ (by
    intro i hi; unfold Lattice.translate; apply h
    exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hi))) r
  have hu (x : P.Points) : travel U x.val (alongBond P o) = travel W x.val (alongBond P o) :=
    travel_local _ _ U W fun i hi _ => h i <| mem_union_right _ (mem_biUnion.mpr
      ⟨x,mem_univ x,List.mem_toFinset.mpr hi⟩)
  unfold y at hh
  simp only [predictionAt, he, hh, hu]

private lemma reads_at (U : Config G f) (k : S.Choices) (q : Site c) (i : Axis) :
    S.prediction U k (q,i) = predictionAt S.patch i S.kernel (expandAt (S.ratio.embed q) U)
      (k.1 q) (k.1 (q+step i)) (k.2 (q,i)) := by
  have he := levels S q U (step i)
  rw [plank, wrap_step, add_comm] at he
  unfold predictionAt StepData.prediction StepData.connector StepData.frames bondShift alongBond; rw [he]

/-- One permissible post-L extent. -/
def predReach := univ.sup fun i : Axis => (predSites P i).sup (fun x => (route 0 x 1).length)

lemma prediction_near_eq (hb : S.patch.Branches S.kernel G) (U U' : Config G f) (k : S.Choices)
    (i : Bond c) (h : AgreeNear S.ratio.parent i.1 (predReach S.patch) U U') :
    S.prediction U k i = S.prediction U' k i := by
  rcases i with ⟨q,o⟩
  rw [reads_at, reads_at]
  apply predAt_eq _ _ _ hb
  rintro ⟨x,a⟩ hx
  unfold expandAt
  apply h
  let w := route 0 x 1
  let s := S.ratio.embed q
  have hh : stop s w = wrap f x + s := by
    simpa only [map_zero, add_zero, add_comm] using Work.E03.stop_route s 0 x
  have hv := Work.E03.sep_walk _ (Work.E03.parent_step S) s w
  rw [hh, show S.ratio.parent s = q from S.ratio.embed_parent q] at hv
  refine hv.trans ?_
  change x ∈ predSites S.patch o at hx
  exact le_trans (le_sup (f:=fun x => (route 0 x 1).length) hx) (le_sup (f:=fun i =>
    (predSites S.patch i).sup (fun x => (route 0 x 1).length)) (mem_univ o))
end locality

abbrev PairLogs (G : Gauge) (f c : Side) := LogField G f × LogField G c

def zTest (S : StepData c f) (k : S.Choices) (i : Bond c) (u : PairLogs G f c) :=
  Z S (S.prediction (represent u.1) k) (represent u.2) i

section fixed
variable (hb : S.patch.Branches S.kernel G) (k : S.Choices) (i : Bond c)
include hb

lemma zTest_diff : ContDiffAt ℝ ω (zTest (G:=G) S k i) 0 := by
  let t := fun a : PairLogs G f c => S.prediction (represent a.1) k i
  have hp : ContDiffAt ℝ ω (fun a : PairLogs G f c => G.mat (t a)) 0 :=
    (Push.prediction_cont S hb i k).comp (f:=fun a : PairLogs G f c => a.1) (0:PairLogs G f c) contDiffAt_fst
  have he := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ hp
  have ht : ContDiffAt ℝ ω (fun a : PairLogs G f c => G.mat (represent a.2 i)) 0 := by
    simp only [represent,increment, Pi.one_apply,mul_one,collect]
    exact (G.exp_jet.comp ((contDiff_apply ℝ _ (pole i)).comp contDiff_snd)).contDiffAt
  unfold zTest Tube.Z
  apply ContDiffAt.const_smul _ _
  apply curvature_diff_mat
  simp only [G.mat_mul,G.mat_inv]
  exact ht.mul he

lemma zTest_deriv (a : PairLogs G f c) :
    HasDerivAt (fun v : ℝ => zTest S k i (v • a)) (zLin S a.1 a.2 i) 0 := by
  let X := a.2 (pole i)
  let Y : G.Color := WithLp.toLp 2
    (fun j => Matrix.mulVec (probe S) (parts G 1 a.1 j) (pole i))
  let V (v : ℝ) := represent (v • a.2) i
  let Q (v : ℝ) := S.prediction (represent (v • a.1)) k i
  have he : HasDerivAt (fun v : ℝ => G.mat (V v)) (G.colorMat X) 0 := by
    simp only [V, represent,increment,collect, Pi.one_apply, Pi.smul_apply,mul_one,G.mat_lieExp,map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat X) (0:ℝ)
  have hh : HasDerivAt (fun v : ℝ => G.mat (Q v)) (G.colorMat Y) 0 := Push.prices S hb i k a.1
  suffices hf : HasDerivAt (fun v : ℝ => G.curvature (V v * (Q v)⁻¹)) (X-Y) 0 from
    hf.const_smul (Real.sqrt S.kernel.penalty)
  apply Work.F03.curvature_of_hasDerivAt (V:=fun v => V v * (Q v)⁻¹)
  have hz : V 0=1 := by simp only [V,zero_smul,link_one,Pi.one_apply]
  have hr : Q 0=1 := by simp only [Q,zero_smul, link_one, Push.settled S hb i k]
  simp only [G.mat_mul, G.mat_inv]
  convert! he.mul hh.star using 1
  rw [hz, hr,G.mat_one, star_one,mul_one, one_mul,G.colorMat_skew,map_sub]; abel

lemma zTest_zero : zTest (G:=G) S k i 0 = 0 := by
  simp only [zTest, Prod.fst_zero, Prod.snd_zero,Tube.Z, link_one,Push.settled S hb i k,
    Pi.one_apply,inv_one,mul_one,G.curvature_unit,smul_zero]

private lemma fixed_z_price : ∃ D r : ℝ, 0<D ∧ 0<r ∧
    ∀ k : S.Choices, ∀ i : Bond c, ∀ a : PairLogs G f c, ‖zLin S a.1 a.2 i‖ ≤ D * ‖a‖ ∧
      (‖a‖ ≤ r → ‖zTest S k i a - zLin S a.1 a.2 i‖ ≤ D * ‖a‖^2) := by
  classical
  choose d s hd hs h using fun j : S.Choices × Bond c => chart_quadratic_cost _ _
    (zTest_diff hb j.1 j.2).analyticAt (zTest_deriv hb j.1 j.2)
  let m := (univ.image s).min' (univ_nonempty.image s)
  have hm : m ∈ univ.image s := min'_mem _ _
  refine ⟨1+∑ j, d j, m, ?_, ?_, fun k i a => ?_⟩
  · have hx : 0 ≤ ∑ j, d j := sum_nonneg fun j _ => (hd j).le
    positivity
  · obtain ⟨k,-,he⟩ := mem_image.mp hm
    exact he ▸ hs k
  let j : S.Choices × Bond c := (k,i)
  have hd' : d j ≤ 1+∑ j, d j := (single_le_sum (f:=d) (fun i _ => (hd i).le)
    (mem_univ j)).trans (by simp)
  have hx := h j a
  refine ⟨hx.1.trans (by gcongr), fun hh => ?_⟩
  have hs := hx.2 (hh.trans (min'_le _ _ (mem_image_of_mem _ (mem_univ j))))
  rw [zTest_zero hb, zero_add] at hs
  exact hs.trans (by gcongr)
end fixed

section transplant
variable (P : Patch) (K : KernelChoices)

private lemma reference_exists : ∃ c₀ : Side, 1 < c₀.val ∧
    ∀ i : Axis, ∀ x ∈ predSites P i, lift (wrap (c₀*P.L) x) = x := by
  let M := univ.sup (fun i : Axis => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs)))
  let c₀ : Side := ⟨2*M+2, by omega⟩
  refine ⟨c₀, by change 1 < 2*M+2; omega,fun i x hx => lift_eq_iff.mpr ⟨rfl,fun a => ?_⟩⟩
  have hv : (x a).natAbs ≤ M := le_trans (le_sup (s:=univ) (f:=fun a => (x a).natAbs) (mem_univ a))
    (le_trans (le_sup (s:=predSites P i) (f:=fun x => univ.sup (fun a : Axis => (x a).natAbs)) hx)
      (le_sup (s:=univ) (f:=fun i => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs))) (mem_univ i)))
  have ht : 2*M < (c₀*P.L).val := lt_of_lt_of_le (b:=c₀.val) (by change _ < 2*M+2; omega)
    (by exact le_mul_of_one_le_right (Nat.zero_le _) P.L.property)
  omega

-- Evaluation on two tori. These StepData use *identical* P and K;
-- the transplant need not stay on any tree slice.
variable {P K} {c₀ : Side}
private lemma transplant_z (hb : P.Branches K G)
    (hv : f.val = c.val * P.L.val) (hc : 1 < c₀.val)
    (hu : ∀ i : Axis, ∀ x ∈ predSites P i, lift (wrap (c₀*P.L) x) = x) :
    let S : StepData c f := ⟨P,K,hv⟩
    let S₀ : StepData c₀ (c₀*P.L) := ⟨P,K,rfl⟩
    ∀ (k : S.Choices) (x : Site c) (i : Axis) (u : PairLogs G f c),
      ∃ (k₀ : S₀.Choices) (u₀ : PairLogs G (c₀*P.L) c₀), ‖u₀‖ ≤ ‖u‖ ∧
        ∀ v : ℝ, zTest S k (x,i) (v • u) = zTest S₀ k₀ (0,i) (v • u₀) := by
  intro S S₀ k x i u
  classical
  let f₀ := c₀*P.L
  haveI : Fact (1 < c₀.val) := ⟨hc⟩
  have ha : step i ≠ (0:Site c₀) := by
    intro he
    have h : (1 : ZMod c₀.val) = 0 := by simpa using congr_fun he i
    exact one_ne_zero h
  let k₀ : S₀.Choices := (fun y => if y=0 then k.1 x else k.1 (x+step i), fun _ => k.2 (x,i))
  let s := S.ratio.embed x
  let s₀ := S₀.ratio.embed 0
  let X (y : Site f₀) := wrap f (lift (y-s₀))+s
  let a₀ : LogField G f₀ := fun b => u.1 (X b.1,b.2)
  let b₀ : LogField G c₀ := fun _ => u.2 (pole (x,i))
  let u₀ : PairLogs G f₀ c₀ := (a₀, b₀)
  refine ⟨k₀,u₀,?_,fun v => ?_⟩
  · have h1 : ‖a₀‖ ≤ ‖u.1‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => norm_le_pi_norm u.1 _
    have h2 : ‖b₀‖ ≤ ‖u.2‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => norm_le_pi_norm u.2 _
    exact max_le_max h1 h2
  have hp : ∀ b : Edge Cover, b.1 ∈ predSites P i → expandAt s (represent (v • u.1)) b =
      expandAt s₀ (represent (v • a₀)) b := by
    rintro ⟨q,j⟩ hq
    have he : X (wrap f₀ q+s₀) = wrap f q+s := by unfold X; rw [add_sub_cancel_right,hu i q hq]
    change G.lieExp (v • u.1 _) * 1 = G.lieExp (v • u.1 (X (wrap f₀ q+s₀),_)) * 1
    rw [he]
  have hPred : S.prediction (represent (v • u.1)) k (x,i) = S₀.prediction (represent (v • a₀)) k₀ (0,i) := by
    rw [reads_at, reads_at]
    have ht : k₀.1 (0+step i)=k.1 (x+step i) := by dsimp only [k₀]; rw [zero_add, if_neg ha]
    change predictionAt P i K _ _ _ _ = predictionAt P i K _ _ _ _
    rw [ht, show k₀.1 0=k.1 x from if_pos rfl]
    exact predAt_eq P i K hb _ _ hp _ _ _
  change Z S (S.prediction (represent (v • u.1)) k) (represent (v • u.2)) (x,i) =
    Z S₀ (S₀.prediction (represent (v • a₀)) k₀) (represent (v • b₀)) (0,i)
  unfold Z; rw [hPred]; rfl
end transplant

/-- Fixed-patch quantitative estimate on the actual chart. This statement
    has no torus-dependent threshold. Works even for periodic degeneracies,
    since the transplantation can always fill its stencil from actual links. -/
lemma z_chart_cost (P : Patch) (K : KernelChoices) (G : Gauge) (hb : P.Branches K G) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧
    ∀ (c f : Side) (S : StepData c f), S.patch = P → S.kernel = K →
    ∀ (k : S.Choices) (i : Bond c) (u : PairLogs G f c), ‖zLin S u.1 u.2 i‖ ≤ C*‖u‖ ∧
      (‖u‖ ≤ r → ‖zTest S k i u - zLin S u.1 u.2 i‖ ≤ C*‖u‖^2) := by
  obtain ⟨c₀,hc,hu⟩ := reference_exists P
  let S₀ : StepData c₀ (c₀*P.L) := ⟨P,K,rfl⟩
  obtain ⟨C,r,hC,hr,h⟩ := fixed_z_price (S:=S₀) hb
  refine ⟨C,r,hC,hr,?_⟩
  rintro c f ⟨P',K',hv⟩ he hh k ⟨x,i⟩ u
  change P'=P at he; subst P'; change K'=K at hh; subst K'
  let S : StepData c f := ⟨P,K,hv⟩
  obtain ⟨k₀,u₀,ht,H⟩ := transplant_z hb hv hc hu k x i u
  have hz : zTest S k (x,i) u = zTest S₀ k₀ (0,i) u₀ := by
    simpa only [one_smul] using H 1
  have hm : zLin S u.1 u.2 (x,i) = zLin S₀ u₀.1 u₀.2 (0,i) := by
    have he := zTest_deriv (S:=S) hb k (x,i) u
    have hy : (fun v : ℝ => zTest S k (x,i) (v • u)) =
        (fun v : ℝ => zTest S₀ k₀ (0,i) (v • u₀)) := funext H
    rw [hy] at he
    exact he.unique (zTest_deriv (S:=S₀) hb k₀ (0,i) u₀)
  change ‖zLin S u.1 u.2 _‖ ≤ _ ∧ (‖u‖ ≤ _ → ‖zTest S k _ u - zLin S u.1 u.2 _‖ ≤ _)
  rw [hz,hm]
  have hv := h k₀ (0,i) u₀
  exact ⟨hv.1.trans (by gcongr), fun hy => (hv.2 (ht.trans hy)).trans (by gcongr)⟩
end YM.Next.Fluctuations
