import Mathlib.Analysis.Fourier.Convolution
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.FREE_RESOLVENT.Affine
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion
import YM.SectorNext.LARGE_FIELD_REMAINDERS.BondKernel


/-!
# First-derivative cost at a remote read

Don't appeal to differentiating a global tensor of default fderivs.
This module pays operator norm (O_L(chord)) on EACH physical fderiv
near flat after resolving patch reads. Uses same quadratic occupations
as BondPeriod, but stronger stand-alone propagation adapted to order 1
alone. In particular we don't take anything tending uniformly across c
from the EXISTENCE of analytic-at-one or zero-centered series with provenance
on all periods. To reuse the actual transfer proof (private API in
LARGE_FIELD_REMAINDERS/BondPeriod.lean and GAUSSIAN_SECTOR_CHANGE/Block.lean),
repeat BondPeriod's fixed cover construction below (`frameSites`
through `transport_q` taken verbatim with namespace adjusted). All the
true sizes chosen once at P,K. Makes that result public as `transfer`
for whoever needs such reads later. Also retain choice dependence
exactly. Face uses the four-link true path rule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open Next.Fluctuations Next.SectorChange Motion SectorNext.Remainder.Affine Push.SectorMeasure 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}
section raw
variable (P : Patch) (o : Axis)
-- Reuse fixed-address agreement technique of Next.Fluctuations.Prediction
-- (there the following raw methods are private).
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

end raw

private lemma transport_q (P : Patch) (K : KernelChoices) (h : P.Branches K G) {c₀ : Side}
    (hv : f.val = c.val*P.L.val) (hc : 1<c₀.val)
    (hu : ∀ i : Axis, ∀ x ∈ predSites P i,lift (wrap (c₀*P.L) x)=x) :
    let S : StepData c f := ⟨P,K,hv⟩; let S₀ : StepData c₀ (c₀*P.L) := ⟨P,K,rfl⟩
    ∀ (k : S.Choices) (x : Site c) (i : Axis), ∃ (k₀ : S₀.Choices) (y : Bond (c₀*P.L) → Bond f),
      ∀ U : Config G f, S.prediction U k (x,i) = S₀.prediction (U ∘ y) k₀ (0,i) := by
  intro S T k x i
  let f₀ := c₀*P.L
  haveI : Fact (1 < c₀.val) := ⟨hc⟩
  have ha : step i ≠ (0:Site c₀) := by
    intro he
    have h : (1 : ZMod c₀.val) = 0 := by simpa using congr_fun he i
    exact one_ne_zero h
  let k₀ : T.Choices := (fun y => if y=0 then k.1 x else k.1 (x+step i), fun _ => k.2 (x,i))
  let s := S.ratio.embed x
  let s₀ := T.ratio.embed 0
  let X (y : Site f₀) := wrap f (lift (y-s₀))+s
  let y (e : Bond f₀) : Bond f := (X e.1,e.2)
  refine ⟨k₀,y,?_⟩; intro U
  rw [reads_at, reads_at]; change predictionAt P i K _ _ _ _=predictionAt P i K _ _ _ _
  rw [show k₀.1 (0+step i)=k.1 (x+step i) by dsimp only [k₀]; rw [zero_add,if_neg ha], show k₀.1 0=k.1 x from if_pos rfl]
  refine predAt_eq P i K h _ _ ?_ _ _ _
  rintro ⟨z,a⟩ hz
  change U (wrap f z+s,a)= U (y (wrap _ z+s₀,a))
  unfold y X; dsimp only; rw [add_sub_cancel_right, hu i z hz]


/-- Fixed medium independent of c,f for any $P,K$. -/
lemma transfer (P : Patch) (K : KernelChoices) (h : P.Branches K G) :
    ∃ c' : Side, ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
      ∀ (k : S.Choices) (x : Bond c), let X : StepData c' (c'*P.L) := ⟨P,K,rfl⟩
      ∃ (k' : X.Choices) (y : Bond (c'*P.L)→Bond f), ∀ U : Config G f,
        S.prediction U k x = X.prediction (U ∘ y) k' (0,x.2) := by
  obtain ⟨c',hc,hr⟩ := reference_exists P
  refine ⟨c',?_⟩
  rintro c f ⟨P1,K1,e⟩ hP hK k x
  change P1=P at hP; change K1=K at hK; subst P1 K1
  exact transport_q P K h e hc hr k x.1 x.2

section Common
variable {E F R : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- Any fixed medium analytic at zeros yields constant times sup
parameter discount in the directional dual. This doesn't bound inverse
jets on sectors, just supplies compatibility of linearization when
holding masks/data as on some remote addresses. -/
lemma linear {X : E × F → R} (h : ContDiffAt ℝ ω X 0) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ Y : F, ‖Y‖ ≤ r →
      let F' y := fderiv ℝ (fun x : E => X (x,y)) 0
      ContDiffAt ℝ ω (fun x : E => X (x,Y)) 0 ∧ ‖F' Y - F' 0‖ ≤ C*‖Y‖ ∧ ‖F' 0‖ ≤ C := by
  let D := fderiv ℝ X
  obtain ⟨C,r,hC,hr,H⟩ := chart_linear_cost D 0 ((h.fderiv_right (by simp : (ω:WithTop ℕ∞)+1 ≤ ω)).analyticAt)
  obtain ⟨b,hb,Hb⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (h.eventually (by simp))
  let L := ContinuousLinearMap.inl ℝ E F
  let A (y : F) := fderiv ℝ (fun x : E => X (x,y)) 0
  have ht (y : F) (hy : ‖y‖ ≤ b) :
      A y=(D (0,y)).comp L ∧ ContDiffAt ℝ ω (fun x : E => X (x,y)) 0 := by
    have HH := Hb (x:=((0:E),y)) (Metric.mem_closedBall.mpr (by simpa [Prod.norm_def] using hy))
    refine ⟨?_,HH.comp (f:=fun (x:E) => (x,y)) 0 (contDiffAt_id.prodMk contDiffAt_const)⟩
    have he : HasFDerivAt (fun x : E => (x,y)) L 0 := by
      have hh := (hasFDerivAt_id (𝕜:=ℝ) (0:E)).prodMk (hasFDerivAt_const y 0)
      exact hh
    exact (((by simpa only using (HH.differentiableAt (by simp)).hasFDerivAt : HasFDerivAt X _ ((fun x:E => (x,y)) 0))).comp (f:=fun x:E=> (x,y)) 0 he).fderiv
  refine ⟨C*‖L‖+‖A 0‖+1,min r b,by positivity,lt_min hr hb, fun Y hy => ⟨(ht Y (hy.trans (min_le_right ..))).2,?_,?_⟩⟩
  · change ‖A Y-A 0‖ ≤ _
    rw [(ht Y (hy.trans (min_le_right ..))).1,(ht 0 (by simpa using hb.le)).1, ← ContinuousLinearMap.sub_comp]
    have hf := H (0,Y) (by simpa [Prod.norm_def] using (hy.trans (min_le_left ..)))
    change ‖D (0,Y)-_‖ ≤ _ at hf
    simp only [sub_zero,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] at hf
    apply (ContinuousLinearMap.opNorm_comp_le ..).trans
    change ‖D (0,Y)-D 0‖*‖L‖ ≤ (C*‖L‖ + ‖(D 0).comp L‖+1)*‖Y‖
    apply (mul_le_mul_of_nonneg_right hf (norm_nonneg L)).trans; calc
      C*‖Y‖*‖L‖ = C*‖L‖*‖Y‖ := by ring
      _ ≤ _ := by gcongr; linarith [norm_nonneg ((D 0).comp L)]
  nlinarith [norm_nonneg L]
end Common

-- literal prediction fderiv, no period dependence
section Bond
lemma transfer_cost (P : Patch) (K : KernelChoices) (G : Gauge) (h : P.Branches K G) :
    ∃ A r : ℝ, 0<A ∧ 0<r ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
      ∀ (k : S.Choices) (i : Bond c) (Y : Directions G f), ‖Y‖ ≤ r →
        let U := absolutize Y
        let H (w : Config G f):= fderiv ℝ (bTest w k i) 0
        ContDiffAt ℝ ω (bTest U k i) 0 ∧ ‖H U-H 1‖ ≤ A*‖Y‖ ∧ ‖H 1‖ ≤ A := by
  obtain ⟨c',hi⟩ := transfer P K h
  let f':=c'*P.L; let T : StepData c' f':=⟨P,K,rfl⟩
  let F (a : T.Choices × Axis) (x : Directions G f' × Directions G f') := qTangent T (0,a.2) a.1 ((x.1,x.2,(0:G.Color)):BondTest G f')
  have hf (a) : ContDiffAt ℝ ω (F a) 0 := by
    let w := fun x : Directions G f' × Directions G f' => ((x.1,x.2,(0:G.Color)):BondTest G f')
    exact ContDiffAt.comp (g:=qTangent T (0,a.2) a.1) (f:=w) 0 ((bond_germ T h a.1 (0,a.2)).2) (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_const))
  choose C r hC hr H using fun a => linear (X:=F a) (hf a)
  let A := 1+∑ a,C a; let M:=(univ.image r).min' (univ_nonempty.image r)
  have ha : 0 < A := by have h1 := sum_nonneg (f:=C) (s:=univ) fun a _ => (hC a).le; unfold A; linarith
  have hM : 0 < M := by have hx := min'_mem (univ.image r) (univ_nonempty.image r); obtain ⟨a,-,hu⟩ := mem_image.mp hx; unfold M; rw [← hu]; exact hr _
  refine ⟨A,M,ha,hM,?_⟩; intro c f S hP hK k i Y hv U Q
  obtain ⟨k0,y,hy⟩ := hi S hP hK k i
  let a := (k0,i.2)
  let L : Directions G f →L[ℝ] Directions G f' := (LinearMap.funLeft ℝ G.Color y).toContinuousLinearMap
  have hl (w) : ‖L w‖ ≤ ‖w‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => norm_le_pi_norm w (y j)
  have HX : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using hl)
  let Q' (Y : Directions G f') := fun x : Directions G f' => F a (x,Y)
  have ht (Y) : bTest (absolutize Y) k i=(Q' (L Y)) ∘ L := by
    funext x; unfold bTest out Q' F qTangent qForecast
    rw [hy,hy]; simp only [increment_zero]; rfl
  have hp j : M ≤ r j := min'_le _ _ (mem_image_of_mem _ (mem_univ _))
  have he (b : Directions G f') (hb : ‖b‖ ≤ r a) := H a b hb
  obtain ⟨hs,hH,hG⟩ := he (L Y) ((hl _).trans (hv.trans (hp a)))
  obtain ⟨hs',-⟩ := he 0 (by rw [norm_zero]; exact (hr _).le)
  change ContDiffAt ℝ ω (Q' _) _ at hs hs'
  let m b := fderiv ℝ (Q' b) 0
  have h0 : absolutize (0:Directions G f)=1 := by ext; simp [absolutize]
  have HQ : ∀ b : Directions G f, ContDiffAt ℝ ω (Q' (L b)) 0 → Q (absolutize b)=(m (L b)).comp L := by
    intro b hb; unfold Q; rw [ht, fderiv_comp _ (by rw [map_zero]; exact hb.differentiableAt (by simp)) L.differentiableAt,L.fderiv, map_zero]
  have h01 : Q 1=(m 0).comp L := by rw [← h0,HQ,map_zero]; rw [map_zero]; exact hs'
  have hc : C a ≤ A := (single_le_sum (f:=C) (fun a _ => (hC a).le) (mem_univ a)).trans (le_add_of_nonneg_left zero_le_one)
  unfold U
  rw [ht] -- only first occurrence
  refine ⟨ContDiffAt.comp (g:=Q' (L Y)) (f:=(L:Directions G f → _)) 0 (by rw [map_zero]; exact hs) L.contDiff.contDiffAt, ?_, ?_⟩
  · rw [HQ _ hs,h01,← ContinuousLinearMap.sub_comp]
    exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) HX).trans (hH.trans (by gcongr; apply hl)))
  rw [h01]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) HX).trans (hG.trans hc))
end Bond
end YM.AnalyticBridge.LocalGaussianLaws.Remote
