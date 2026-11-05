import YM.Next.EXTRACTION.Raw
import YM.Next.FOUNDATIONS.SU2
import YM.SectorNext.LARGE_FIELD_REMAINDERS.BondKernel
import YM.Work.C22


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Uniform release of Q affine response estimates

Like for z_chart_cost, carry the *actual k shared choices* back to a fixed medium
and keep the constants there even when returning the tangent calculation. The earlier
fixed-z test only transfers along common scaling, need here to transfer under
increments & fixed base as well. We keep whole finite reader agreement. Reference
macros neither assume nor reconstruct an F0 independently of inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
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

private lemma bounded (S : StepData c f) (hB : S.patch.Branches S.kernel G) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ (k : S.Choices) (i : Bond c),
    ∀ u : BondTest G f, ∀ v : ℝ, ‖u‖ ≤ v → v ≤ r →
    let a := response (qTangent S i k) u.1 u.2
    let w := chordColor S i k
    DifferentiableAt ℝ (fun t : ℝ => qTangent S i k (t • u.1,u.2)) 0 ∧
    DifferentiableAt ℝ (fun t : ℝ => G.mat (qForecast S i k (t • u.1,u.2))) 0 ∧
    ‖w u-(w (0,u.2)-a)‖ ≤ C*v^2 ∧ ‖w u‖ ≤ C*v ∧ ‖w (0,u.2)‖ ≤ C*v ∧ ‖a‖ ≤ C*v := by
  choose C r hC hr H using fun i : S.Choices × Bond c => bond_expense S hB i.1 i.2
  let A := 1+∑ j, C j
  let M := (Finset.univ.image r).min' (Finset.univ_nonempty.image r)
  refine ⟨A,M,?_, ?_, fun k i u v hu hv => ?_⟩
  · have hx : 0 ≤ ∑ j, C j := sum_nonneg fun j _ => (hC j).le
    unfold A; positivity
  · have hm : M∈ Finset.univ.image r := min'_mem _ _
    obtain ⟨k,-,he⟩ := mem_image.mp hm; exact he ▸ hr k
  let j : S.Choices × Bond c := (k,i)
  have hd' : C j ≤ A := (single_le_sum (f:=C) (fun i _ => (hC i).le)
    (mem_univ j)).trans (by unfold A; simp)
  have hp : 0 ≤ v := (norm_nonneg u).trans hu
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := H (k,i) u v hu (hv.trans (min'_le _ _ (mem_image_of_mem _ (mem_univ j))))
  exact ⟨h1,h2,h3.trans (mul_le_mul_of_nonneg_right hd' (sq_nonneg _)),
    h4.trans (mul_le_mul_of_nonneg_right hd' hp),h5.trans (mul_le_mul_of_nonneg_right hd' hp),h6.trans (mul_le_mul_of_nonneg_right hd' hp)⟩

set_option maxHeartbeats 560000 in
lemma postage (P : Patch) (K : KernelChoices) (G : Gauge) (h : P.Branches K G) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ (c f : Side) (S : StepData c f), S.patch=P → S.kernel=K → ∀ (k : S.Choices) (i : Bond c),
    ∀ u : BondTest G f, ∀ v : ℝ, ‖u‖ ≤ v → v ≤ r →
    let a := response (qTangent S i k) u.1 u.2; let w := chordColor S i k
    DifferentiableAt ℝ (fun t : ℝ => qTangent S i k (t • u.1,u.2)) 0 ∧
    DifferentiableAt ℝ (fun t : ℝ => G.mat (qForecast S i k (t • u.1,u.2))) 0 ∧
    ‖w u-(w (0,u.2)-a)‖ ≤ C*v^2 ∧ ‖w u‖ ≤ C*v ∧ ‖w (0,u.2)‖ ≤ C*v ∧ ‖a‖ ≤ C*v := by
  obtain ⟨c₀,hc,hu⟩ := reference_exists P
  let f₀ := c₀*P.L
  let S₀ : StepData c₀ f₀ := ⟨P,K,rfl⟩
  obtain ⟨C,r,hC,hr,H⟩ := bounded S₀ h
  refine ⟨C,r,hC,hr,?_⟩
  rintro c f ⟨P',K',hv⟩ he ha k ⟨x,i⟩ a v hq hA
  change P'=P at he; subst P'; change K'=K at ha; subst K'
  let S : StepData c f := ⟨P,K,hv⟩
  let e : Bond c := (x,i)
  obtain ⟨k₀,y,hy⟩ := transport_q P K h hv hc hu k x i
  let b (u : BondTest G f) : BondTest G f₀ := (u.1 ∘ y,u.2.1 ∘ y,u.2.2)
  have hx : ∀ u : BondTest G f,qForecast S e k u=qForecast S₀ (0,i) k₀ (b u) := fun u => hy _
  have hab : ‖b a‖ ≤ ‖a‖ := by
    refine max_le_max ?_ (max_le_max ?_ le_rfl)
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg a.1)).mpr fun j => norm_le_pi_norm a.1 (y j)
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg a.2.1)).mpr fun j => norm_le_pi_norm a.2.1 (y j)
  have hX (t : ℝ) : qTangent S e k (t • a.1,a.2)=qTangent S₀ (0,i) k₀ (t • (b a).1,(b a).2) := by unfold qTangent; simp only [hx]; rfl
  have hm (t : ℝ) : G.mat (qForecast S e k (t • a.1,a.2)) = G.mat (qForecast S₀ (0,i) k₀ (t • (b a).1,(b a).2)) := by rw [hx]; rfl
  have hn (t : ℝ) : chordColor S e k (t • a.1,a.2)=chordColor S₀ (0,i) k₀ (t • (b a).1,(b a).2) := by unfold chordColor; rw [hx]; rfl
  -- t inferred ℕ! annotate
  have hg : chordColor S e k a=chordColor S₀ (0,i) k₀ (b a) := by simpa only [one_smul,Prod.mk.eta] using! hn 1
  have hg' := hn 0; rw [zero_smul,zero_smul] at hg'
  dsimp only; change DifferentiableAt _ (fun t : ℝ => qTangent S e k _) _ ∧ DifferentiableAt _ (fun t : ℝ => G.mat (qForecast S e k _)) _ ∧
    ‖chordColor S e k a-(chordColor S e k _-response (qTangent S e k) _ _)‖ ≤ _ ∧ ‖chordColor S e k a‖ ≤ _ ∧ ‖chordColor S e k _‖ ≤ _ ∧ ‖response (qTangent S e k) _ _‖ ≤ _
  unfold response; simp_rw [hX,hm,hg,hg']
  exact H k₀ (0,i) (b a) v (hab.trans hq) hA
end YM.SectorNext.Remainder.Affine
