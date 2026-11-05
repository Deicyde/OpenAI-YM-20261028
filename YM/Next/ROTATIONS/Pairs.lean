import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Climb.Beams
import YM.Next.ROTATIONS.Collision



/-!
# Pair kernels and singular order. Uses S, no extension trace at diagonal. -/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Row Word OS Table Ward Climb
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius NNReal ENNReal InnerProductSpace
variable {G : Gauge} {L : Register G} {S : Table L}

lemma rowin {x y : E4} (h : x≠y) : points ![x,y]∈conf _ := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm h]
lemma pair_meas (H : S.Hierarchy) (v w : S.Tag) : Measurable (pair v w) := by
  apply measurable_of_measurable_on_compl_singleton (0:E4)
  refine Continuous.measurable ?_
  apply continuousOn_iff_continuous_restrict.mp
  let M : E4→L[ℝ] Points 2 := LinearMap.toContinuousLinearMap {
    toFun x := points ![x,0]
    map_add' x y := by ext1 i; fin_cases i <;> simp,
    map_smul' c y := by ext1 i; fin_cases i <;> simp }
  refine ContinuousOn.comp (g:=disc ![v,w]) ((S.class_smooth S H.smooth _).continuousOn) M.continuous.continuousOn (fun x hx => rowin hx)
lemma pair_bound (H : S.Hierarchy) (v w : S.Tag) : ∃ D, ScaleCap D (pair v w) := by
  let t : Fin 2 → S.Tag := ![v,w]
  obtain ⟨D,C,hC,h⟩ := H.order 2 (fun i => (t i).1) (fun i => S.representative _ (t i).2) 0
  refine ⟨D,C,hC,fun x r hr he hl => ?_⟩
  have hg : spaced r (points ![x,0]) := by
    intro i j hij
    change r ≤ cubedist (![x,(0:E4)] i) (![x,0] j)
    fin_cases i <;> fin_cases j <;> simp_all [cubedist,rad]
  have hu := h r hr he _ hg; rw [norm_iteratedFDeriv_zero] at hu; exact hu
lemma pair_flip (H : S.Hierarchy) (v w : S.Tag) {x : E4} (hx : x≠0) : pair v w x=pair w v (-x) := by
  have h := scan H (x,expose v) (0,expose w) (by exact hx); have hh := scan H (0,expose w) (x,expose v) (by exact Ne.symm hx)
  simp only [sends_back,sub_zero,zero_sub] at *
  rw [← h, ← hh]
  exact S.order H.laws.toSymmetric (show distinct [(0,expose w),(x,expose v)] from locations.mpr (by simp [Ne.symm hx])) (List.Perm.swap ..)
lemma pair_dif (H : S.Hierarchy) (v w : S.Tag) (P : DiffPlan S) (hp : P.Derivatives S) (i : Axis) (x : Tang) (hx : x≠0) (t) :
    HasDerivAt (fun u => pair v w (make i (u,x))) (pair (Ward.rise P i v) w (make i (t,x))) t := by
  let X (t : ℝ) : Points 2 := points ![make i (t,x),0]
  let f := disc ![v,w]; let y := make i (0,x)
  have he : X = fun t : ℝ => X 0+t • Points.direction 0 i := by
    ext1 z; apply PiLp.ext; intro k; fin_cases k <;> simp [X,make_eq,Points.direction,add_comm]
  have ht : HasDerivAt X (Points.direction 0 i) t := by
    conv => arg 1; rw [he]
    simpa using (ContinuousLinearMap.toSpanSingleton ℝ (Points.direction 0 i)).hasDerivAt (x:=t) |>.const_add (X 0)
  have hy : X t∈conf 2 := rowin (made_of_ne i x hx t)
  have hh : Analysis.D (Points.direction 0 i) (disc ![v,w]) (X t)=pair (Ward.rise P i v) w (make i (t,x)) := by
    rw [fromD P H hp hy]; unfold pair
    congr 2; ext1 j; fin_cases j <;> simp
  rw [← hh]
  exact (cont_disc H _ hy).differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt t ht
lemma pair_dif_neg (H : S.Hierarchy) (v w : S.Tag) (P : DiffPlan S) (hp : P.Derivatives S) (i : Axis) (x : Tang) (hx : x≠0) (t) :
    HasDerivAt (fun u => pair v w (make i (u,x))) (-pair v (Ward.rise P i w) (make i (t,x))) t := by
  have hv u : make i (-u,-x) = -make i (u,x) := by
    apply PiLp.ext; intro j; by_cases he : j=i; · subst j; simp [make_time]
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq he; simp [make_other]
  rw [show (fun u => pair v w (make i (u,x)))=(fun u => pair w v (make i (-u,-x))) by
    ext1 u; rw [pair_flip H v w (made_of_ne _ _ hx _),hv],pair_flip H v _ (made_of_ne _ _ hx _),← hv]
  simpa [Function.comp_def] using (pair_dif H w v P hp i (-x) (neg_ne_zero.mpr hx) (-t)).scomp t (hasDerivAt_neg' t)

-- signed convention
abbrev colorSign (s : Signed) (i : Axis) := signValue (s.flip i)
lemma tensor_signed (J : Stress S) (H : S.Hierarchy) (h : RawTensor H.spin J) (a b : Axis) (s : Signed) :
    S.mirror H.spin 4 s (J a b)=(colorSign s a*colorSign s b) • J (s.perm a) (s.perm b) := by
  rw [h]; rw [Finset.sum_eq_single (s.perm a),Finset.sum_eq_single (s.perm b)]
  · rw [Signed.matrix_at,Signed.matrix_at]; cases hx : s.flip a <;> cases hy : s.flip b <;> simp [hx,hy,colorSign,signValue]
  · intro i hi hh; rw [Signed.matrix_at s b]; simp [Ne.symm hh]
  · simp
  · intro i hi hh; simp [Signed.matrix_at,Ne.symm hh]
  · simp
abbrev tag (J : Stress S) (a b : Axis) : S.Tag := ⟨4,J a b⟩
abbrev linePair (J : Stress S) (a b c d) (p : E4) := pair (tag J a b) (tag J c d) p
lemma shifted (H : S.Hierarchy) (v w : S.Tag) {x : E4} (hx : x≠0) (s : Signed) :
    pair ⟨_,S.mirror H.spin v.1 s v.2⟩ ⟨_, S.mirror H.spin w.1 s w.2⟩ (Ortho.move s.ortho x)=pair v w x := by
  have hm p : S.classTokens (L.move s (expose (S:=S) p))=⟨_,S.mirror H.spin p.1 s p.2⟩ := by
    cases p with | mk d x =>
    dsimp only [classTokens,Register.move,expose]; rw [← S.mirror_project,S.rep]
  have he : points ![x,(0:E4)]∈conf 2 := rowin hx
  have h := H.spin.mirror s he ![expose v,expose w]
  rw [← Table.at_project S S H.laws.toSymmetric (fun _ => le_rfl) (Points.move_in _ he),
    ← Table.at_project S S H.laws.toSymmetric (fun _ => le_rfl) he] at h
  have heq : S.classTokens ∘ ![expose v,expose w]= ![v,w] := by ext1 j; fin_cases j <;> simp
  rw [heq] at h
  unfold pair disc
  rw [show points ![Ortho.move s.ortho x,0]=Points.move s.ortho (points ![x,0]) by ext1 j; fin_cases j <;> simp [-Ortho.motion_at,← Ortho.motion_at]]
  refine Eq.trans ?_ h; congr 1
  ext1 j; fin_cases j <;> simp [hm]
lemma pair_scalar (v w : S.Tag) (a b : ℂ) (x : E4) : pair ⟨_,a • v.2⟩ (⟨w.1,b • w.2⟩:S.Tag) x=a*b*pair v w x := by
  let q : Fin 2→S.Tag := ![v,w]
  let y := points ![x,(0:E4)]
  let r := update q 1 (⟨_,b • w.2⟩:S.Tag)
  have he (p : S.Field v.1) : update r 0 (⟨_,p⟩:S.Tag) = ![⟨_,p⟩,⟨_,b • w.2⟩] := by ext1 j; fin_cases j <;> simp [r]
  have ht (p : S.Field w.1) : update q 1 (⟨_,p⟩:S.Tag)= ![v,⟨_,p⟩] := by ext1 j; fin_cases j <;> simp [q]
  unfold pair; rw [← he,← takes,_root_.map_smul,takes,he, Sigma.eta,← ht, ← takes,_root_.map_smul,takes,ht]; simp [mul_assoc]
lemma moved_pair (H : S.Hierarchy) (J : Stress S) (h : RawTensor H.spin J) (i j k l) (s : Signed) (x) (hx : x≠0) :
    colorSign s i * colorSign s j * (colorSign s k * colorSign s l) *
      linePair J (s.perm i) (s.perm j) (s.perm k) (s.perm l) (Ortho.move s.ortho x)=linePair J i j k l x := by
  unfold linePair
  rw [← shifted H (tag J i j) (tag J k l) hx s]; dsimp only [tag]
  rw [tensor_signed J H h,tensor_signed J H h]; exact (pair_scalar ..).symm
end YM.Outer
