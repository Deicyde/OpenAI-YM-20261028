import YM.EveryPhase.Compatibility
import YM.EveryPhase.Frequency

/-! # Attachment covers the hot vectors -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Set Filter MeasureTheory Spec Boundary Probe OS Org Next.BOUNDARY
open scoped Topology NNReal ContDiff InnerProductSpace
variable {G : Gauge} {C : Family G} {S T : Table C.book} {V : Chamber T timeAxis}
    {A : Spread V} {Y : Show.Rhythm (C:=C) S V A} {X : Wightman S}
    {J : X.operators.H →L[ℂ] V.H} {R : Algebra S} {W : Surface S}

variable {n m : ℕ}

private lemma closer (p : Heights n) (hp : p∈positiveHeight n) (m : ℕ) :
    Tendsto (fun u : ℝ≥0 × Heights m => dawn (Bid.bothH p u.2)) (edgeFilter m)
      (𝓝[shores (n+m)] (dawn (Bid.bothH p (0:Heights m)))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, (heights_valid m).mono fun _ hx => warmer (n+m) (etched (Work.C24.ordered hp hx.1))⟩
  have hm : Continuous (fun z : Heights m => Bid.bothH p z) := by
    apply continuous_pi; intro i; refine Fin.addCases ?_ ?_ i
    · intro i; simp only [Bid.bothH,Fin.append_left]; exact continuous_const
    intro i; simp only [Bid.bothH,Fin.append_right]; exact continuous_apply _
  have hh : Continuous (@dawn (n+m)) := by
    unfold dawn place points position; fun_prop
  exact ((hh.comp hm).tendsto 0).comp (heights_zero m)

lemma vector_cooled (I : Attachment X V J) (h : Show.Reveals R X.spin X.J Y W)
    (ht : Bid.Hull Y.bits Y.lift X.J) (hi : Y.lift.NonTangentialFree W)
    (v : Fin n → S.Union) (x : ℝ≥0 × Heights n) (hx : x∈margins n)
    (P : Joint n →L[ℂ] X.operators.H) (hP : ExtendsTensor X.operators v P)
    (f : Joint n) (hf : HasCompactSupport ⇑f) :
    hot Y.bits v (hat f) x=J (P (hat (chilled x.2 f hf))) := by
  haveI := edge_nontrivial n
  let A := hot Y.bits v (hat f) x
  let g := chilled x.2 f hf
  have hg : HasCompactSupport ⇑g := remains _ _ _
  let B := J (P (hat g))
  obtain ⟨D,F,hF,hZ⟩ := h.visible
  let C₀ := D (n+n)
  let r := Bid.bothT v v X.J
  let Q p (u : Joint _) := C₀.partialD (W.W _ r) (dawn (Bid.bothH x.2 p)) (joinedTest (hat f) u)
  have tp (u) (y : ℝ≥0 × Heights n) (hy : y∈margins n) :
      inner ℂ A (hot Y.bits v u y) = Q y.2 u := by
    unfold A Q; rw [hot_pair ht hi _ _ _ _ _ _ hx hy]
    exact (Work.C15.partialD_psi (hF (n+n)) (spectra h.I) Y.power.1 Y.power.2 h.I.axis r (Work.C24.ordered hx.1 hy.1) _).symm
  have hw : inner ℂ B B = W.W _ r (joinedTest (hat g) (hat g)) := by
    unfold B
    rw [show inner ℂ (J (P (hat g))) (J (P (hat g))) = inner ℂ (P (hat g)) (P (hat g)) from
      LinearIsometry.inner_map_map (⟨J.toLinearMap, I.acts.scale⟩ : X.operators.H →ₗᵢ[ℂ] V.H) _ _]
    exact I.inner_eq Y.linked ht hi hP hP _ _
  have hu : inner ℂ A A=inner ℂ B B := by
    apply Eq.trans (tp _ x hx)
    rw [hw]; exact boundary_tilt (hF (n+n)) (spectra h.I) x.2 x.2 _
      (warmer (n+n) (etched (Work.C24.ordered hx.1 hx.1))) f f hf hf
  have hp := closer x.2 hx.1 n
  let u := dawn (Bid.bothH x.2 (0:Heights n))
  have he : u∈ shores (n+n) := by
    obtain ⟨he,hh⟩ := tendsto_nhdsWithin_iff.mp hp
    exact (solid_fields _).mem_of_tendsto he hh
  obtain ⟨Ψ,hΨ,e⟩ := I.smears n v
  have hv : Tendsto (hot Y.bits v (hat g)) (edgeFilter n) (𝓝 B) := by
    unfold B; rw [extends_unique v hP hΨ]; exact e _ _ Y.linked _
  have hh := tendsto_const_nhds (x:=A) |>.inner (𝕜:=ℂ) hv
  have ha : Tendsto (fun y : ℝ≥0 × Heights n => Q y.2 (hat g)) (edgeFilter n) (𝓝 (Q 0 (hat g))) :=
    ((D (n+n)).tends (hF _) _ _ u he).tendsto.comp hp
  have hb : inner ℂ A B=inner ℂ B B := by
    refine (tendsto_nhds_unique_of_eventuallyEq hh ha ((heights_valid n).mono fun y hy => tp (hat g) y hy)).trans ?_
    rw [hw]; unfold Q
    rw [boundary_tilt (K:=C₀) (hF _) (spectra h.I) _ _ _ he f g hf hg,chilled_zero]
  apply sub_eq_zero.mp; change A-B=0
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right,hu, hb, ← inner_conj_symm B A, hb,
    inner_conj_symm]; simp

lemma hot_cont (B : Small S V) (v : Fin n → S.Union) {x : ℝ≥0 × Heights n} (hx : x∈margins n) :
    Continuous fun f : Joint n => hot B v f x := by
  let M := (∏ i, ‖B.bar x.1 (v i)‖)*‖V.omega‖
  have hp (f : Joint n) : ‖hot B v f x‖ ≤ M * weight f := by
    rw [weight_eq, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (f.integrable.norm.const_mul M)
    refine ae_of_all _ fun i => ?_
    rw [norm_smul]; exact mul_comm M ‖f i‖ ▸
      mul_le_mul_of_nonneg_left ((Work.C23.shot_control B x.1 n v x.2 hx.2).2 _) (norm_nonneg _)
  apply continuous_iff_continuousAt.mpr; intro t
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have hh : Continuous fun f : Joint n => M * weight (f-t) :=
    continuous_const.mul (weight_cont.comp (continuous_id.sub continuous_const))
  filter_upwards [(hh.tendsto t).eventually (gt_mem_nhds (show M*weight (t-t)<ε by simpa using hε))]
    with u hu
  rw [dist_eq_norm,show hot B v u x-hot B v t x=hot B v (u-t) x from ?_]
  · exact (hp (u-t)).trans_lt hu
  unfold hot; rw [← integral_sub (hot_int B v u hx) (hot_int B v t hx)]; simp [sub_smul]

lemma rangeClosed (I : Attachment X V J) : IsClosed (J.range : Set V.H) :=
  (⟨J.toLinearMap, I.acts.scale⟩ : X.operators.H →ₗᵢ[ℂ] V.H).isometry.isUniformInducing.isComplete_range.isClosed

lemma vector_in (I : Attachment X V J) (h : Show.Reveals R X.spin X.J Y W)
    (ht : Bid.Hull Y.bits Y.lift X.J) (hi : Y.lift.NonTangentialFree W)
    (v : Fin n → S.Union) (x : ℝ≥0 × Heights n) (hx : x∈margins n)
    (f : Joint n) : hot Y.bits v f x ∈ J.range := by
  let g j := Probe.cap j (port f)
  obtain ⟨P,hP,-⟩ := I.smears n v
  have hh j : hot Y.bits v (hat (g j)) x ∈ J.range :=
    ⟨_,(vector_cooled I h ht hi v x hx P hP (g j) (Probe.finite_cap j)).symm⟩
  have he : Tendsto (fun j => hat (g j)) atTop (𝓝 f) := by
    simpa only [Function.comp_def,g,Probe.travels] using! (hat.continuous.tendsto (port f)).comp (persistent (port f))
  exact (rangeClosed I).mem_of_tendsto (((hot_cont Y.bits v hx).tendsto f).comp he) (Eventually.of_forall hh)

lemma shot_in (I : Attachment X V J) (h : Show.Reveals R X.spin X.J Y W)
    (ht : Bid.Hull Y.bits Y.lift X.J) (hi : Y.lift.NonTangentialFree W)
    (v : Fin n → S.Union) (x : ℝ≥0 × Heights n) (hx : x∈margins n)
    (q : Points n) : Y.bits.shot x.1 n v x.2 q ∈ J.range := by
  have hJ : J.rangeᗮᗮ=J.range := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, (rangeClosed I).submodule_topologicalClosure_eq]
  rw [← hJ]
  apply (Submodule.mem_orthogonal ..).mpr; intro u hu
  let f := Y.bits.shot x.1 n v x.2
  have hg := (innerSL ℂ u).continuous.comp (Work.C23.shot_control Y.bits x.1 n v x.2 hx.2).1
  refine congr_fun (Work.C15.eq_of_tests (fun y => inner ℂ u (f y)) (fun _ => 0) hg continuous_const (fun g => ?_)) q
  have hv : inner ℂ u (hot Y.bits v g x)=0 := (Submodule.mem_orthogonal' ..).mp hu _ (vector_in I h ht hi _ _ hx g)
  simp only [zero_mul,integral_zero]; rw [← hv, hot, ← integral_inner (hot_int Y.bits v g hx)]
  simp only [inner_smul_right,f]; simp_rw [mul_comm]
end YM.EveryPhase
