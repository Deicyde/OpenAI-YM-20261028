import YM.RemainderComparison.Cascade.Unison
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Charm

/-!
# Event in the mixed marked/force sweep

Per-vertex product variation with the payloads held at their actual inputs,
*all* anchors accounted, strict distinction marks / inherited E / other via
the `ember` budget parameter. No differentiability assumption on marks. No
period factor in the price. Extension even allows arbitrary subset remainder.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cascade
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R)(X:Coat T F)(H:Cash W x μ L Q o C T R) {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {V:E→Config G c} {y:E} {f':E→Directions G f}{z':Air f G}{g:E→Air f G}
variable {l:Head S→ℝ}{L':ℝ}
lemma warning_absent (i: WarningAt c f): Sum.inr (.inr (.inr i)) ∉ M.signs S:=by
  intro h
  obtain ⟨x,hx,ht⟩ := mem_image.mp h
  cases hz:x.turn <;> simp only [hz,Wing.badge,Sum.inr.injEq] at ht <;> contradiction
lemma keeps_blaze : blaze (p\M.signs S)=blaze p:=by
  ext i
  simp only [blaze,mem_toRight]; exact Finset.mem_sdiff.trans (and_iff_left (warning_absent M i))
lemma spanR (i:Head S) : 0≤ spanW T R X.B m i:=by
  cases i; · exact zero_le_one
  exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
omit [FiniteDimensional ℝ E] in
lemma acres (he : troupe T R Q.halo (radiusB x) p)(hA : M.signs S ⊆ p)(k:Finset ℕ)
    (H₀: Stamp T) (hX:X.x=x)(ht:X.width=o.K)(hu:X.manifest)(hV : Mode V y j v)(hr: Clutch X z' o.a R.beta d y j V f' g) (hB : 0≤B)(hL:0≤L')
    (hC : ∀ m∈M.own, Brush j m.weight (B*spanW T R X.B Q.halo (m.turn.badge S)) (fun t=> m.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z'))) y)
    (hD : ∀ i∈p\M.signs S, Brush j (l i) (L'*spanW T R X.B Q.halo i) (fun t=> Polar.ember (vary X (V t)) o.a R W Q.table (f' t) (X.input (worldZ X R.beta z')) (g t) k Q.halo i) y) :
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun _=> M.weight*∏ i∈p\M.signs S,l i) z') ((L'+B)*(2*H.shapeW p))
      (fun t=> M.floret (vary X (V t)) p W o.a Q.table k Q.halo (g t)) y:=by
  let u i (t:E):=Polar.ember (vary X (V t)) o.a R W Q.table (f' t) (X.input (worldZ X R.beta z')) (g t) k Q.halo i
  let a (m:Leaf R) t:= m.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z')); let s:=p\M.signs S
  let F t:= (∏ m∈M.own, a m t)*∏ i∈s,u i t
  have hU : (fun t=>M.floret (vary X (V t)) p W o.a Q.table k Q.halo (g t))=ᶠ[𝓝 y] F:=by
    filter_upwards [hr.patch] with z hv
    unfold Team.floret; rw [if_pos hA]; unfold F u a Polar.floating Team.paidU; simp_rw [hr.moving z]
    let Z:= vary X (V z); have hv' := plastic hv hr.pulse
    exact congr_arg₂ (·*·) (Finset.prod_congr rfl (fun i _=> i.canv Z _ _ _ hv')) (Finset.prod_congr rfl fun i _=> hv'.reeled (show Room P S _ Z.x from hX.symm ▸ H.laws.data.room) W _ _ _ (show Intake P _ Z.x R from hX.symm ▸ H.laws.intake) i (g z))
  apply Brush.shimmy _ hU
  let S' := X.catastrophe (o.ξ/2) R.beta (blaze p)
  by_cases hy:z' ∈ S'
  · rw [Set.indicator_of_mem hy]
    have hp:= ((Brush.all_prod _ a _ _ hC).paints (Brush.all_prod _ u _ _ hD)); apply hp.climb le_rfl
    rw [← Finset.mul_sum, ← Finset.mul_sum]; let w:= spanW T R X.B Q.halo
    have hn : (∑ i∈M.own, w (i.turn.badge S))=∑i∈ M.signs S,w i := Eq.symm (Finset.sum_image fun _ h _ h' hz=> M.alone h h' (Team.badged S hz))
    change B*(∑i∈M.own,w (i.turn.badge S))+L'*∑i∈s,w i≤_
    rw [hn]
    have ha: B*(∑ i∈M.signs S,w i)≤(L'+B)*(∑ i∈M.signs S,w i):= mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL) (sum_nonneg fun i _=>spanR X i)
    have hb:L'* (∑ i∈s,w i)≤(L'+B)* (∑ i∈s,w i):= mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (sum_nonneg fun i _=>spanR X i)
    apply (add_le_add ha hb).trans; rw [← mul_add,show ((∑ i∈M.signs S,w i)+∑ i∈s,w i)=∑ i∈p,w i from add_comm _ _|>.trans (Finset.sum_sdiff hA)]; unfold w; rw [show X.B=radiusB x from congr_arg radiusB hX]
    exact mul_le_mul_of_nonneg_left (Utopia.worthy p he) (add_nonneg hL hB)
  rw [Set.indicator_of_notMem hy]; refine Brush.zi ?_ le_rfl (mul_nonneg (add_nonneg hL hB) (mul_nonneg zero_le_two (H.positive_volume p)))
  unfold S' catastrophe Poll.Crash at hy; change ¬ (∀ i∈_,∃ j, _≤_ ∧ _≤_) at hy; push Not at hy
  obtain ⟨i,hi,hp'⟩:=hy
  have hc : Cash W X.x μ L Q o C T R:= hX.symm ▸ H; have hx:=hr.sleek hc hV H₀ hu ht i (fun i hi =>(hp' i hi).le) k
  filter_upwards [hx] with v hZ
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_sdiff.mpr ⟨mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi)), warning_absent M i⟩) hZ)
section
variable {B':ℝ}{I:Finset (Bond f)}{k:ℕ}
omit [FiniteDimensional ℝ E] in
lemma measures (hv : troupe T R Q.halo (radiusB x) p)(hA : M.signs S⊆p) (h₀:Stamp T) (hX:X.x=x)(ht:X.width=o.K)
    (hu:X.manifest)(hV : Mode V y j v)(hr: Clutch X z' o.a R.beta d y j V f' (fun i=>course X A R.beta z' (V i))) (hB : 0≤B)(hL:0≤L')
    (hC : ∀ m∈M.own, Brush j m.weight (B*spanW T R X.B Q.halo (m.turn.badge S)) (fun t=> m.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z'))) y)
    (hD : ∀ i∈p\M.signs S, Brush j (l i) (L'*spanW T R X.B Q.halo i) (fun t=> Polar.ember (vary X (V t)) o.a R W Q.table (f' t) (X.input (worldZ X R.beta z')) (course X A R.beta z' (V t)) (own p) Q.halo i) y)
    (hT : Brush j 1 (B'*facescale I z'^k) (fun i=> scalp I X (V i) R.beta A z') y)(h':0≤B') :
    let K':=M.weight * ∏i∈p\M.signs S, l i
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun z=> K'*(1+B'+2*(L'+B))^j*(1+H.shapeW p)^j*facescale I z^(k*j)) z') 1
      (fun i=> M.chimes X p I (V i) A Q.table W o.a Q.halo z') y := by
  intro P'; have h := (hT.paints (acres M X H hv hA (own p) h₀ hX ht hu hV hr hB hL hC hD)).trim
  refine h.climb ?_ le_rfl
  by_cases hx:z'∈X.catastrophe (o.ξ/2) R.beta (blaze p)
  swap; · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,mul_zero,zero_mul]
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,one_mul]; change P'* _ ≤ _
  let f:=facescale I z'; let g:= L'+B; let D:=1+H.shapeW p; have ht':0≤g:=add_nonneg hL hB; have hF:1≤f:= (Flux.expenses ..).1; have hv':1≤D:=le_add_of_nonneg_right (H.positive_volume p)
  have h₁:1≤ f^k:= one_le_pow₀ hF; have h₂ : 1+(B'*f^k+g*(2*H.shapeW p))≤(1+B'+2*g)*D*f^k:=by
    have hc : f^k ≤ D*f^k:= le_mul_of_one_le_left (zero_le_one.trans h₁) hv'
    have hS:H.shapeW p ≤ D*f^k:= (show H.shapeW p ≤ D from le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (zero_le_one.trans hv') h₁)
    have ha:1≤ D*f^k:= h₁.trans hc
    nlinarith only [mul_le_mul_of_nonneg_left hc h', mul_le_mul_of_nonneg_left hS ht',ha]
  have he : 0 ≤ 1+(B'*f^k+g*(2*H.shapeW p)):=add_nonneg zero_le_one (add_nonneg hT.pos (mul_nonneg ht' (mul_nonneg zero_le_two (H.positive_volume p))))
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he h₂ j) (show 0≤P' from mul_nonneg M.profit (prod_nonneg fun i hi=> (hD i hi).nonneg))).trans_eq ?_
  rw [mul_pow,mul_pow,pow_mul]; unfold f g D; ring
end
end YM.RemainderComparison.Cascade
