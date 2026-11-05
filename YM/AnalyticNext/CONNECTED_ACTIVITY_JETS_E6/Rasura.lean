import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Parterre


/-!
# Pull a gauge-covariant formula from a true flat log chart around evaluation

Keep saturated derivative budgets. Here `spectrum_jet` does not assume interior
membership persists (boundary flag equality); uses `Safe` ONLY at calculation
point. Post L. Use `Brush` COMP where reanchoring costs paid up to queried order. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel    Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side} {E F Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
variable [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {j : ℕ}
open Brush

lemma base_ray (P : Teller G) (L : Side) (j : ℕ) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (hv : ∀ᶠ x in atTop,0≤V x) :
    ∃ Q : ℝ→ℝ, Rate G L (-(1/2)) Q ∧ ∀ᶠ s in atTop, 0≤Q s ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), Works P L s S T →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : E → Config G c) (x:E) (p : ℕ) (o : Site c),
    Mode U x j (V s) → p ≤ 32*radiusB s→ Clean (U x) s o (p+1) →
      ∃ (z : Site c→ G.El) (L : E→ Directions G c), Brush j (Q s) 1 L x ∧
        ∀ᶠ i in 𝓝 x, AgreeNear id o p (gauge z (U i)) (increment 1 (L i)) := by
  obtain ⟨C,hC,hP⟩:= flattening P L
  obtain ⟨J,d,hJ⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨e,he,hy⟩ := Metric.nhds_basis_closedBall.mem_iff.mp G.plog_left
  obtain ⟨f,r,hf,hr,h⟩:= chord_chart_cost G
  let D x:= (1+royalty G)*V x
  let K : ℝ := j.factorial*J
  have hx := hJ.value; have hk : 0≤K := by unfold K; positivity
  have hD : Rate G L (-(1/2)) D := ‹Rate _ _ _ V›.mul_left _
  refine ⟨fun x=> C x+K* D x,hC.add (hD.mul_left K),?_⟩
  filter_upwards [hP,hv,hD.below (by norm_num) 1 zero_lt_one,hC.below (by norm_num) (min r e) (lt_min hr he),
    ((hC.mul_left f).mul_right (royalty G)).below (by norm_num) d hJ.pos, room G P L] with x hp hv hz he hx hr
  have ht : 0≤ D x := by unfold D; have hh:=royalty_ge G; positivity
  have ht' := add_nonneg hp.1 (mul_nonneg hk ht)
  refine ⟨ht',?_⟩
  intro c f' S T hS E _ _ U X p o hU hf' hw
  obtain ⟨z,b,hb,hB⟩:= hp.2 _ _ S T hS.length_eq (hr _ _ S T hS) (U X) o p hf' hw
  let g x:= gauge z (U x); let L' (x:E) (j : Bond c) := if separation o j.1 ≤ p then G.plog (G.mat (g x j)) else 0
  obtain ⟨hR,hE⟩ := le_min_iff.mp ((le_abs_self _).trans he)
  have he (i : Bond c) (hi : separation o i.1 ≤ p) : ‖L' X i‖ ≤ C x ∧ ‖G.mat (g X i)-1‖ ≤ d := by
    let y := b (pole i); have hb' : ‖y‖ ≤ C x := (norm_le_pi_norm _ _).trans hB
    have hg : g X i=G.lieExp y := by rw [show g X i=_ from hb i hi]; unfold represent increment; rw [Pi.one_apply,mul_one]; rfl
    refine ⟨?_,?_⟩
    · unfold L'; rw [if_pos hi,hg,show G.plog (G.mat (G.lieExp y))=y from hy (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hb'.trans hE))]; exact hb'
    have he := (h y (hb'.trans hR)).trans (mul_le_mul_of_nonneg_left hb' hf.le)
    rw [hg]; change _ / royalty G≤ _ at he
    apply le_trans ((div_le_iff₀ (lt_of_lt_of_le zero_lt_one (royalty_ge G))).mp he); exact (le_abs_self _).trans hx
  have hh := soak hU z
  have hy i : Brush j (C x+K*D x) 1 (fun y=> L' y i) X := by
    unfold L'; split_ifs
    next ht =>
      have hu : Brush j K (D x) (fun y=> G.plog (G.mat (g y i))) X := (hh.atLink i).pine (hJ.sound _ (he i ht).2)
      apply Brush.offer.mpr; refine ⟨hu.smooth,fun k hi=>?_⟩
      rcases k with _|k
      · unfold normJ; rw [norm_iteratedFDeriv_zero]; have hq:= (he i ht).1; unfold L' at hq; rw [if_pos ht] at hq
        exact hq.trans (le_add_of_nonneg_right (mul_nonneg hk ‹0 ≤ D x›))
      apply (hu.order _ hi).trans
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ‹0≤ D x› ((le_abs_self _).trans hz)
        (by omega : 1 ≤ k+1)) hk).trans (by rw [pow_one]; exact le_add_of_nonneg_left hp.1)
    exact (certified (show (0:ℝ)≤1 by norm_num) (0:G.Color)).climb (by rw [norm_zero]; exact ht') le_rfl
  have hv i (hi : i∈univ.filter fun j : Bond c=> separation o j.1 ≤ p) : ∀ᶠ y in 𝓝 X,g y i=increment 1 (L' y) i := by
    have hi := (mem_filter.mp hi).2
    have hz : ‖G.mat (g X i)-1‖ < 2*d := lt_of_le_of_lt (he i hi).2 (by have h:=hJ.pos; linarith)
    have he : ContinuousAt (fun y : E=> ‖G.mat (g y i)-1‖) X := ((hh.atLink i).smooth.continuousAt.sub_const (1:G.Mat)).norm
    filter_upwards [he (gt_mem_nhds hz)] with y hy; unfold increment L'; rw [if_pos hi,hJ.inverse _ hy,Pi.one_apply,mul_one]
  refine ⟨z,L',Brush.fold zero_le_one ht' hy,?_⟩
  filter_upwards [(Finset.eventually_all _).2 hv] with y hz i hi; exact hz i (mem_filter.mpr ⟨mem_univ _, hi⟩)

/-- Comp budget even when the consuming brush tests multiple orders;
    use scaled-positive physical r preserving u when inverse nursery
    huge O(beta^a). -/
lemma scaled {v w p : ℝ} {f : E→F} {x : E} {g : F→Y} (h : Brush j v 1 f x) (he : Brush j w p g (f x)) :
    Brush j (j.factorial*w) (1+v*(1+|p|)) (fun i=>g (f i)) x := by
  have hx : 0 < 1+|p| := add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _)
  let t:= (1+|p|)⁻¹
  have ht : 0<t := by unfold t; positivity
  refine Brush.trail (h:=ht) he (h.climb (le_of_eq ?_) le_rfl) ?_
  · unfold t; field_simp
  rw [mul_comm, ← div_eq_mul_inv]; apply (div_le_one hx).2; exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)

lemma parseRate {G : Gauge} {L : Side} {a b : ℝ} {U V X : ℝ → ℝ} (j : ℕ) (p : Rate G L a X) (h : Rate G L b U)
    (he : b≤0) (hv : Rate G L (-b) V) : Rate G L a
      (fun x => (j.factorial*X x)*(1+(1+U x*(1+|V x|)))^j) := by
  have hf := (Rate.const (G:=G) (L:=L) (1:ℝ))
  have hh : Rate G L 0 (fun x => U x*(1+|V x|)) := by
    convert (h.mul ((hf.weaken (by linarith only [he])).add
      (hv.compare (Eventually.of_forall (fun x => by rw [abs_abs])) : Rate G L (-b) (fun x => |V x|)))) using 1; ring
  simpa only [zero_mul,add_zero] using! ((p.mul_left _).mul (((hf.add (hf.add hh)).pow j)))
end YM.ConnectedActivityE6.Blaze.Frond
