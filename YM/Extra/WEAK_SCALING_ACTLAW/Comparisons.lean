import YM.Extra.WEAK_SCALING_ACTLAW.Analysis
import YM.Extra.WEAK_SCALING_ACTLAW.Station
import YM.Work.A04
import YM.Work.A15

/-!
# The finite weak comparisons transported to the same physical table

This passes k-grid data and quantitative reflection-cell inputs on the
actual cutoff variables through the ordered limits. One centered cost
`A^n = o(1/(rescaled k-grid spacing))` pays both the derivative bound off
ties via `Difference.stepTotal` and the undifferentiated bound everywhere,
allowing later interpolation once **exact** derivative rows are fitted.
No rank/derivative convergence is yet used here. Only detector curves in a
fixed strictly coordinate-generic open subset are needed before derivative
row fitting (so don't need shrinking strip estimates). All strict window
parameters must be priced at the finite request.
-/
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Function Filter Metric MeasureTheory Extraction Climb Ward Table
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {n : ℕ} {f : Order}

def readMap (U : Maps S) (r : ℕ → ℝ) (v : Fin n → (Free C).Tag) (k : ℕ) (x : Points n) :=
  disc (routed U k ∘ v) (r k • x)

lemma readMap_smooth (H : S.Hierarchy) {U : Maps S} {r : ℕ → ℝ} {v : Fin n → (Free C).Tag} {k : ℕ}
    (h : 0 < r k) {x : Points n} (hx : x ∈ conf n) : ContDiffAt ℝ ∞ (readMap U r v k) x :=
  (cont_disc H _ (Work.A04.scale_conf _ h hx)).comp x (show ContDiffAt ℝ ∞ (fun x : Points n => r k • x) x by fun_prop)

lemma points_approach (h : f.PointLimits C S) {u : ℕ → Fin n → Lattice.Cover} {x : Points n} (hx : x ∈ generic n)
    (he : Tendsto (fun i => tag (C.S.a i) (u i)) atTop (𝓝 x)) (v : Fin n → C.book.Token) :
    Tendsto (fun j : ℕ × ℕ => lifted C j.1 j.2 v (u j.1)) f.fuse (𝓝 (S.read x v)) := by
  obtain ⟨P,hp,hv⟩ := h
  apply Order.along (L := fun i j => lifted C i j v (u i)) (p := fun p => x∈Cyclic C.S p n)
  refine ⟨?_,fun p => (P p).read x v,fun p h => f.evaluated C hp p n v x h (u ∘ f.mesh) (he.comp f.mesh.cofinal),?_⟩
  · filter_upwards [f.per.cofinal.eventually (room C.S isCompact_singleton)] with p hp
    exact (no_wrap_tie C.S (hp (mem_singleton x))).mpr hx
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [hv n {x} isCompact_singleton (singleton_subset_iff.mpr hx) v ε hε] with i hi
  rw [dist_eq_norm]; exact hi _ (mem_singleton x)

section gaps
variable {r Q : ℝ} {S' : Schedule}

lemma cofin_fst (f : Order) : Tendsto (fun j : ℕ × ℕ => j.1) f.fuse atTop := by
  intro s h
  change f.late (fun N _ => N ∈ s); exact Eventually.of_forall fun _ => f.mesh.cofinal h
lemma cofin_snd (f : Order) : Tendsto (fun j : ℕ × ℕ => j.2) f.fuse atTop := by
  intro s h
  change f.late (fun _ p => p ∈ s)
  exact (f.per.cofinal.eventually (p:=(· ∈ s)) h).mono fun _ h => Eventually.of_forall fun _ => h

lemma off_late (S' : Schedule) (f : Order) {u : ℕ → Points n} {x : Points n} (hr : 0 < r)
    (he : Tendsto u atTop (𝓝 (r • x))) {a : Axis} {s t : Fin n} (hx : Q⁻¹ < |x t a-x s a|) :
    ∀ᶠ j : ℕ × ℕ in f.fuse, Gaps.off S' j.2 (Gaps.distances (u j.1) s t a) (r/Q) := by
  have hh : r/Q < |Gaps.distances (r • x) s t a| := by
    change r/Q < |r*x t a-r*x s a|
    rw [← mul_sub, abs_mul,abs_of_pos hr,div_eq_mul_inv]; gcongr
  let K := closedBall (r • x) 1
  have hi := he.eventually ((Gaps.ct s t a).abs.continuousAt.eventually (lt_mem_nhds hh))
  filter_upwards [(cofin_fst f).eventually hi,(cofin_snd f).eventually (Gaps.expand_equivalent S' (K:=K) (isCompact_closedBall _ _)),
    (cofin_fst f).eventually (he.eventually (closedBall_mem_nhds _ one_pos))] with j hj hp hu l
  exact hj.le.trans (hp (u j.1) hu s t a l)

lemma approx_step (S' : Schedule) {t : ℝ} (h : 0 < t) : Tendsto (fun N => S'.a N * (⌊t/S'.a N⌋₊ : ℝ)) atTop (𝓝 t) := by
  refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) ?_ S'.shrinks)
  intro i
  have ht := S'.a_pos i
  have hp := Nat.floor_le (by positivity : 0 ≤ t/S'.a i)
  have hw := Nat.lt_floor_add_one (t/S'.a i)
  rw [div_lt_iff₀ ht] at hw
  rw [Real.dist_eq,abs_le]
  rw [le_div_iff₀ ht] at hp
  constructor <;> linarith

lemma tag_advance (q : ℝ) (u : Fin n → Lattice.Cover) (i : Fin n) (a : Axis) (l : ℕ) :
    tag q (Difference.advance u i a l) = tag q u + (q*l) • Points.direction i a := by
  ext1 j; ext1 b
  by_cases h : j=i
  · subst j; by_cases he : b=a <;> simp [he,Difference.advance,tag,Points.direction]; ring
  simp [Difference.advance,tag,h,Points.direction]
end gaps

variable {b : Stations C}
namespace Retained
variable (Z : Retained b f)

lemma approach (k : ℕ) (h : f.PointLimits C S) (hS : S.Hierarchy)
    {v : Fin n → (Free C).Tag} {x : Points n} (hx : x∈generic n) {u : ℕ → Fin n → Lattice.Cover}
    (he : Tendsto (fun i => tag (C.S.a i) (u i)) atTop (𝓝 (b.r k • x))) :
    Tendsto (fun j : ℕ × ℕ => lifted C j.1 j.2 (b.name k j.1 j.2 ∘ v) (u j.1)) f.fuse
      (𝓝 (readMap (Z.maps S) b.r v k x)) := by
  have hp := smul_generic (b.positive k) hx
  let z : Fin n → C.book.Token := fun i => ⟨(v i).1,Z.a k (v i).1 (v i).2⟩
  have hh : readMap (Z.maps S) b.r v k x = S.read _ z :=
    S.at_project S hS.laws.toSymmetric (fun _ => le_rfl) (generic_conf _ hp) z
  rw [hh]
  let d : Caps n := fun i => (v i).1
  have hc (i : Fin n) : Tendsto (fun j : ℕ × ℕ => b.coef k (v i).1 j.1 j.2 (v i).2)
      f.fuse (𝓝 (Z.a k _ (v i).2)) := Dash.arcing (Z.tends k _) tendsto_const_nhds
  have hh := multi_fitted (V:=fun i => C.book.Ref (d i)) (l:=f.fuse) (x:=fun i => Z.a k (d i) (v i).2) (u:=fun j i => b.coef k (v i).1 j.1 j.2 (v i).2)
    (fun j : ℕ × ℕ => C.ensemble (N:=j.1) (p:=j.2) d (Lattice.wrap (C.side j.1 j.2) ∘ u j.1)) (S.value d (b.r k • x))
    (fun w => points_approach h hp he fun i => ⟨d i,w i⟩) hc
  exact hh

lemma grid_approach (k : ℕ) (h : f.PointLimits C S) (hS : S.Hierarchy)
    (v : Fin n → (Free C).Tag) (u : Fin n → Lattice.Cover) (hx : b.rescaled k u∈generic n) :
    Tendsto (fun j : ℕ × ℕ => b.cost k j.1 j.2 v u) f.fuse (𝓝 (readMap (Z.maps S) b.r v k (b.rescaled k u))) := by
  have he : b.r k • b.rescaled k u = tag (C.S.a (b.grid k)) u := b.physical k u
  have hp := he ▸ smul_generic (b.positive k) hx
  let z : Fin n → C.book.Token := fun i => ⟨(v i).1,Z.a k (v i).1 (v i).2⟩
  rw [readMap,he,show disc (routed (Z.maps S) k ∘ v) _ = S.read _ z from
    S.at_project S hS.laws.toSymmetric (fun _ => le_rfl) (generic_conf _ hp) z]
  let d : Caps n := fun i => (v i).1
  have hc (i : Fin n) : Tendsto (fun j : ℕ × ℕ => b.coef k (v i).1 j.1 j.2 (v i).2)
      f.fuse (𝓝 (Z.a k _ (v i).2)) := Dash.arcing (Z.tends k _) tendsto_const_nhds
  have hh := multi_fitted (V:=fun i => C.book.Ref (d i)) (l:=f.fuse) (x:=fun i => Z.a k (d i) (v i).2) (u:=fun j i => b.coef k (v i).1 j.1 j.2 (v i).2)
    (fun j => C.ensemble (N:=j.1) (p:=j.2) d (Cells.location C.S (b.grid k) j.1 j.2 ∘ u)) (S.value d (tag (C.S.a (b.grid k)) u))
    (fun w => Order.inPatch h (b.grid k) u hp fun i => ⟨d i,w i⟩) hc
  exact hh

lemma amount (k m j : ℕ) (Q : ℝ) (hQ : 0 < Q) (v : Fin n → (Free C).Tag) (s : Spec.Seed C f S)
    (hm : m≤j) (hg : C.S.a m < b.r k/Q) (hroom : (n:ℝ)*(2*(3*C.S.a j)) < C.S.a m) (A : ℝ)
    (h : f.late fun N p => ∀ i z, centeredBudget C (Extraction.Spin.token C.book (b.name k N p (v i)) z) A j N p)
    {x : Points n} (hx : x ∈ apart Q n) : ‖readMap (Z.maps S) b.r v k x‖ ≤ A^n := by
  let F := readMap (Z.maps S) b.r v k
  have H y (hy : y ∈ apart Q n) (hw : y ∈ generic n) : ‖F y‖ ≤ A^n := by
    let u := fun N => address (C.S.a N) (b.r k • y)
    let P (w : ℕ × ℕ) := b.name k w.1 w.2 ∘ v
    have ha := chosen (S:=C.S) (b.r k • y)
    have hr : 0 < b.r k := b.positive k
    apply le_of_tendsto (Z.approach k s.generic s.kernel hw ha (v:=v)).norm
    have hf (i t : Fin n) : ∀ᶠ w : ℕ × ℕ in f.fuse, i≠t → ∃ a : Axis,
        Gaps.off C.S w.2 (Gaps.distances (tag (C.S.a w.1) (u w.1)) i t a) (b.r k/Q) := by
      by_cases he : i=t
      · subst i; simp
      obtain ⟨a,h⟩ := hy.2 i t he
      exact (off_late C.S f hr ha h).mono fun w hw _ => ⟨a,hw⟩
    have H (i : Fin n) := (cofin_fst f).eventually (Around.fit (f:=Order.full) (C:=C)
      (⟨(v i).1,0⟩ : C.book.Token) j)
    have he := (cofin_fst f).eventually (eventually_ge_atTop j)
    have hb : ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ i z, centeredBudget C (Extraction.Spin.token C.book (P w i) z) A j w.1 w.2 := h
    filter_upwards [eventually_all.mpr fun i => eventually_all.mpr (hf i),eventually_all.mpr H,he,hb] with w hw hF hJ hp
    exact Around.fits_budget s.cutoff _ {tag (C.S.a w.1) (u w.1)} (b.r k/Q)
      (fun _ hu => (mem_singleton_iff.mp hu).symm ▸ hw) A hg hm hroom ⟨hJ,fun i z => ⟨hp i z,by
        rw [Around.Fit,Extraction.Spin.stay]; exact hF i w.2⟩⟩ _ rfl
  have ht : ContinuousOn (fun z => ‖F z‖) (apart Q n) := fun y hy =>
    ((readMap_smooth s.kernel (b.positive k) (apart_conf hQ hy)).continuousAt.norm.continuousWithinAt)
  have hop := apart_open Q n
  suffices h : EqOn (fun z => min (A^n) ‖F z‖) (fun z => ‖F z‖) (apart Q n) by
    exact (h hx).symm.trans_le (min_le_left ..)
  apply Measure.eqOn_open_of_ae_eq (μ:=volume) _ hop (continuousOn_const.inf ht) ht
  exact ((ae_restrict_iff' hop.measurableSet).mpr ((almostGeneric n).mono fun y hy hw => min_eq_right (H y hw hy)))

lemma grad_bound (k j : ℕ) (Q : ℝ) (hQ : 0 < Q) (v : Fin n → (Free C).Tag) (s : Spec.Seed C f S)
    (hj : C.S.a j < b.r k/(4*Q)) (A : ℝ) (hA : 0 ≤ A)
    (h : f.late fun N p => ∀ i z, centeredBudget C (Extraction.Spin.token C.book (b.name k N p (v i)) z) A j N p)
    {x : Points n} (hx : x ∈ clearance Q n) (l : Fin n) (a : Axis) :
    ‖fderiv ℝ (readMap (Z.maps S) b.r v k) x (Points.direction l a)‖ ≤ A^n*(4*Q) := by
  cases n with
  | zero => exact Fin.elim0 l
  | succ n =>
  let ρ := b.r k
  have hρ : 0 < ρ := b.positive k
  have h0 : 0 < ρ/(4*Q) := by positivity
  have h1 : 0 < (4*Q)⁻¹ := by positivity
  let F := readMap (Z.maps S) b.r v k
  let d := Points.direction l a
  let u := fun N => address (C.S.a N) (ρ • x)
  have hu := chosen (S:=C.S) (ρ • x)
  have hx' : x ∈ generic _ := clearance_generic hQ hx
  have main (t : ℝ) (ht : 0 < t) (ht' : t < (4*Q)⁻¹) (hy : x + t • d ∈ generic _) :
      ‖F (x+t • d) - F x‖ ≤ A^(n+1)/(ρ/(4*Q)) * (ρ*t) := by
    let L := fun N => ⌊(ρ*t)/C.S.a N⌋₊
    have he : Tendsto (fun N => C.S.a N * (L N:ℝ)) atTop (𝓝 (ρ*t)) := approx_step _ (by positivity)
    let W := fun N => Difference.advance (u N) l a (L N)
    have hV : Tendsto (fun N => tag (C.S.a N) (W N)) atTop (𝓝 (ρ • (x + t • d))) := by
      dsimp only [W]
      simp_rw [tag_advance, smul_add,smul_smul]; exact hu.add (he.smul tendsto_const_nhds)
    rw [← dist_eq_norm]
    apply le_of_tendsto_of_tendsto ((Z.approach k s.generic s.kernel hy hV).dist (Z.approach k s.generic s.kernel hx' hu))
      ((tendsto_const_nhds (f:=f.fuse)).mul (he.comp (cofin_fst f)))
    have hh := eventually_all.mpr fun i => eventually_all.mpr fun p => (eventually_all.mpr fun (hi : i≠p) =>
      eventually_all.mpr fun z => off_late C.S f hρ hu (hx.2 i p hi z))
    let P (w : ℕ × ℕ) := b.name k w.1 w.2 ∘ v
    have hb : ∀ᶠ w in f.fuse, ∀ i z, centeredBudget C (Extraction.Spin.token C.book (P w i) z) A j w.1 w.2 := h
    filter_upwards [hh,hb,(he.comp (cofin_fst f)).eventually (gt_mem_nhds (a := ρ/(4*Q))
      (by rw [div_eq_mul_inv]; exact mul_lt_mul_of_pos_left ht' hρ)),(cofin_fst f).eventually (eventually_ge_atTop j)] with w hw hz hL hJ
    have H := Difference.stepTotal s.cutoff (P w) hA h0 {tag (C.S.a w.1) (u w.1)} _ _ _ hJ (by
      rintro i z (rfl|⟨c,rfl⟩)
      · simpa using hz i (1,false)
      rw [← Register.token_adjoint, Extraction.Spin.swapC]
      exact hz i (Signed.mirror c,true)) (by
      rw [show 4*(ρ/(4*Q)) = ρ/Q by ring]; intro y (hy : y ∈ {_}); rw [mem_singleton_iff.mp hy]; exact hw)
      hj l a (L w.1) (u w.1) rfl (by rw [Difference.extent _ _ _ _ _ (C.S.a_pos _)]; exact hL.le)
    rw [Difference.extent _ _ _ _ _ (C.S.a_pos _)] at H
    exact H
  have hf : HasDerivAt (fun t : ℝ => F (x+t • d)) (fderiv ℝ F x d) 0 := by
    have hi := (readMap_smooth s.kernel (U:=Z.maps S) (v:=v) hρ (generic_conf _ hx')).differentiableAt (by simp)
    have hp : HasDerivAt (fun t : ℝ => x+t • d) d 0 := by
      exact (show HasDerivAt ((fun _ : ℝ => x) + fun t : ℝ => t • d) d 0 by simpa only [one_smul,zero_add] using ((hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id' (0:ℝ)).smul_const d)))
    exact (show HasFDerivAt F (fderiv ℝ F x) (x + (0:ℝ) • d) by simpa [F] using hi.hasFDerivAt).comp_hasDerivAt (f:=fun t : ℝ => x+t • d) (0:ℝ) hp
  apply le_of_tendsto (x := 𝓝[>] (0:ℝ)) (hf.tendsto_slope_zero.norm.mono_left (nhdsWithin_mono _ (by simp)))
  simp only [zero_add,zero_smul,add_zero]
  have hc : Tendsto (fun t : ℝ => x+t • d) (𝓝[>] 0) (𝓝 x) := by
    simpa using ((show Continuous (fun t : ℝ => x+t • d) by fun_prop).continuousWithinAt (s:=Ioi 0) (x:=0)).tendsto
  filter_upwards [self_mem_nhdsWithin, hc.eventually ((genericOpen _).mem_nhds hx'),
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds h1)] with t ht hy ht'
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht), ← div_eq_inv_mul,div_le_iff₀ ht]
  apply (main _ ht ht' hy).trans_eq
  field_simp

variable {M D : ℕ} {Q : ℝ} {s : Spec.Seed C f S} {v : Fin n → (Free C).Tag}

lemma on_grid (s : Spec.Seed C f S) (h : AlignedCosts b f M D Q) (hQ : 0 < Q) (hn : n ≤ M) (hv : capped D v) :
    Sampled (apart Q n) b.delta (readMap (Z.maps S) b.r v) (disc v) := by
  have hw := h _ hn v hv
  intro a ha x hx u hu he
  let z (i : ℕ) := b.rescaled (a i) (u i)
  have hc : Tendsto (fun i => disc v (z i)) atTop (𝓝 (disc v x)) :=
    ((((Free C).class_smooth (Free C) (Maxwell.table_smooth _) v).continuousOn.continuousAt
      ((conf_open _).mem_nhds (apart_conf hQ hx))).tendsto.comp hu)
  refine hc.congr_dist (Metric.tendsto_nhds.mpr (fun ε hε => ?_))
  filter_upwards [ha.eventually (hw _ (half_pos hε)), hu.eventually ((apart_open Q n).mem_nhds hx),he] with i hi hy hU
  rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg,dist_comm]
  apply lt_of_le_of_lt (le_of_tendsto ((Z.grid_approach (a i) s.generic s.kernel v (u i) hU).dist tendsto_const_nhds) ?_)
    (half_lt_self hε)
  simpa only [Order.fused,dist_eq_norm,z] using hi (u i) hy hU

lemma growth (s : Spec.Seed C f S) (h : CenterCosts b f M D Q) (hQ : 0 < Q) (hn : n ≤ M) (hv : capped D v) :
    Follows (apart Q n) (fun k x => b.delta k • readMap (Z.maps S) b.r v k x) 0 := by
  obtain ⟨A,hA,hlim,H⟩ := h n hn v hv
  intro a ha x hx z hz
  change Tendsto _ _ (𝓝 0); rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ (hlim.comp ha)
  filter_upwards [hz.eventually ((apart_open _ _).mem_nhds hx), ha.eventually H] with i hi H
  obtain ⟨m,j,hj,hg,hroom,-,hc⟩ := H
  have he := Z.amount (a i) m j Q hQ v s hj hg hroom _ hc hi
  have hp := b.positive (a i)
  have hs := C.S.a_pos (b.grid (a i))
  simpa only [comp_apply,norm_smul,Real.norm_eq_abs, abs_of_pos (by positivity : 0 < b.delta (a i)),mul_comm] using!
    mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ b.delta (a i))

lemma on_clearance (s : Spec.Seed C f S) (h : CenterCosts b f M D Q) (h' : AlignedCosts b f M D Q)
    (hQ : 0 < Q) (hn : n ≤ M) (hv : capped D v) : Follows (clearance Q n) (readMap (Z.maps S) b.r v) (disc v) := by
  obtain ⟨A,hA,hlim,H⟩ := h n hn v hv
  apply interpolate (clearance_open Q n) (h:=b.delta) (fun k => div_pos (C.S.a_pos _) (b.positive _)) b.fine
  · exact fun k x hx => (readMap_smooth s.kernel (b.positive k) (generic_conf _ (clearance_generic hQ hx))).differentiableAt (by simp)
  · exact fun a ha x hx => Z.on_grid s h' hQ hn hv a ha x (clearance_apart hx)
  intro ⟨l,c⟩ a ha x hx z hz
  change Tendsto _ _ (𝓝 0); rw [tendsto_zero_iff_norm_tendsto_zero]
  have hi : Tendsto (fun i => (A (a i)^n*b.delta (a i))*(4*Q)) atTop (𝓝 0) := by
    simpa [comp_def] using (hlim.comp ha).mul_const (4*Q)
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hi
  filter_upwards [hz.eventually ((clearance_open _ _).mem_nhds hx),ha.eventually H] with i h H
  obtain ⟨m,j,-,-,-,hj,hc⟩ := H
  have he := Z.grad_bound (a i) j Q hQ v s hj _ (hA _) hc h l c
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (C.S.a_pos _) (b.positive _))]
  convert mul_le_mul_of_nonneg_left he (show 0 ≤ b.delta (a i) from (div_pos (C.S.a_pos _) (b.positive _)).le) using 1
  · rfl
  ring
end Retained
end YM.Extra.WeakScaling
