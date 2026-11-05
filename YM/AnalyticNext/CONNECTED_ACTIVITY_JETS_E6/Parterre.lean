import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Engrave
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tint

/-!
# Local transported tangent, primitive smooth global log ψ

Probe all masks under θ.E. Pull locally by accepted patch operations. Only
paint stencil visible; allows power growth post-L. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows  Coat SliceRows.DataKernel   
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k j : ℕ} {U : E → Config G f} {V Q : E → Config G c} {x : E} {v z a w b d e : ℝ}
open Brush

namespace Frond

lemma hard_turn (F : Rod c f) (h : Room P S T s) {u : E→ Directions G f} (he : 0≤e) (hd : 0≤d)
    (hx : ∀ i:Bond f, separation (focus S F) (atEdge S i)≤radiusB s→ Brush k e d (fun j=> u j i) x)
    (hm : Mode V x k v) (hv : SliceRows.Bounded T P.top.width z) (hp : 0≤z) :
    let f:=4*radiusB s*(v*royalty G)
    Brush k (z*(royalty G*(e*royalty G))) (f+d+f) (fun i=> straightened T (till s) (V i) (u i) F) x := by
  intro f'
  let o:=focus S F; let R:=radiusB s; let g j i:= if separation o (atEdge S i) ≤ R then spinRow S (carrier o (V j)) (u j) i else 0
  have hf (v : E) : straightened T (till s) (V v) (u v) F=barField T (till s) (g v) F := by
    refine tangent_local T (SectorMeasure.funds_branch h.accepted) _ _ _ F ?_
    intro i hi
    unfold g; rw [if_pos (by have hx:=h.sight; change separation o (atEdge S i)≤R; change separation o (atEdge S i)≤_ at hi; unfold R; omega)]
  obtain ⟨_,_,hr,-⟩ := h.accepted.feeds
  let f : Directions G _ →ₗ[ℝ] G.Color :=
    { toFun x:= barField T (till s) x F,
      map_add' x y := bar_add T hr _ x y _, map_smul' x y := bar_smul T hr _ y x _ }
  have hi : 0≤ v := hm.pos; have hc : 1≤ royalty G:= royalty_ge G
  have hh : Brush k (royalty G*(e*royalty G)) (f'+d+f') g x := by
    have hX : 0 ≤ f' := by unfold f'; positivity
    have he : 0 ≤ royalty G*(e*royalty G) := by positivity
    refine Brush.fold (by positivity) he fun i=> ?_
    change Brush _ _ _ (fun j=>g j i) _; unfold g; split_ifs
    next hp =>
      let V' j:= carrier o (V j) (atEdge S i)
      have hk : Brush k (royalty G) f' (G.mat ∘ V') x := by
        apply (tour (U:=V) (carriage o (atEdge S i)) o hm.pos hm.atLink).climb le_rfl
        unfold f'; apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (mileage ..).trans (Nat.mul_le_mul_left 4 hp)
      exact decorate hk (hx i hp)
    exact (certified (show 0≤ f'+d+f' by positivity) (0:G.Color)).climb (by rwa [norm_zero]) le_rfl
  simp_rw [hf]; exact hh.report f.toContinuousLinearMap (ContinuousLinearMap.opNorm_le_bound _ hp (fun _=> hv.short ..))

structure Suitable (G : Gauge) (k : ℕ) (J d r : ℝ) : Prop where
  pos : 0<d
  value : 0<J
  sound u : ‖G.mat u-1‖ ≤ d → Brush k J 1 G.plog (G.mat u)
  price u : ‖G.mat u-1‖ ≤ d → ‖G.plog (G.mat u)‖ ≤ r
  inverse u : ‖G.mat u-1‖ < 2*d → G.lieExp (G.plog (G.mat u))=u

lemma cleanly (G : Gauge) (k : ℕ) (r : ℝ) (hr : 0<r) : ∃ J d : ℝ, Suitable G k J d r := by
  obtain ⟨J,hJ,h⟩:= neighborhood _ (G.plog_diff.of_le (show (↑k:WithTop ℕ∞)≤⊤ from le_top))
  obtain ⟨e,he,hp⟩:= Metric.nhds_basis_closedBall.mem_iff.mp h
  have hy : ∀ᶠ u : G.El in 𝓝 1, ‖G.plog (G.mat u)‖ < r := by
    have ht : ‖G.plog (G.mat 1)‖<r := by simpa using hr
    exact (G.plog_diff.continuousAt.comp (g:=G.plog) (f:=G.mat) (x:=1) G.continuous_mat.continuousAt).norm (gt_mem_nhds ht)
  obtain ⟨t,ht,hz⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (hy.and G.plog_right)
  let d:= min e (t/3)
  have hd : 0<d := lt_min he (by positivity)
  have hv u (hp : ‖G.mat u-1‖≤2*d) : u∈Metric.closedBall (1:G.El) t := by
    apply Metric.mem_closedBall.mpr; change dist (G.mat u) (1:G.Mat) ≤ _; rw [dist_eq_norm]
    have hh : d≤t/3 := min_le_right ..; linarith
  exact ⟨J,d,hd,hJ,fun u h=> hp (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact h.trans (min_le_left ..))),
    fun _ h=> (show _<r from (hz (hv _ (h.trans (by linarith)))).1).le, fun _ h=> (hz (hv _ h.le)).2⟩

lemma ep {L J r : ℝ} (h : Mode U x k v) (he : Suitable G k J L r) (hp : ∀ i, ‖G.mat (U x i)-1‖ ≤ L) :
    let p (s : E) := toLog (G:=G) fun i:Bond f=> G.plog (G.mat (U s i))
    Brush k (k.factorial*J) ((1+royalty G)*v) p x ∧ ‖p x‖≤r ∧
      U =ᶠ[𝓝 x] (fun i=> represent (p i)) := by
  intro p
  let T i (x:E):= G.plog (G.mat (U x i))
  have hz i : Brush k (k.factorial*J) ((1+royalty G)*v) (T i) x := (h.atLink i).pine (he.sound _ (hp _))
  let fD : Bond f := (0,0)
  have hr : 0 ≤ r := (norm_nonneg _).trans (he.price _ (hp fD))
  refine ⟨Brush.fold (hz fD).pos (hz fD).nonneg (fun i=> hz _), (pi_norm_le_iff_of_nonneg hr).2 (fun i=> he.price _ (hp _)),?_⟩
  have hx i : ∀ᶠ t in 𝓝 x, G.lieExp (T i t)=U t i := by
    have hh : ∀ᶠ t in 𝓝 x,‖G.mat (U t i)-1‖ < 2*L := (h.atLink i).smooth.continuousAt.sub_const (1:G.Mat)|>.norm|>.eventually
      (gt_mem_nhds (show ‖G.mat (U x i)-_‖ < 2*L from lt_of_le_of_lt (hp i) (by have hp := he.pos; linarith)))
    filter_upwards [hh] with x hx; exact he.inverse _ hx
  filter_upwards [eventually_all.mpr hx] with i hi; ext1 j
  simp only [represent,increment,p, Pi.one_apply,mul_one]; rw [SliceRows.collects]; exact (hi j).symm
end Frond
end YM.ConnectedActivityE6.Blaze
