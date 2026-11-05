import YM.UVExtension.Reward.Dais
import YM.UVExtension.Reward.Heal

/-! Day-level new licensed step and interface for iteration. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a}
structure Courtesy (V:Horizon a)(D : Knobs a) (Q:PostCost L) (Z:ChartRatio G)(b:ℝ) (N m:ℕ)(R: PathData G) (x:Cube G) (α:ℝ)(ρ:GainWire a m):Prop where
    above : (label D m).Lodge x
    toll : ‖x‖ ≤ b
    bubble : Bubble V Q Z N m R (sat D V N m x) α ρ

section day
structure Charges (G : Gauge) (P : MapPrices) (K : KernelChoices) (Z s A τ a d γ : ℕ →ℝ) (u : ℕ→ℕ)(pace : ℕ→ℝ) (F W : ℕ → Side → ℝ) : Prop where
    moon (j i : ℕ) (h : j=i ∨ j=i+1) : Reward.Choices G K j (P.η j) (P.α j) (pacesE P j) (Z j) (P.α i) (pacesE P i) (Z i) (a j) (τ j) (A i) (d j) (s i) (γ j) (u j) (pace i) (F j) (W j)

variable {pace Zc A σ d g : ℕ → ℝ} {u : ℕ → ℕ} {F T : ℕ → Side → ℝ} {m N : ℕ}
variable (h : Paid w a) (hΘ : BudgetGap s L P Q.η) (hS : ∀ i, GateVolume i ≤ W.shells i) (ht : ∀ i (n : Side),W.shells i ≤ n.val → F i (L.L i)*Real.exp (-(g i)*n.val) ≤ Q.Γ i*Real.exp (-Q.c i*n.val))
variable (hi : (fun i=> (s.profile i).clip.direct) ≤ Zc) (hw : (fun i=> (s.profile i).width) ≤ σ) (hA : A ≤ fun i => (s.profile i).paths)
    (hq : d ≤ fun i => (s.profile i).drift) (hp : u≤ s.floorL) (he : LocalRatio Z)
    (hb : Craft.Rack a P K) (hk : Bid.Retained V K) (hJ : Charges G P s.kernel Zc σ A (fun i=> (s.profile i).width) (fun i=> (s.profile i).paths) d g u pace F T)
include h hΘ hS ht hi hw hA hq hp he hb hk hJ
lemma bought {aB Er : ℝ} (hEps : aB ≤ 1) (hx : Working D V P m) (hrates : D.widths m≤ σ (a.clock.J m)) (hCost : T (a.clock.J (m+1)) (L.L (a.clock.J (m+1)))≤ Er) (hEcost : pace (a.clock.J m)*a.clock.loopCap (m+1) ≤ Er) (hE : Er≤ a.clock.loopCap m)
    (hXcost : Er / D.loops m+A (a.clock.J m)/D.E m+A (a.clock.J m)/D.E m≤aB) (H : 1 ≤ a.clock.loopCap (m+1)) {R : PathData G} (hy : R.Bounds (a.params (m+1)).clip (a.params (m+1)).width (a.params (m+1)).paths (a.clock.loopCap (m+1))) (hu' : Attached (V.H N (m+1)) R) (hm : m < N) :
    ∃ x α ρ,Courtesy V D Q Z aB N m R x α ρ := by
  let i:= a.clock.J m; let j:= a.clock.J (m+1); let U := a.params (m+1); let T' := a.params m
  let C := a.clock; let M:= (a.clock.op m 0).patch
  let p:= V.towers N m; let b := V.H N m; let z := V.H N (m+1)
  have hj : M.L=L.L j := (a.fits.sameFactor m).symm.trans (congr_fun h.lengths _)
  have h' : j=i ∨ j=i+1 := by
    have h : i≤j := a.fits.mono (Nat.le_succ m); have hi : j≤ i+1 := a.fits.stepSlow m; omega
  have hu : U=s.profile j := by unfold U Levels.params Calendar.params; rw [h.stage]
  have hT : T'=s.profile i := by unfold T' Levels.params Calendar.params; rw [h.stage]
  have hg v := larger h hS m v
  have hF := hull_fact hb hk hm; have hT' := hull_fact hb hk (le_of_lt hm)
  obtain ⟨h2,Ld⟩ := tack_columns hb hk hm
  let f := fun t => a.S.side m t; let c := fun t=> a.S.side (m+1) t
  have hv t (F : Forest (a.clock.op m t).ratio) := hΘ.ask j (a.clock.op m t) h.kernel hj rfl (hg t) F z b U.clip T'.clip R U.width U.paths _ _ _ _ p (Ld t) (hF.2.2.1 _) hy hu' (hF.2.2.2 t) (hT'.2.2.1 _)
  have hK t F := (hv t F).1
  choose ρ hρ using fun i F=> (hv i F).2
  let fF (t : ℕ) : Forest (a.clock.op m t).ratio := Classical.choice (Tree.select _ M.odd_side)
  let ξ : Armada f c M C.kernel := ⟨fun t=> (a.clock.op m t).sizes⟩
  let a' := fun i=> ρ i (fF i)
  have hZ : Reward.Choices G C.kernel j (P.η j) (P.α j) (pacesE P j) (Zc j) (P.α i) (pacesE P i) (Zc i) U.paths U.width (A i) (d j) (σ i) (g j) (u j) (pace i) (F j) (T j) := by rw [hu,show C.kernel=s.kernel from h.kernel]; exact hJ.moon j i h'
  have hΦ : Scud ξ G U.clip T'.clip R fF a' (P.α j) U.width (pacesE P j) U.paths (pacesE P j) (P.η j) (a.clock.loopCap (m+1)) (P.α i) (pacesE P i) (P.η i) z b p (Q.η j) :=
      ⟨hg, hF,hT',hu',hy,h2,Ld,fun t=> hK t _,fun i=> (hρ i _).1,fun i=>(hρ i _).2.1, fun i=>(hρ i _).2.2⟩
  obtain ⟨Y,α,h1,h3,h5,hout,hX,hY,hP,hEc,hG,H'⟩ := hZ f c M ξ U.clip T'.clip R fF a' z b p (a.clock.loopCap (m+1)) (P.η i) (Q.η j) Z rfl (by rw [hj]; exact (hp j).trans (L.large j).need) (bound_climb G a m) (hu ▸ hi j) (hT ▸ hi i) hΦ H (Q.price _) he
  have hc0:T j M.L≤Er:= by rw [hj]; exact hCost
  have hSat0:= hP (D.widths m) (A i) Er (D.health _).1 hrates le_rfl hc0 hEcost
  obtain ⟨x,htx,hax,hTx⟩:= (label D m).store b h1 h3 h5 Y T'.clip hSat0 hout (le_refl (D.widths m)) hXcost
  obtain ⟨x',hy',hrat,hmin⟩:= (label D m).sealed x hax
  have hSat : Y.Bounds T'.clip T'.width T'.paths (a.clock.loopCap m) := hP _ _ _ (a.params _).width_pos (hT ▸ hw i) (hT ▸ hA i) (le_trans hc0 hE) (le_trans hEcost hE)
  refine ⟨x',α,ρ,hrat,hy'.trans hTx,realign ?_ hmin (hx.paid _ hm.le _ hrat.2 (hy'.trans (hTx.trans hEps)))⟩
  rw [show sat D V N m x=Y from htx]
  refine ⟨hEc.trans (show d j ≤ U.drift from hu ▸ hq _), ⟨hX,hY,hSat⟩,fun t v => ⟨hK t v,(hρ t v).1, (hρ t v).2.1,?_,?_⟩⟩
  · exact Bid.one_for_all (a.clock.op m t) Work.F05.answer (hg t) (fF t) U.clip T'.clip R Y U.width U.paths _ _ (Q.price _) hy Z he (ρ t) (fun F=> (hρ t F).1) (hK t) (hG t) v
  have hn : W.shells j ≤ (f t).val := (Nat.le_mul_of_pos_right _ (by positivity)).trans (h.volume m t)
  have hr := transfer_bound (hg t) hy he (Q.price j) (hρ t v).1 (hρ t (fF t)).1 (hK t v) (hK t _) (H' (F j M.L) (g j) le_rfl le_rfl t)
  apply higher_bill hr
  simp only [mul_one]; rw [hj]; exact ht _ _ hn

end day
end YM.UVExtension.Reward
