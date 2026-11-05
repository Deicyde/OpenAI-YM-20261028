import YM.UVExtension.Concat
import YM.UVExtension.Reward.Tempo
import YM.UVExtension.Free.Rows

/-! Common bed shape on converging tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset MenuView
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a} {ε : ℝ} {m N :ℕ}
structure Buried (V:Horizon a) : Prop where
    root m : Arrives fun n=> (V.H n m).roots
    breadth m : Arrives fun n=> (V.H n m).metric
lemma reading_line (h:Buried V)(he:Working D V P m):∃ B, Keyline (label D m) B ∧
    ∀ i v,Tendsto (fun n=> reading (label D m) (V.H n m) i v) atTop (𝓝 (reading (label D m) B i v)):=by
  obtain ⟨R,hR⟩:=h.breadth m
  let f:= fun n=>(V.H n m).metric
  let B:= {(V.H m m) with metric:=R}; let i:=a.clock.J m; let s:=P.α i; let E:=pacesE P i; let L:=label D m
  have hu:0<s:=P.alpha_pos _
  have hx:∀ᶠ n in atTop,(f n).strip s E:= (eventually_ge_atTop m).mono fun n hn=> (he.beside n hn).1
  have hp : Free.Received f R s E:= Free.reported hR hx
  have hh i v: Tendsto (fun n=>reading L (V.H n m) i v) atTop (𝓝 (reading L B i v)):=by
    have ht:= Free.acts_limit hp hx hu (L.stageSide i)
    let p:=fun Q=>∑ j, dotProduct (parts G 1 (arm G (L.stageSide i) 1 (v 0)) j) ((Precision.K Q).mulVec (parts G 1 (arm G (L.stageSide i) 1 (v 1)) j))
    exact (show Continuous p by unfold p Precision.K Matrix.mulVec dotProduct; fun_prop).continuousAt.tendsto.comp ht
  refine ⟨B,⟨⟨_,_,hu,hp.bound⟩,?_,fun i x y=>?_⟩, hh⟩
  · have he' : Next.Free.physical (0:Momentum) := by simp [Next.Free.physical]
    apply tendsto_nhds_unique_of_eventuallyEq (Free.read_limit hp hx hu he') tendsto_const_nhds ((eventually_ge_atTop m).mono ?_)
    intro n hn; exact (keysReady he hn).tap
  exact tendsto_nhds_unique_of_eventuallyEq (hh i _) (hh i _) ((eventually_ge_atTop m).mono fun n hn => (keysReady he hn).sym i x y)
lemma starters {x y:ℕ→Cube G}{t:ℕ→ℕ}{b:ℕ→ℝ}{z:ℕ→GainWire a m} {v}(h:Buried V)(hp : Tendsto t atTop atTop)(he : Working D V P m)(hL:LocalRatio Z) (hf:HLimit x v) (hr:∀ i,Tried V D Q Z ε m (t i) (x i) (y i) (b i) (z i)) :
    Arrives (fun i=> daysF D V (x i) (t i) (z i))∧ Arrives (fun i=> daysL D V Z (x i) (t i) (z i)):=by
  have hg i:=(he.paid (t i) (hr i).time.le 0 (Submodule.zero_mem _) (by simp)).bound
  let M:=label D (m+1)
  have ht p:SourceBasis limitView (fun i=>sat D V (t i) (m+1) (x i)) (a.params (m+1)).clip (a.S.side (m+1) p) 5:=by
    refine ⟨insideLine 5 _ (fun i=> (hr i).origin.bound) (fun i=> (hr i).origin.row) ((h.root _).upon t hp),?_,?_⟩
    · change Run _ _ _ (fun i=> M.hat (x i) p) _; exact ⟨fun i=>(M.hat_an (x i) p).contDiffAt,fun i _ v=> travels.mpr ⟨_,hf.bids (M.hat_cost _ _ v)⟩⟩
    refine ⟨fun i=> (turns_analytic _ (hr i).origin.bound.width (hr i).origin.bound.two).contDiffAt,fun i hi v=> travels.mpr ?_⟩; exact ⟨_,hf.bids (M.e_cost _ p v)⟩
  obtain ⟨ha,hb⟩:= queries hL t x y b z hr ht (fun j=> insideLine 4 _ hg (fun n=> (rfl:(sat D V (t n) m 0).row=rowPath (V.H (t n) m))) ((h.root m).upon _ hp))
  exact ⟨Arrives.columns fun i=> Arrives.columns fun j=> Arrives.columns (ha i j),Arrives.columns fun i=> Arrives.columns (hb i)⟩

lemma moving {B t n n'}{x y:ℕ→Cube G}{v}{b:ℕ→ℝ}{Z:ChartRatio G}{z:ℕ→GainWire a m}{α:ℝ} (h:Working D V P m)(ht:Tendsto t atTop atTop)(he:∀ i, Tried V D Q Z ε m (t i) (x i) (y i) (b i) (z i)) (hw : ∀ i w,Tendsto (fun n=> reading (label D m) (V.H n m) i w) atTop (𝓝 (reading (label D m) B i w)))
    (hp:HLimit y v) (hb:Tendsto b atTop (𝓝 α))(hd:Tendsto (fun i=> daysF D V (x i) (t i) (z i)) atTop (𝓝 n))(hv:Tendsto (fun i=> daysL D V Z (x i) (t i) (z i)) atTop (𝓝 n')): Aligns (label D m) B (v,α) n n':=by
  let Y:=label D m
  have hk i: Y.Lodge (y i):= (he i).run.above
  have ha:=(he ·)
  have hα i:=classOrder (he i).run.bubble
  refine ⟨(paints_iff ..).2 ?_,?_, (show Neglect _ _ from ⟨tariff (a:=a) Q m,levity D,?_⟩)⟩
  · exact ⟨hp.normal (Eventually.of_forall (fun i=> (hk i).1)), Y.areas.2 v hp (Eventually.of_forall (fun i=> (show Y.Inked _ from (hk i).2)))⟩
  · funext i j w
    apply tendsto_nhds_unique_of_eventuallyEq (hp.bids (Y.hat_cost _ i w)) (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hd i) j) w)
    exact Eventually.of_forall fun p => congr_fun (congr_fun (congr_fun (hα p) i) j) w
  intro i p q u v' hu hv'
  let w := (![pew p u,pew q v']: Fin 2 → Link G (Y.stageSide i))
  apply le_of_tendsto (((hb.smul ((hw i w).comp ht)).add (hp.bids (Y.e_cost _ i w))).sub (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv i) w)|>.norm)
  exact Eventually.of_forall fun n=> mistOrder h (he n).time (he n).run.bubble i p q u v' hu hv'
end YM.UVExtension.Reward
