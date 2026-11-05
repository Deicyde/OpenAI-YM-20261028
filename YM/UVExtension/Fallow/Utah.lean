import YM.UVExtension.Fallow.Paste
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D) (hF:Fridge C u ζ) {d N p:ℕ}
open Extra.Histories Motion
include H h B hF hG
-- first match maps in TOP currency
lemma socket (F:Stem C p)(hp:Pasted F)(hx:garment F d)(hC:∀ᶠ i in atTop, Continuous (F i)): ∃ x:ℕ→ C.label d,Bleak p x∧ Faded C (F - thor x p):=by
   obtain ⟨E,hE,hp'⟩:= persistsR H hG hF.full (roof_of_tabs B) hF.candle (hF.path Order.full) (hF.smoke d _) (fun i hi=> (h.grows d i hi).le) hx hC
   let V i:=(C.factory d i p); let Y:=C.labels.level d
   let f(i)(x:C.label d):= ‖(V i).terminal.symm x‖ ≤ 2*E i ∧ ∀ m k:ℕ,C.ref d ≤ k→k < i →Stock.Tabs.opens C.path.levels 1 m k →∀ hm:m ≤ i,(center C.S p hm 0).rootTest (C.beta i p) (F i-C.O i p x 0) ≤ cider C ζ d m k*E i * flight C (-RelayDifference.gamma) (i,p)
   have hM:∀ᶠ i in atTop,∃ x,f i x:=by
      filter_upwards [hp'] with i ⟨hi,Z,t,Q,hT⟩; obtain ⟨v,hV,hL⟩:= Vintage.YM.MergeProof.pudding C i p d B W u ψ φ δ ζ r D H h (F i) Z Q t (E i) hi hT; refine ⟨v,?_,fun m k hm hk hb hn=>?_⟩ -- splits f
      · let x:= (C.factory d i p).terminal.symm v; let A0:= (C.path.levels.params i).columns
        have ht:0 ≤ Q:= hT.fuel.le; have hA : 1 ≤ A0:= (C.path.levels.params _).columns_ge; have hp:2*(1+A0)*Q ≤ E i:=le_trans (mul_le_mul_of_nonneg_right (show 2*(1+A0)≤4*(1+A0) by linarith only [hA]) ht) hT.dom
        have hz:0 ≤ Q:=ht; have hc:Y.coeffSize Z.x ≤ E i:=(le_trans (b:=Y.coeffSize Z.x+t) (le_add_of_nonneg_right (rem_nonneg hT.pay)) hT.charge).trans ((le_mul_of_one_le_left ht (show 1 ≤ 2*(1+A0) by linarith only [hA])).trans hp)
        have hr:Y.coeffSize (x-Z.x) ≤ E i:=by rw [Work.G08.size_sub_rev]; exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (show 1 ≤ 32*(1+A0)^2 by nlinarith only [hA])).trans (hV.trans hp)
        exact (RelayDifference.norm_cost Y x).trans ((Work.G08.size_triangle Y x Z.x).trans ((add_le_add hc hr).trans_eq (two_mul _).symm))
      have he:= hL m k hm hk hb Motion.nil hn; rw [dance_nil] at he; exact he
   let x i:= if h:∃ z,f i z then Classical.choose h else 0
   have ht: ∀ᶠ i in atTop,f i (x i):= hM.mono fun i hi=> by unfold x; rw [dif_pos hi]; exact Classical.choose_spec hi
   refine ⟨x, ((Slow.const (C:=C) (f:=Extraction.Order.full) (2:ℝ)).mul hE).reduce ((cutoff_grows _).eventually (ht.mono fun i hi=> hi.1.trans (Real.le_norm_self _))), ⟨hp.subH (thorP H x),?_⟩⟩
   filter_upwards [eventually_ge_atTop (C.ref d)] with m hm ε he; let k:= Stock.Tabs.chosen _ 1 B m; have hK:Stock.Tabs.opens C.path.levels 1 m k:= Stock.Tabs.opened ..
   have he' := Rested.sinking (w:=fun i=> cider C ζ d m k*E i) ((Slow.const _).mul hE) (show 0<RelayDifference.gamma by norm_num [RelayDifference.gamma]) he p
   filter_upwards [eventually_gt_atTop k,ht,he'] with i hi ht he hn; exact (ht.2 m k (hm.trans hK.1) hi hK hn).trans he
end YM.UVExtension.Fallow
