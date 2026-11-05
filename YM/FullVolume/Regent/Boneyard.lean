import YM.FullVolume.Regent.Moment
/-! Holding tag alloc, path limit shape. Real.As.rental prices.Plain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Beacon
open Lattice RG Precision Wilson Filter Function Laurent Bloch Exterior Next.Free.Retort Tralis Shade
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:Side}{σ η:ℝ}
structure Flagship (G:Gauge) where
    a:Cameo G 1
    b:Cameo G 2
    c:Cameo G 3
namespace Flagship
variable {V: Reel G} (K:Flagship G)
def Lash (V: Reel G)(x:Flagship G)(R:PathData G):Prop := R.loop=ringT V.e2.δ x.a ∧ R.cubic=ringT V.e3.δ x.b ∧ R.quartic=ringT V.e4.δ x.c
def Rig (V: Reel G)(x:Flagship G)(n:ℕ→Side)(r L :ℝ) :Prop:= x.a ∈ V.e2.royal n ∧ ‖x.a‖≤ L ∧ x.b∈ V.e3.royal n∧ ‖x.b‖≤r ∧ x.c∈ V.e4.royal n∧ ‖x.c‖≤ r
lemma laying {R:PathData G}{T:ℕ→Side}{A L:ℝ}(h:V.Wing T R A L):∃ p:Flagship G,Lash V p R∧ Rig V p T A L:=by obtain ⟨S,hp,h1,h2,T,hT,h3,h4,X,hX,h5,h6⟩:=h; exact ⟨⟨S,T,X⟩,⟨h2,h4,h6⟩,hp,h1,hT,h3,hX,h5⟩
structure Beacon (x:ℕ→ Flagship G)(K:Flagship G)(r L:ℝ):Prop where
    a:Gleam (fun i=>(x i).a) K.a L
    b:Gleam (fun i=>(x i).b) K.b r
    c:Gleam (fun i=>(x i).c) K.c r

lemma grooves {R:PathData G}{p:Clip}{x:Flagship G}{w K L:ℝ}(h:Lash V x R)(hp:R.Bounds p w K L): AtomWall (ringT V.e2.δ x.a) w L ∧ Bs G (ringT V.e2.δ x.a) ∧ AtomWall (ringT V.e3.δ x.b) w K ∧ AtomWall (ringT V.e4.δ x.c) w K:=by
    rw [←h.1,←h.2.1,←h.2.2]; exact ⟨⟨hp.two,fun i=>(hp.invariant i).1⟩, brands hp,⟨hp.three,fun i=>(hp.invariant i).2.1⟩,hp.four,fun i=>(hp.invariant i).2.2⟩
lemma proved {R:ℕ→ PathData G}{S:PathData G}{p:Clip}{x:ℕ→Flagship G}{K:Flagship G}{w A L a b:ℝ}(h:Drive R S w A)(hp: Beacon x K a b)(he:V.Price w)(hx:Lash V K S)(hv:∀ᶠ i in atTop, Lash V (x i) (R i) ∧ (R i).Bounds p w A L): S.Bounds p w A L:=by
    have ha := hv.mono fun i hi=>grooves hi.1 hi.2; have hg:= compassion hp.a he.1 (ha.mono fun i hi=>hi.1); have hf:= consulates hp.a V.e2.hired (ha.mono fun i hi=>⟨hi.2.1,hi.1.2⟩); have hQ:= compassion hp.b he.2.1 (ha.mono fun i hi=>hi.2.2.1); have hP:= compassion hp.c he.2.2 (ha.mono fun i hi=>hi.2.2.2)
    rw [← hx.1] at hg hf; rw [← hx.2.1] at hQ; rw [← hx.2.2] at hP
    have hb (x:PlaqAxes): Summable fun i=> ‖(S.row x i).1‖:= Summable.of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=> le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.wage.le (by positivity)))) (h.funds x).2.1
    refine ⟨h.wage,h.funds,hg.1,hQ.1,hP.1, fun i=>⟨hg.2 _,hQ.2 _,hP.2 _⟩,?_, ?_, fun i x=>⟨(hf i x S rfl).1.summable,fun k=> ((hf i x S rfl).2 k).summable⟩,fun i x=>⟨(hf i x S rfl).1.tsum_eq,fun k=> ((hf i x S rfl).2 k).tsum_eq⟩⟩
    · intro i q; refine (hb i).of_norm.indicator {k | (S.row i k).2.plaq=q} |>.congr (fun k => by simp [Set.indicator])
    intro i j
    have hX (i j): Tendsto (fun n=> (R n).symbol0 i j) atTop (𝓝 (S.symbol0 i j)):=by
        let f(n:ℕ)(k:ℕ):= if ((R n).row i k).2.plaq=j then ((R n).row i k).1 else 0
        let g(k:ℕ):= if (S.row i k).2.plaq=j then (S.row i k).1 else 0
        change Tendsto (fun n=> ∑' k, f n k) _ (𝓝 (∑' k,g k))
        refine tendsto_tsum_of_dominated_convergence ((coins h.wage).mul_left A) (fun k=>?_) ?_
        · have H (V:PathData G) (hx: (V.row i k).2=flag k): ((V.row i k).2.plaq)=(flag k).plaq:=by rw [hx]
          unfold g; rw [H _ (h.here i k)]
          split; next hx=> exact (h.ink i k).congr' (h.flit.mono fun n h=> (if_pos (Eq.trans (H _ (h i k)) hx)).symm)
          next hx=> exact tendsto_const_nhds.congr' (h.flit.mono fun n h=> (if_neg (fun v=>hx ((H _ (h i k)).symm.trans v))).symm)
        filter_upwards [h.flit,h.sails] with n h hs k; let T:=(R n).row i k
        have hG: |T.1| * Real.exp (w*T.2.length) ≤A:=by
               have hh := hs i; exact le_trans (by simpa using hh.2.1.sum_le_tsum {k} (fun j _=> hh.1 j)) hh.2.2
        have H : ‖T.1‖≤ A*channel (-w) k:=by
            change |T.1| ≤ _; unfold channel; rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _), ← show T.2=flag k from h i k]; exact hG
        unfold f; split; · exact H
        rw [norm_zero]; exact (norm_nonneg _).trans H
    apply tendsto_nhds_unique ((tendsto_const_nhds.add (tendsto_finsetSum _ fun x _=> (hX x i).mul (hX x j))).congr' (hv.mono fun z h=> h.2.metric i j)) tendsto_const_nhds
end Flagship
end YM.Stationary.Beacon
