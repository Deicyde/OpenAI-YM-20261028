import YM.TraceExtension.Verse.Movie
import YM.TraceExtension.Verse.Stars
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Function Filter Set Extraction Cells OS OS.Ground Lattice Spec
open scoped Topology BigOperators InnerProductSpace
variable {G: Gauge} {C: Family G} {F: Filter (ℕ×ℕ)} {f:Extraction.Order} {S:Table C.book} {V:Chamber S timeAxis}{A:Spread V} {p:A.Resolution}{k b : ℕ}

lemma ticket [F.NeBot] (Y: Seed C f S) (hf:F ≤ f.fuse) (H:p.Out) (hv:Steady V){x : p.X→Table C.book}(hs:∀ i,(x i).Hierarchy)(hq:∀ i,p.receives (x i) i)
    (c:ℝ)(hc:0≤c)(hb:b≤k)(E:Scene C F k)(hE: ∀ᶠ t:ℕ×ℕ in F,∃ hk:k ≤ t.1,
      let T:= Cells.center C.S t.2 (hb.trans hk) 0
      Interior (T.chamber 0) (E.cuts t.1 t.2 0) ∧ T.rootTest (C.beta t.1 t.2) (E.cuts t.1 t.2 0) ≤ c)(x':p.X):‖p.character x' (E.cluster A)‖ ≤ c:=by
    apply Retain.bit _ H _ _ hc
    intro n
    apply le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp (opening H hv hs hq Y.kernel (p':=hb) E n))
    filter_upwards [eventually_gt_atTop 0,eventually_all.mpr (fun i:Fin (2*n)→Fin E.num=> term_pass E i hf Y.generic hb)] with t ht hu
    have hh:Tendsto (fun i:ℕ×ℕ=> E.fromCut hb t n i.1 i.2) F (𝓝 (E.wanted hb t n S)):= by
       unfold Scene.wanted
       apply Tendsto.congr' ((fromCut_expand E Y.cutoff hb hf n t).mono fun _ hc=>hc.symm)
       exact tendsto_finsetSum Finset.univ fun i _=> tendsto_const_nhds.mul (hu i)
    apply le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hh)
    have hj:∀ᶠ i:ℕ×ℕ in f.fuse, 2*t*(2*n) ≤ (C.side b i.2).val:=by
       rw [Extraction.Order.fused]; unfold Extraction.Order.late
       have hp':= (C.S.period_strict.tendsto_atTop.comp f.per.cofinal).eventually_ge_atTop (2*t*(2*n))
       filter_upwards[hp'] with i hi
       exact Eventually.of_forall fun _ => hi.trans (Nat.le_mul_of_pos_right _ (C.S.denominator b).property)
    filter_upwards [hj.filter_mono hf,hE] with i hi hi'
    obtain ⟨hk,hI,h'⟩:= hi'; exact (Complex.re_le_norm _).trans (cutoff_bound hb hk E n t ht (Y.copies.all _ _) hi hI h')
end YM.Trace.Verse
