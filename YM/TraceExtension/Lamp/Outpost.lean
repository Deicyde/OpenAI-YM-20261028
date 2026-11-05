import YM.TraceExtension.Lamp.Dan

/-!
# Residue matrix insert characteristics consumed by infrared lemma. Align over same Scene.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{W:Type*}{g:W→Side}{p:Clip}{R:W→PathData G}{L:Filter W}{a C σ A:ℝ} {ε:W→ℝ}{V:∀ w, Dart G (g w)}
structure Oil {k:ℕ}(L:Filter W)(F:∀ w, WildM G (g w) k k): Prop where
    jets : Pella (fun _=>0) F 2
    turn(i j:Loc G k): Tendsto (fun w=>carb 0 (F w) i j (![]:Fin 0→_) 0) L (𝓝 0) ∧ Tendsto (fun w=>fderiv ℝ (carb 0 (F w) i j (![]:Fin 0→_)) 0) L (𝓝 0)
    hat(i j:Loc G k)(x:Loc G 1): Tendsto (fun w=> carb 0 (F w) i j (![x]:Fin 1→_) 0) L (𝓝 0)
lemma onsite (Q:Tendsto (fun w=>(g w).val) L atTop)(h:Scene g V p R a C ε)(ht:Flare g R p σ A)(hp:Tendsto ε L (𝓝 0))(hG:G.Simple) (b:Axis):
    let Y(w):=(V w).Y b 0; Oil L (fun w=> wB (stampQ 0) b (Y w) ∘ input G (g w))∧Oil L (g:=g) (fun w=> wG (stampQ 0) b∘ input G (g w)):=by
    intro Y
    have hz(w):Y w∈ rains G _:= (h.house w).sound.palm b 0
    have he(w): Cloaked (Y w):=by obtain ⟨h,_⟩:=hz w;exact h
    have hc(w i):= pea_rain (hz w) ((h.house w).Y b _) h.c0 h.vp.le i
    obtain ⟨A',hA,H⟩:= pipe_w G 3
    have hy:Pella (fun w:W=>(0:Site (g w))) (fun w=>tidal (Y w)∘ input G (g w)) 2:=by
        have hp:=h.vp; refine ⟨_,A'*C, ?_,mul_nonneg hA h.c0,fun w=> tidal_pay _ (he w) (H (g w) _ 0 C (a/5) (by positivity) h.c0 (he w) (hc w))⟩; positivity
    obtain ⟨hc',hd⟩:= locus_extra hy b
    have hM: CodeM (g:=g) (fun _=>0) (fun w=> Y w ∘ input G (g w)) 1:=⟨a/5,C,div_pos h.vp (by norm_num),h.c0,fun w i=>(hc w i|>.tilt le_rfl le_rfl (by norm_num))⟩
    choose B τ P D h' hv hu hh using ht.tanks
    have hx(w): (Tempo (wB (stampQ 0) b (Y w) ∘ input G (g w)))∧(Tempo (wG (stampQ 0) b∘ input G (g w))):= PaceV b (hz w) (h' w) ((hull_m (μ:= (1:ℝ)) zero_lt_one le_rfl (h' w) (hv w) (hu w) (hh w)).1.det_pos.ne')
    let F(w):=(wB (stampQ 0) b (Y w) ∘ input G (g w))
    let H(w):=(wG (stampQ 0) b∘ input G (g w));
    have hm(i j:Loc G 1)(x y:Cover): Tendsto (fun w=>w0 (F w 0) i j x y) L (𝓝 0):=by
        have hw:= combine_r Q b hz hp (fun w=>(h.house w).orb b 0) hM hG x y i j; refine hw.congr' (Eventually.of_forall (fun w=>?_)); unfold F; simp only[Function.comp_apply,input_zero]
    have hQ(i j:Loc G 0)(x y:Cover): Tendsto (fun w=> w0 (H w 0) i j x y) L (𝓝 0):=by
        have hw := combine_p Q x y b i j; refine hw.congr' (Eventually.of_forall fun w=>?_); unfold H; simp only[Function.comp_apply,input_zero]
    exact ⟨⟨hc',fun i j=>Tempo.pike Q (F:=F) hm (hc'.tada (by omega)) i j, fun i j x=> Tempo.via (F:=F) Q (fun w=>(hx w).1) hm (hc'.tada (by omega)) i j ![x]⟩,⟨hd,fun i j=>Tempo.pike (F:=H) Q hQ (hd.tada (by omega)) i j,fun i j x=>Tempo.via (F:=H) Q (fun w=>(hx w).2) hQ (hd.tada (by omega)) i j ![x]⟩⟩
end YM.Trace.Lamp
#print axioms YM.Trace.Lamp.saga
#print axioms YM.Trace.Lamp.onsite
