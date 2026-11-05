import YM.TraceExtension.Lamp.Vernal
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{p:Clip}{M:PathData G}{α σ a b c τ A C D μ:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {W:Type*}{g:W→Side}{L:Filter W}(d i b:Axis)(q:G.ColorIndex)
variable {R:W→PathData G}{ε:W→ℝ}{V:(w:W)→Dart G (g w)}
lemma fawn {b':ℝ}(Q:Tendsto (fun x=>(g x).val) L atTop)(hG:G.Simple)(h:Scene g V p R a C ε)(H:Flare g R p σ A)(hσ:0<σ) (hM:0<b')(hε:Tendsto ε L (𝓝 0)):
    Rose L (fun w=> cob d i q (lush ((V w).Y b 0) ∘ input G (g w))) (fun w=> (b':ℂ)^ (2:ℕ)*cob d i q (lensW p (R w) b' b ((V w).Y b 0))):=by
    let μ':W→ℝ:=fun _=> b';have hm(w:W): b' ≤ μ' w ∧ μ' w ≤ b':=⟨le_rfl,le_rfl⟩
    choose B A' N D hp hF ht hs using H.tanks
    let Y w b:= (V w).Y b 0; let S w:=mainTerm p (R w) (n:=g w); let Z w:= marke p (R w) (μ' w) (f:=g w)
    let U w:=input G (g w); let A'X w b:= ashore p (R w) (μ' w) (Y w b); let M' w b:= mica p (R w) (μ' w) (stampQ 0) b (f:=g w)
    have hz(w b):Y w b∈rains G _:= (h.house w).sound.palm b 0; have hu(w b): Cloaked (Y w b):=by obtain ⟨p,h⟩:= hz w b;exact p
    have he(w):= hM.trans_le (hm w|>.1); have hs'(w):(stock p (R w) (μ' w) (1:Config G (g w))).det≠0:=by have hx:=(H.posit he w);rw[input_zero] at hx;exact hx.det_pos.ne'
    have hT:= H.house hσ hM hm 1
    have hc:∀ w b i, Pet Prod.fst 0 (fun z=> Y w b (U w z) i) (a/5) (C* Decay (a/5) 0 i.1) 3:= fun w b i=> pea_rain (hz w b) ((h.house w).Y b _) h.c0 h.vp.le i
    obtain ⟨T,h',HT⟩:= pipe_w G 3; have hh:= hT.2.2.1; have hv:= hT.2.2.2; have hy:=h.c0; have ha:=h.vp
    have hR(w:W)(b:Axis):=HT (g w) (Y w b) 0 _ _ (by positivity) hy (hu w b) (hc w b)
    have hX(b): CodeM (g:=g) (fun _=>0) (fun w=> A'X w b ∘ U w) 1:=by
        have hc:0≤ T*C:=mul_nonneg h' hy; have hd:0 < a/5/((↑(3:ℕ):ℝ)+1)/( (↑(3:ℕ):ℝ)+2):=by positivity
        have he: Pella (fun w=>(0:Site (g w))) (fun w=> tidal (Y w b) ∘ U w) 2:=⟨_,_,hd,hc,fun w=>tidal_pay _ (hu w b) (hR w b)⟩
        exact ashore_budget (he.tada (by norm_num)) hh hv (shoreX_step hh (fun w=> hR w b) (fun w=> hu w b) hd hc)
    let F(w) b:= sailM p (R w) (μ' w) (aroma p (R w) (Y w b)); let P(w) b:= portage p (R w) (μ' w) b (g w); let X(w) b:= lensW p (R w) (μ' w) b (Y w b); let μV(w):=(μ' w:ℂ)^ (2:ℕ)
    let J w b:= rill (Z w) (Y w b)∘U w; let M w b:= rill (S w) (M' w b)∘ U w; let E w b:=rill (S w) (A'X w b)∘ U w
    have h₁:= cob_E d i q Q (mark_kin H hσ hM hm) hG (fun i=> contours_m (he i) (hp i) (hs' i)) (fun w=>hu w b) (CodeM.mk (o:=fun w : W=> (0:Site (g w))) (X:=fun i=> Y i b ∘ U i) (m:=1) ⟨_,C, by exact show 0<a/5 by positivity,h.c0,fun w i=> (hc w b i).tilt le_rfl le_rfl (by decide)⟩)
    have hk:=knick_path H hσ
    have h₂:=cob_E d i q Q hk hG (fun i=>contours_main (hp i)) (fun w=>cloak_shore (hp w) (he w) (hs' w) (hu w b)) (hX b)
    have h₃:=cob_E d i q Q hk hG (fun i=>contours_main (hp i)) (fun w=> cloak_mica (stampQ 0) b (hp w) (he w) (hs' w)) (mica_budget (fun w=>(0:Site (g w))) b hh hv)
    have h₄:= vanish_cob d i q Q b h.house h.pad hε h.clip H hσ ha h.c0 hM hm
    have ht0: Tendsto (fun w=> 1/2*cob d i q (F w b)-cob d i q (J w b)-cob d i q (E w b)+ (b':ℂ)^ (2:ℕ)*cob d i q (M w b)) L (𝓝 0):=by
       convert ((( (h₄.const_mul (1/2:ℂ)).sub h₁).sub h₂).add (h₃.const_mul ((b':ℂ)^ (2:ℕ)))) using 1
       simp
    refine ht0.congr' (Eventually.of_forall fun w=>?_); rw[Pi.sub_apply,ultimate_cob _ _ _ _ hG (hp w) (he w) (hs' w) (hu w b),port_cob_local _ _ _ _ H hσ hM hm w]
    change 1/2*cob d i q (F w b)-cob d i q (J w b)-cob d i q (E w b)+ (b':ℂ)^(2:ℕ)*_= _ -(μ' w:ℂ)^(2:ℕ)*_
    unfold F M E J Y Z S M' A'X U μ'; ring
end YM.Trace.Lamp
