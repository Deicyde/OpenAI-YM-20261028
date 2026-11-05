import YM.TraceExtension.Lamp.Oct
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{p:Clip}{M:PathData G}{α σ a b c τ A C D μ:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {W:Type*}{g:W→Side}{L:Filter W}(d i b:Axis)(q:G.ColorIndex)
-- factors
abbrev senior (F H:WildM G f k k)(x:Link G f):ℝ:=(F x*H x).trace
lemma memo_se (F:WildM G f k k) (h:Memo F 0) : ContDiffAt ℝ ω (fun x=>(F x).trace) 0:= ContDiffAt.sum fun i _=> h i i
lemma sequester {F H:WildM G f k k}(h:Memo F 0)(hp:Memo H 0): ContDiffAt ℝ ω (senior F H) 0:= memo_se _ (h.cross hp)

abbrev zell (p:Clip)(R:PathData G)(μ:ℝ)(f:Side):WildM G f 1 1:= shellB p R μ ∘ input G f
abbrev wentG (G:Gauge)(μ:ℝ)(f:Side):WildM G f 0 0:= shellG μ ∘ input G f
abbrev lensW (p:Clip)(R:PathData G)(μ:ℝ)(b:Axis)(Y:Gal G f): Maze G f:= senior (zell p R μ f) (wB (stampQ 0) b Y ∘ input G f)+ senior (wentG G μ f) (wG (stampQ 0) b ∘ input G f)
abbrev terraF (G:Gauge)(b:Axis)(k:ℕ)(F:WildM G f k k):= senior F (fun _=>teat G (stampQ (0:Site f)) b k)
abbrev localeZ (b:Axis)(F:WildM G f 1 1):= senior F (fun _=>deal G (stampQ (0:Site f)) b)
abbrev portage (p: Clip)(R:PathData G)(μ:ℝ)(b:Axis)(f:Side): Maze G f:= localeZ b (zell p R μ f) -(1/2:ℝ) • terraF G b 1 (zell p R μ f) + (1/2:ℝ) • terraF G b 0 (wentG G μ f)
lemma ultimate {Y:Gal G f}(hs:G.Simple)(h:M.Bounds p α C D)(hμ:0<μ)(he:(stock p M μ (1:Config G f)).det≠0)(hp:Cloaked Y) :
   let S:= mainTerm p M (n:=f); let A:=marke p M μ (f:=f); let τ:=1/2* (lux d i q b (sailM p M μ (aroma p M Y)))
   let J:=rill A Y ∘ input G f; let F:=rill S (ashore p M μ Y)∘ input G f; let W:=rill S (mica p M μ (stampQ 0) b (f:=f))∘ input G f
   lux d i q b (lush Y ∘ input G f) = τ - lux d i q b J -lux d i q b F +(μ:ℂ)^ (2:ℕ)*(lux d i q b (portage p M μ b f)+lux d i q b W+lux d i q b (lensW p M μ b Y)):=by
    intro S A τ J F W
    let L:= input G f; have hv:Army L 0:=Army.powL (v:=id) contDiffAt_id; have hx: L 0=1:= input_zero ..
    obtain ⟨hV,hT⟩:= gate_shell h hμ he hv hx
    have hz := (gauge_fleur (Y:=Y) h hμ he hp hv hx)
    let X:=portage p M μ b f; let U:= (1/2:ℝ) • sailM p M μ (aroma p M Y); let V:=lensW p M μ b Y
    obtain ⟨hh,hW⟩:= w_memo (stampQ (0:Site f)) b hp hv hx
    have ht: ContDiffAt ℝ ω (sailM p M μ (aroma p M Y)) 0:= hearth_s (aroma_diff h hp) hV
    have hU:ContDiffAt ℝ ω U 0:=ht.const_smul (1/2:ℝ)
    have hJ : ContDiffAt ℝ ω J 0:= (rill_state hs (dyed_mark h hμ he) hp).1
    have hF : ContDiffAt ℝ ω F 0:= (rill_state hs ((contours_main h).coat) (cloak_shore h hμ he hp)).1
    have hX: ContDiffAt ℝ ω X 0:= by
       let f'(b:Axis):= localeZ b (zell p M μ f)
       have hp: ContDiffAt ℝ ω (f' b) 0:= sequester hV (Memo.raw _ _)
       have hs: ContDiffAt ℝ ω (terraF G b 1 (zell p M μ f)) 0:= sequester hV (Memo.raw _ _); have hx:ContDiffAt ℝ ω (terraF G b 0 (wentG G μ f)) 0:= sequester hT (Memo.raw _ _)
       exact (hp.sub (hs.const_smul (1/2:ℝ))).add (hx.const_smul (1/2:ℝ))
    have hV':ContDiffAt ℝ ω V 0:= (sequester hV hh).add (sequester hT hW)
    have hM :ContDiffAt ℝ ω W 0:= (rill_state hs ((contours_main h).coat) (cloak_mica (stampQ 0) b h hμ he)).1
    have hP :ContDiffAt ℝ ω (X+W+V) 0:=(hX.add hM).add hV'
    have hi: lush Y∘ L=ᶠ[𝓝 0] U-J-F+ μ^ (2:ℕ) • (X+W+V) :=by
       filter_upwards [hz,mica_lim (Y:=Y) (stampQ 0) b h hμ he hv hx] with z hk hf
       change (sailM p M μ (aroma p M Y) z)/2 - lush Y (L z)= J z-μ^2*_+F z at hk
       rw [hf] at hk; rw[show (shellB p M μ (L z) * (deal G (stampQ (0:Site f)) b - (1/2:ℝ) • teat G (stampQ (0:Site f)) b 1)).trace = (localeZ b (zell p M μ f) z)-(1/2)* (terraF G b 1 (zell p M μ f) z) from ?_] at hk
       change sailM _ _ _ (aroma p M Y) z/2-lush _ _=J z-μ^2*(X z+W z+V z)+F z at hk
       change lush Y (L z)=(1/2:ℝ)*sailM p M μ (aroma p M Y) z-J z-F z+ μ^2*(X z+W z+V z); linarith only [hk]
       rw[Matrix.mul_sub, Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul];rfl
    rw [lux_far d i b q hi,lux_a d i b q (F:=U-J-F) ((hU.sub hJ).sub hF) (show ContDiffAt ℝ ω (μ^ (2:ℕ) • (X+W+V)) _ from hP.const_smul (μ^ (2:ℕ))), lux_c d i b q _ hP,lux_a (F:=X+W) (H:=V) d i b q (hX.add hM) hV',lux_a d i b q hX hM,lux_s d i b q (F:=U-J) (hU.sub hJ) hF,lux_s d i b q hU hJ, show U=(1/2:ℝ) • sailM p M μ (aroma p M Y) from rfl,lux_c d i b q _ ht]; push_cast;rfl
-- Portage sum b
variable {F:∀ w, WildM G (g w) 1 1}{H:∀ w,WildM G (g w) 0 0} {R:W→PathData G} {μ':W→ℝ}
lemma luxSum (Q:Tendsto (fun w=>(g w).val) L atTop)(h:Flare g R p σ C)(hs:0<σ)(hv:0<a)(hp:∀ w,a ≤ μ' w∧ μ' w≤ c) : Rose L (fun w=> ∑ i':Axis,lux d i q i' (portage p (R w) (μ' w) i' (g w))) (fun w=> - highray d i q (zell p (R w) (μ' w) (g w))+2 * highray d i q (wentG G (μ' w) (g w))):=by
    have ht:= h.house hs hv hp 2; let F(w):= zell p (R w) (μ' w) (g w); let U(w):=wentG G (μ' w) (g w)
    have he w:=hv.trans_le (hp w|>.1)
    choose B a b A hp' hA H hh using h.tanks
    have hx(w):Circles (F w):= cirB (he w) (hp' w) (show (stock p (R w) (μ' w) (1:Config G (g w))).det≠0 from (hull_m (he w) le_rfl (hp' w) (hA w) (H w) (hh w)|>.1.det_pos.ne')); have hu(w):Circles (U w):=cirG (he w) (hp' w)
    let X(w):=highray d i q (F w);let Y(w):=highray d i q (U w); let V(w)(b:Axis):=∑ x:G.ColorIndex,cob d i q (cutM (F w) (mood G b x) (mood G b x) 0)
    have hr:= ht.2.2.1; have hW:=ht.2.2.2
    obtain ⟨A,p,hZ,hP,g'⟩:= (show Parked F 2 from hr).top
    obtain ⟨D,q',hD,hq,gT⟩:= (show Parked U 2 from hW).top
    have hR (b): Rose L (fun w=>lux d i q b (localeZ b (F w)-(1/2:ℝ) • terraF G b 1 (F w)+(1/2:ℝ) • terraF G b 0 (U w))) (fun w=>V w b-(1/2)*X w+(1/2)*Y w):=by
       have ht:=Rose.inc (Rose.dec (deal_b d i b q Q hx hr) (roseRate (1/2) (teat_ro d i b q Q hx hr))) (roseRate (1/2) (teat_ro d i b q Q hu hW))
       apply Rose.chain (Rose.skip ?_) ht
       filter_upwards with w; let f:=g w; let X:= localeZ b (F w); let Y:=terraF G b 1 (F w); let Z:= terraF G b 0 (U w)
       have hv : Memo (F w) 0:=fun i j=>(g' w i j).1; have hm:Memo (U w) 0:=fun i j=>(gT w i j).1
       have hX: ContDiffAt ℝ ω X 0:=sequester hv (Memo.raw _ _);have hY:ContDiffAt ℝ ω Y 0:=sequester hv (Memo.raw _ _); have hZ:ContDiffAt ℝ ω Z 0:=sequester hm (Memo.raw _ _)
       let t:ℝ:=1/2; have hu: ContDiffAt ℝ ω (t • Y) 0:= hY.const_smul t; change lux d i q b (X - t • Y + t • Z)= lux d i q b X - _ + _
       rw [lux_a d i b q (F:=X-t • Y) (hX.sub hu) (H:=t • Z) (hZ.const_smul t),lux_s d i b q hX hu,lux_c d i b q _ hY,lux_c d i b q _ hZ]; unfold t; push_cast;rfl
    apply Rose.chain (Rose.sumX (univ:Finset Axis) (fun i _=> hR i)) (Rose.skip ?_); filter_upwards with w; change ∑ a:Axis,(V w a-(1/2)*X w+(1/2)*Y w)= -(X w)+2*Y w
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_const,sum_const, Finset.card_univ, show Fintype.card Axis=4 from Fintype.card_fin _, show ∑ a,V w a=X w from ?_]; · simp; ring
    unfold X; rw[high_eq _ _ _ (hx w) (g' w) hZ hP,Fintype.sum_prod_type, ← Equiv.sum_comp axisEquiv];rfl
-- main global ward. Keep error poses uniform, µ-dependent lensW remaining.
structure Scene (g:W→Side)(V:(w:W)→Dart G (g w)) (p:Clip)(R:W→PathData G)(a C:ℝ) (ε:W→ℝ) : Prop where
    house w: Viz (V w) p (R w) a (fun _=>C) (fun _=> ε w) (ε w)
    pad w:(V w).March
    vp:0<a
    c0:0≤C
    clip w:0≤ε w∧ ε w≤ 1
variable {V:(w:W)→Dart G (g w)}{ε:W→ℝ}
abbrev umbra (p:Clip)(R:PathData G)(μ:ℝ)(n:Side) :ℂ:= -highray d i q (zell p R μ n)+2*highray d i q (wentG G μ n)

def suite (F:Axis→Axis→ℂ) := ∑ d,∑ i,(if d=i then 0 else F d i)
lemma suite_hold {F H:W→Axis→Axis→ℂ}(h:∀ d i,Rose L (fun w=>F w d i) (fun w=>H w d i)): Rose L (fun w=> suite (F w)) (fun w=> suite (H w)):=by
    unfold suite; refine Rose.sumX univ (fun d _=> Rose.sumX univ (fun i _=>?_)); by_cases he:d=i
    · simp only [he,↓reduceIte]; exact Rose.const _
    simp only[he,↓reduceIte]; exact h _ _
lemma suiteIL (c:ℂ)(F H J K K' U:Axis→Axis→ℂ): (suite (fun d i=> (1/2:ℂ)*F d i-H d i-J d i + c*(K d i+K' d i+U d i)))=(1/2:ℂ)*suite F-suite H-suite J+c*(suite K+suite K'+suite U):=by
    unfold suite; simp only[Fin.sum_univ_four];simp; ring
-- more simple
lemma scale_select {f g:W→ℂ}(c:W→ℂ)(h: DashQ L c)(hp:Rose L f g): Rose L (c*f) (c*g):=by unfold Rose; rw [← mul_sub,mul_comm c]; exact coh _ c hp h
lemma knick_path (h:Flare g R p α A)(ht:0<α) : knick (g:=g) (fun w=>mainTerm p (R w)):=by
    obtain ⟨η,D,hv,hD,H⟩:= H_park G p 0 ht A; refine ⟨_,_,hv,hD,fun w=>?_⟩
    obtain ⟨B,x,y,z,hk,_,_,_⟩:= h.tanks w
    intro i j; have hx:= H (g w) (R w) z hk i j
    apply pet_fixed; let p:= hx.2 0 le_rfl Fin.elim0; simp only [entry,iteratedFDeriv_zero_apply,Function.comp_apply,input_zero, spanSites,sum_of_isEmpty,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at p; exact p
lemma saga {b':ℝ}(Q:Tendsto (fun x=>(g x).val) L atTop)(hG:G.Simple)(h:Scene g V p R a C ε)(H:Flare g R p σ A)(hσ:0<σ) (hM:0<b')(hm:∀ w,b'≤μ' w∧ μ' w≤ c)(hε:Tendsto ε L (𝓝 0)):
    Rose L (fun w=> xup q (fun b=> lush ((V w).Y b 0) ∘ input G (g w))) (fun w=> (μ' w:ℂ)^ (2:ℕ)*(suite (fun d i=>umbra d i q p (R w) (μ' w) (g w)) + xup q (fun b=>lensW p (R w) (μ' w) b ((V w).Y b 0)))):=by
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
    have hm':DashQ L μV:=by refine ⟨c^2,sq_nonneg _,Eventually.of_forall fun w=>?_⟩; unfold μV; rw[norm_pow,Complex.norm_real,Real.norm_of_nonneg (he w|>.le)]; exact pow_le_pow_left₀ (he w|>.le) (hm w|>.2) _
    have hk:=knick_path H hσ
    have h₁: Rose L (fun w=> xup q (J w)) 0:=by unfold Rose; rw [sub_zero]; exact arcPay _ Q (mark_kin H hσ hM hm) hG (fun i=> contours_m (he i) (hp i) (hs' i)) hu (fun b=> ⟨_,C,by exact show 0<a/5 by positivity,h.c0,fun w i=> (hc w b i).tilt le_rfl le_rfl (by decide)⟩)
    have h₂: Rose L (fun w=> xup q (E w)) 0:=by unfold Rose; rw[sub_zero]; exact arcPay _ Q hk hG (fun i=> contours_main (hp i)) (fun w b=> cloak_shore (hp w) (he w) (hs' w) (hu w b)) hX
    have h₃: Rose L (fun w=> xup q (M w)) 0:=by unfold Rose; rw[sub_zero]; exact arcPay _ Q hk hG (fun i=> contours_main (hp i)) (fun w b=> cloak_mica (stampQ 0) b (hp w) (he w) (hs' w)) (fun a=> mica_budget (fun w=>(0:Site (g w))) a hh hv)
    have h₄ : Rose L (fun w=> xup q (F w)) 0:=Rose.chain (suite_hold (F:=fun w d i=> fata d i q (F w)) (H:=fun _ _ _=>0) (fun d i=>by unfold Rose; rw[show (fun _:W=>(0:ℂ))=0 from rfl,sub_zero]; exact vanish_r _ _ q Q h.house h.pad hε h.clip H hσ ha h.c0 hM hm)) (Rose.skip (Eventually.of_forall (fun i=>by dsimp only[suite];simp)))
    let V' w:=suite fun d i=> umbra d i q p (R w) (μ' w) (g w); have h₅: Rose L (fun w=>xup q (P w)) V':= suite_hold (F:=fun w d i=> fata d i q (P w)) (H:=fun w d i=>umbra d i q p (R w) (μ' w) (g w)) (fun d i=>luxSum d i q Q H hσ hM hm)
    refine Rose.chain (Rose.skip ?_) (Rose.chain (Rose.inc (Rose.dec (Rose.dec (roseRate (1/2) h₄) h₁) h₂) (scale_select _ hm' (Rose.inc (Rose.inc h₅ h₃) (Rose.const (fun w=> xup q (X w)))))) (Rose.skip ?_))
    · filter_upwards with w
      let F'(a:Axis):= lush (Y w a) ∘ U w
      have hz(d i: Axis): fata d i q F' = (1/2:ℂ)*fata d i q (F w)-fata d i q (J w)-fata d i q (E w)+μV w*(fata d i q (P w)+fata d i q (M w)+fata d i q (X w)):=by
         unfold fata; simp_rw[ show ∀ b: Axis,lux d i q b (F' b)= _ from fun b=> ultimate d i b q hG (hp w) (he w) (hs' w) (hu w b),sum_add_distrib,Finset.sum_sub_distrib, ← Finset.mul_sum]; rw [sum_add_distrib,sum_add_distrib]
      change suite (fun d i=>fata d i q F') = (1/2:ℂ)*xup q (F w)-xup q (J w)- xup q (E w) + μV w*(xup q (P w)+xup q (M w)+xup q (X w)); simp_rw[hz]; exact suiteIL (μV w) _ _ _ _ _ _
    filter_upwards with w; simp [μV,V']; left; rfl
end YM.Trace.Lamp
