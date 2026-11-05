import YM.TraceExtension.Lamp.Thin
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{p:Clip}{M:PathData G}{α σ a b c τ A C D μ:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {W:Type*}{g:W→Side}{L:Filter W}(d i b:Axis)(q:G.ColorIndex)
lemma ultimate_cob {Y:Gal G f}(hs:G.Simple)(h:M.Bounds p α C D)(hμ:0<μ)(he:(stock p M μ (1:Config G f)).det≠0)(hp:Cloaked Y) :
   let S:= mainTerm p M (n:=f); let A:=marke p M μ (f:=f); let τ:=1/2* (cob d i q (sailM p M μ (aroma p M Y)))
   let J:=rill A Y ∘ input G f; let F:=rill S (ashore p M μ Y)∘ input G f; let W:=rill S (mica p M μ (stampQ 0) b (f:=f))∘ input G f
   cob d i q (lush Y ∘ input G f) = τ - cob d i q J -cob d i q F +(μ:ℂ)^ (2:ℕ)*(cob d i q (portage p M μ b f)+cob d i q W+cob d i q (lensW p M μ b Y)):=by
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
    rw [cob_near d i q hi,cob_plus d i q (F:=U-J-F) ((hU.sub hJ).sub hF) (show ContDiffAt ℝ ω (μ^ (2:ℕ) • (X+W+V)) _ from hP.const_smul (μ^ (2:ℕ))), cob_c d i q _ hP,cob_plus (F:=X+W) (H:=V) d i q (hX.add hM) hV',cob_plus d i q hX hM,cob_s d i q (F:=U-J) (hU.sub hJ) hF,cob_s d i q hU hJ, show U=(1/2:ℝ) • sailM p M μ (aroma p M Y) from rfl,cob_c d i q _ ht]; push_cast;rfl

lemma port_cob_local {R: W→PathData G}{μ':W→ℝ}(h:Flare g R p σ C)(hs:0 < σ)(hv:0<a)(hp:∀ w,a ≤ μ' w∧ μ' w≤c) (w): cob d i q (portage p (R w) (μ' w) b (g w))=0:=by
    obtain ⟨B,c',C',D,hR,hF,hx,hA⟩:=h.tanks w
    let F:=fun i=> zell p (R i) (μ' i) (g i); let V:= fun i=> wentG G (μ' i) (g i)
    have H:= h.house hs hv hp 2; have hz(i):= hv.trans_le (hp i|>.1); have h1(i): Circles (F i):=by obtain ⟨B,c,C,D,hR,hF,hx,hA⟩:=h.tanks i; refine cirB (hz i) hR (show (stock p (R i) (μ' i) (1:Config G (g i))).det≠0 from ?_); exact (hull_m (hz i) le_rfl hR hF hx hA|>.1.det_pos.ne')
    have h2(i): Circles (V i):=by obtain ⟨B,c,C,D,hR,hF,hx,hA⟩:=h.tanks i; exact cirG (hz i) hR
    let f:=g w
    have ht {k:ℕ} {X:∀ w,WildM G (g w) k k}(h:∀ i,Circles (X i))(hp:Parked X 2)(j v:Loc G k)(s:Axis):
       let V:=cutM (X w) j v; ContDiffAt ℝ ω (V (-(step s:Site f))-V 0) 0∧ cob d i q (V (-(step s:Site f))-V 0)=0:=by
       intro V; have hx:Traverse V:=cutT h hp j v|>.2 w; refine ⟨(hx.team _).sub (hx.team _),?_⟩; rw[cob_s _ _ _ (hx.team _) (hx.team _),cob_in _ _ _ hx,sub_self]
    have hu {k:ℕ}{X:∀ w,WildM G (g w) k k}(h:∀ i,Circles (X i))(hp:Parked X 2): ContDiffAt ℝ ω (terraF G b k (X w)) 0 ∧ cob d i q (terraF G b k (X w))=0:=by
       let A(i:Loc G k):= cutM (X w) i i (-step b)-cutM (X w) i i 0; rw[show terraF G b k (X w)=∑ i,A i from funext (fun x=>by rw[Finset.sum_apply]; exact era_teat b _)]
       refine ⟨?_,?_⟩
       · rw [show (∑ i,A i)=(fun z=>∑ i,A i z) from ?_]
         · exact ContDiffAt.sum (fun i _=> ht h hp i i b|>.1)
         funext z; rw[Finset.sum_apply]
       rw[cob_total d i q (F:=A) (fun i=> ht h hp i i b|>.1)]; exact sum_eq_zero fun i _=> ht h hp i i b|>.2
    have hL:= hu h1 H.2.2.1; have hh:=hu h2 H.2.2.2
    let Y(a:Axis)(j:G.ColorIndex):= cutM (F w) (mood G b j) (mood G a j) (-step a)-cutM (F w) (mood G b j) (mood G a j) 0
    have hY(a:Axis)(j:G.ColorIndex):= ht h1 H.2.2.1 (mood G b j) (mood G a j) a
    let Z(a:Axis):= ∑ j,Y a j
    have hW: localeZ b (F w)=∑ a,Z a:= funext fun x=>by rw[Finset.sum_apply]; unfold Z; simp_rw [Finset.sum_apply]; exact era_deal b _
    have hX(a:Axis): ContDiffAt ℝ ω (Z a) 0:=by rw [show Z a=(fun x=>∑ j,Y a j x) from funext fun x=> Finset.sum_apply ..]; exact ContDiffAt.sum fun i _=> hY a i|>.1
    have hV:ContDiffAt ℝ ω (localeZ b (F w)) 0:=by rw[hW,show (∑ a,Z a)=(fun x=>∑ a,Z a x) from funext fun x=> Finset.sum_apply ..]; exact ContDiffAt.sum fun a _=> hX a
    let c:ℝ:=1/2; change cob d i q (localeZ b (F w)-c • terraF G b 1 (F w)+ c • terraF G b 0 (V w))=0; rw [cob_plus (F:=localeZ b (F w)- c • terraF G b 1 (F w)) (H:= c • terraF G b 0 (V w)) d i q (hV.sub (hL.1.const_smul c)) (hh.1.const_smul c), cob_s d i q hV (H:= c • terraF G b 1 (F w)) (hL.1.const_smul c), cob_c d i q _ hL.1, cob_c d i q _ hh.1,hL.2,hh.2]; simp only [mul_zero,sub_zero,add_zero,hW]; rw[cob_total d i q hX]; apply sum_eq_zero fun z _=>?_ ; unfold Z; rw [cob_total d i q (F:= Y z) (fun i=>hY z i|>.1)]; exact sum_eq_zero fun i _=> hY z i|>.2

lemma cob_E {Y:∀ w,Gal G (g w)}{F:∀ w,Peat G (g w)}
    (Q:Tendsto (fun w=> (g w).val) L atTop)(h:knick F)(hs:G.Simple)(he:∀ w,Contours (F w))(hp:∀ w,Cloaked (Y w))(ht:CodeM (g:=g) (fun _=>0) (fun w=>Y w ∘ input G (g w)) 1): Tendsto (fun w=>cob d i q (rill (F w) (Y w) ∘ input G (g w))) L (𝓝 0):=by
    apply high_filter; intro v hv; have H:=Q.mono_left hv; obtain ⟨T,hT⟩:=shine v h; obtain ⟨K,hK⟩:=flamed v ht hp
    let V w:=rill (F w) (Y w)∘input G (g w); let Z w x:=(pitchf (g w):ℂ)⁻¹^ (2:ℕ)*clipP i q (V w) (wrap (g w) (ra d x)) (-(wrap (g w) (ra d x)))
    have hp': Tendsto (fun w=>(pitchf (g w):ℂ)) (↑v:Filter W) (𝓝 0):=by exact Complex.continuous_ofReal.continuousAt.tendsto.comp (gran H).void
    have hx(p:ℤ): Tendsto (fun w=> Z w p) (↑v:Filter W) (𝓝 0):=by
       have h:= hp'.mul (buzz d i d q H hT h hs he hK hp ht (p,0)); rw [zero_mul] at h; refine h.congr' (Eventually.of_forall fun w=>?_)
       dsimp only; unfold Z V; rw [← clue_at]; have hx:(pitchf (g w):ℂ) ≠0:=by exact_mod_cast (pitch_pos (f:=g w)).ne'
       field_simp
    apply Rose.alight (pan_coh (F:=Z) (H:=0) (fun z=> by unfold Rose; rw[show (fun w:W=> (0:W→ℤ→ℂ) w z)=0 from rfl,sub_zero]; exact hx z))
    exact tendsto_const_nhds.congr (fun i=> (map_zero PanZ).symm)

end YM.Trace.Lamp
