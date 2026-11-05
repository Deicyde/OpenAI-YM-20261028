import YM.TraceExtension.Lamp.Ply

/-! # Finite root-state takes far approx classical. ∂ currents trace station KK.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} (d i:Axis)(q:G.ColorIndex)
lemma cob_near {F H:Maze G f}(hd:F=ᶠ[𝓝 0] H): cob d i q F=cob d i q H:=by unfold cob; simp_rw [clip_far i q hd]
lemma twig_sum {X:Type}[AddCommGroup X][Module ℝ X] (J:Site f→X)(a :Axis): ∑ i, twig a J i=0:=by simp only[twig,sum_sub_distrib]; rw[show ∑ x:Site f,J (x+step a)=∑ x,J x from Equiv.sum_comp (Equiv.addRight (step a:Site f)) J]; simp
lemma polish (V:Dart G f)(h:Dart.March V)(x y:Axis)(i:Site f): V.J x y i=rj i (V.J x y 0):=by
    have he:=h.still i; have ht : rj i (V.J x y (i-i))=V.J x y i:= congr_arg (fun X=>Dart.J X x y i) he
    rwa[sub_self,eq_comm] at ht
lemma cob_abs (V:Dart G f){μ:ℝ}(h:Dart.March V)(hv:V.Sound M p)(hμ:0<μ)(hs:(stock p M μ (1:Config G f)).det≠0)(hp:M.Bounds p σ A D): ∑ b:Axis,cob d i q (sailM p M μ (V.J b b 0))=0:=by
    have ht a b:=traverse_pay hp hμ hs (V.J a b) (hv.heart ..) (polish V h a b)
    let J(a:Axis)(x:Site f):= V.J a a x
    let F(a:Axis)(x:Site f):=sailM p M μ (J a x)
    have hx(a:Axis)(x:Site f): Cleric (J a x):=by obtain ⟨h,_⟩:=hv.heart a a x; exact h
    have hh: ∑ a,∑ x,J a x=0:=by
       rw [sum_comm]; simp_rw[show ∀ x,∑ a,J a x= ∑ a:Axis, twig a (V.Q a) x from fun x=> (Finset.sum_apply ..).symm.trans ((congr_fun hv.hue x).trans (Finset.sum_apply ..))]; rw [sum_comm]; simp_rw [twig_sum]; simp
    have hg:(∑ a,∑ x,F a x)=ᶠ[𝓝 0] 0 :=by
       let K:=sailM p M μ (f:=f)
       have hF : (∑ a,∑ x,F a x)=ᶠ[𝓝 0] K 0:=by
            have ht:(∑ a:Axis,∑ x,F a x)=ᶠ[𝓝 0] (∑ a:Axis, K (∑ x,J a x)):=by
               have hu(a): (∑ x,F a x)=ᶠ[𝓝 0] K (∑ x,J a x):=(arm_sail_t _ (fun i _=>hx a i)).symm
               filter_upwards [eventually_all.mpr hu] with x hx; rw [Finset.sum_apply, Finset.sum_apply]; exact Finset.sum_congr rfl fun a _=>hx a
            rw[← hh]; exact ht.trans (arm_sail_t _ (fun i (_ : i ∈ univ)=> (show Cleric _ from (clergy G f).sum_mem (fun a _=> hx i a)))).symm
       refine hF.trans ?_; have h' : K ((∑ i:Fin 0,(0:Peat G f))) =ᶠ[𝓝 0] ∑ _i:Fin 0,K 0:= arm_sail_t _ (fun i (_:i∈univ)=> Fin.elim0 i); simpa using h'
    let M:ℝ:= Fintype.card (Site f); have hN:(M:ℂ)≠0:=by unfold M; push_cast; exact Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
    apply (mul_eq_zero.mp (show (M:ℂ)*(∑ b,cob d i q (F b 0))=0 from ?_)).resolve_left hN
    have hV(a):ContDiffAt ℝ ω (∑ x,F a x) 0:=by rw [show (∑ x,F a x)=fun v=>∑ x,F a x v from funext fun v=> Finset.sum_apply ..]; exact ContDiffAt.sum fun i _=> (ht a a).team _
    have hx:= (cob_near d i q hg); rw [cob_total d i q hV] at hx
    simp_rw [show ∀ b,cob d i q (∑ x,F b x)=(Fintype.card (Site f):ℂ)*cob d i q (F b 0) from fun b=> cob_s_tot d i q (A':=F b) (ht b b)] at hx
    rw [← mul_sum] at hx; unfold M; push_cast; rw [hx]; simp [cob,pani,clipP,beat,enlarge,recording_apply]

variable (Tn:Tendsto (fun w=>(g w).val) L atTop){V:∀ w,Dart G (g w)}{R:W→PathData G}{μ ε:W→ℝ}
include Tn
lemma vanish_r (hV: ∀ w, Viz (V w) p (R w) a (fun _=> C) (fun _=> ε w) (ε w))(h:∀ w,Dart.March (V w))(he:Tendsto ε L (𝓝 0))(hε:∀ w,0≤ε w∧ε w≤1)(hh:Flare g R p α A)(ht:0 < α)(ha:0<a)(hp:0≤ C)(hb:0<b)(hμ:∀ w, b ≤ μ w ∧ μ w≤c):
    Tendsto (fun w=>∑ b:Axis,lux d i q b (sailM p (R w) (μ w) (aroma p (R w) ((V w).Y b 0)))) L (𝓝 0) :=by
    have hQ:=(hh.house ht hb hμ 2).2.2.1
    choose B ζ P D hD hF hx hK using hh.tanks
    let Y(w)(a b):= fun x=> (V w).J a b x; have hr w:=hb.trans_le (hμ w|>.1); have hs(w): (stock p (R w) (μ w) (1:Config G (g w))).det≠0:= (hull_m (hr w) le_rfl (hD w) (hF w) (hx w) (hK w)|>.1.det_pos.ne')
    let Z(w):= sailM p (R w) (μ w) (f:=g w); let J(w) a b x:= Z w (Y w a b x); let Ξ(w) b:= Z w ((V w).E b 0); let G'(w) b:= sailM p (R w) (μ w) (aroma p (R w) ((V w).Y b 0))
    have hm(w): Memo (shellB p (R w) (μ w) ∘ input G (g w)) 0:= (gate_shell (hD w) (hr w) (hs w) (Army.powL (v:=id) contDiffAt_id) (input_zero ..)).1
    have hu(w)(a b:Axis): Traverse (J w a b):= traverse_pay (hD w) (hr w) (hs w) _ ((hV w).sound.heart ..) (polish (V w) (h w) _ _)
    have H(t b:Axis): Pico (fun _=>0) (fun w=> Y w t b 0 ∘ input G (g w)) 4:=⟨a/5,C,by positivity,hp,fun w=>pea_loom ((hV w).sound.heart t b 0) ((hV w).J ..) hp ha.le⟩
    have ht(b:Axis): Rose L (fun w=> lux d i q b (G' w b)) (fun w=> -cob d i q (J w b b 0)):=by
       have ht(a):= orb_debit d i b q Tn (hearth_pk (H a b) hQ) (fun w=> hu w a b) a
       have hx:= Rose.sumX univ (F:=fun a w=> lux d i q b (elm a (J w a b) 0)) (fun j _=> ht j)
       have hz:=hearth_hush (V:=fun w=>(V w).E b 0) d i q Tn (show 0<_ from div_pos ha (by norm_num: (0:ℝ)<5)) (fun w=>pea_loom ((hV w).sound.plum b _) ((hV w).E ..) (hε w|>.1) ha.le) (fun i=>(hε i).1) he 1 (fun i=>(hε i).2) zero_le_one b hQ
       refine Rose.chain (Rose.skip (Eventually.of_forall fun w=>?_)) ((Rose.dec hx hz).chain (Rose.skip (Eventually.of_forall fun w=>?_)))
       · let K:= ((∑ a:Axis,elm a ((V w).J a b))-(V w).E b) 0
         change lux _ _ _ _ _= (∑ a:Axis,lux d i q b (elm a (J w a b) 0))-lux d i q b (Ξ w b)
         rw [show lux d i q b (G' w b)=lux d i q b (Z w K) from congr_arg Deb (funext (fun x=> congr_arg (fun p:ℂ=> ((pitchf (g w):ℂ)⁻¹)^(3:ℕ)*p) (clip_eq i q (stiff ((hV w).sound.fin b 0) (hm w)).symm _ _)))]
         unfold K; rw[Pi.sub_apply,Finset.sum_apply]; refine pilots d i q b (fun a=> (V w).J a b) (fun a x=>?_) (hm w) ?_
         · obtain ⟨hb,_⟩:=(hV w).sound.heart a b x;exact hb
         obtain ⟨hx,_⟩:=(hV w).sound.plum b 0;exact hx
       simp only [Pi.sub_apply,Pi.zero_apply,sub_zero]; simp
    have hy:(fun w=> ∑ b:Axis, -cob d i q (J w b b 0))=ᶠ[L] (0:W→ℂ):=by refine Eventually.of_forall fun w=>?_ ; change ∑ b:Axis,-cob d i q (sailM p (R w) (μ w) ((V w).J b b 0)) = 0; rw [sum_neg_distrib,cob_abs d i q (V w) (h w) (hV w).sound (hr w) (hs w) (hD w),neg_zero]
    have hp':= Rose.chain (Rose.sumX univ (fun i _=> ht i)) (Rose.skip hy)
    unfold Rose at hp'; rw [sub_zero] at hp'; exact hp'
end YM.Trace.Lamp
