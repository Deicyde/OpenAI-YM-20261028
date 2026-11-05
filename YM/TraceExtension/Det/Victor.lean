import YM.TraceExtension.Det.Clove
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{Y:Gal G f}{α C D μ:ℝ}
    {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T][FiniteDimensional ℝ T][CompleteSpace T]
    {V:T → Config G f}{k:T → Coats G f}

omit [FiniteDimensional ℝ T] [CompleteSpace T] in
lemma gate_n (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det≠0)(hv:Army V 0)(hp:V 0=1):
    ∀ᶠ z in 𝓝 0,(stock p R μ (V z)).det ≠0:=by
    let F(z):= (stock p R μ (V z)).det; have hx: ContDiffAt ℝ ω F 0:=(stocked h hμ V hv).1.det_val
    exact hx.continuousAt.eventually_ne (by unfold F; rw[hp];exact he)
omit [FiniteDimensional ℝ T] [CompleteSpace T] in
lemma gate_shell (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det≠0)(hv:Army V 0)(hp:V 0=1): Memo (shellB p R μ ∘ V) 0 ∧ Memo (shellG μ ∘ V) 0:=
    ⟨(stocked h hμ V hv).1.flip (by simp [Function.comp_apply,hp,he]), (stocked h hμ V hv).2.flip (ammo_safe _ hμ).det_pos.ne'⟩
lemma tape_w (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det≠0)(hY:Cloaked Y)(hv:Army V 0)(hp:V 0=1): ContDiffAt ℝ ω (ashore p R μ Y ∘ V) 0:=by
    obtain ⟨hh,hq⟩:=gate_shell h hμ he hv hp
    have hT:=memo_t hY V hv hp
    let P(x):=shoreM p R μ Y (V x); have hw : Memo P 0:= Memo.cross (Memo.cross (hq.cross (memo_flash hμ hv |>.1.spot)) (hT.twice hT.spot)) hh
    have hb: ContDiffAt ℝ ω (fun z=> shoreX p R μ Y (V z)) 0:=by unfold shoreX trapw; exact ContDiffAt.sum fun i _=> ContDiffAt.sum fun j _=> (hh j i).smul (memo_y hY V hv hp i j)
    have hQ: ContDiffAt ℝ ω (fun z=> shoreZ p R μ Y (V z)) 0:=by
       unfold shoreZ trapw; apply ContDiffAt.sum; intro i _; apply ContDiffAt.sum; intro j _; apply (hw j i).smul
       let p(z: BaseSites G f× (T × Link G f)):= lyric (V z.2.1) z.1 z.2.2
       let F (u:BaseSites G f)(z:T× Link G f):= lull (V z.1) u z.2
       have hm: Army p 0:=by
           let A(z:BaseSites G f × (T×Link G f)):= V z.2.1
           have hx : Army A 0:= Army.comp (g:=V) (w:=fun z:BaseSites G f × (T × Link G f)=> z.2.1) hv contDiffAt_snd.fst
           exact ((Army.powG (v:=Prod.fst) contDiffAt_fst).slant ((Army.powL (v:=fun z:BaseSites G f × (T × Link G f)=> z.2.2) contDiffAt_snd.snd).mul hx)).mul hx.inv
       have he: p 0=1:=by change lyric _ 0 0=1; rw [lyric_axis,input_zero]
       have hr : ContDiffAt ℝ ω (uncurry F) 0:= hm.logL he
       have hf:= Work.F05.curve_partial (F:=fun z:T=> juke (V z) ((pocket _) j)) (keep_l hr _)
       exact (hf.comp (f:=fun z:T=> (z,(0:Link G f))) _ (by fun_prop)).clm_apply (g:=fun _=> (pocket _) i) contDiffAt_const
    exact (hb.const_smul (1/2:ℝ)).sub hQ
lemma accord_n (hY:Cloaked Y)(hv:Army V 0)(hp:V 0=1)(ht:Army k 0){u:G.El}(hh:k 0=(fun _=>u)): ∀ᶠ z in 𝓝 0,accord Y (k z) (V z):=by
    let Q(x:Link G f×T):= input G f x.1*V x.2; let P(x:Link G f×T):= k x.2
    exact el_slice (hY.jacket (Link G f × T) Q P u ((Army.powL (v:=Prod.fst) contDiffAt_fst).mul (Army.comp (g:=V) (w:=Prod.snd) hv contDiffAt_snd)) (by unfold Q; simp[hp]) (Army.comp (g:=k) (w:=Prod.snd) ht contDiffAt_snd) hh)
lemma cloak_shore (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det≠0)(hY:Cloaked Y): Cloaked (ashore p R μ Y):=by
    refine ⟨tape_w h hμ he hY (Army.powL (v:=id) contDiffAt_id) (input_zero G f),?_⟩
    intro X _ _ _ _ V k u hv hh ht hy
    let U(z):= Lattice.gauge (k z) (V z); have hx: U 0=1:=by unfold U;rw[hy,hh];exact strip_roots _
    filter_upwards[gate_n h hμ he hv hh, accord_n hY hv hh ht hy, tune_n hY V hv hh,tune_n hY U (ht.slant hv) hx] with x hw hf hr ha
    have hp:=swapping (V x) (k x) h hμ hw hr ha hf
    unfold ashore; rw [hp.reef,hp.reed,map_sub,map_smul]
lemma dyed_mark (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det ≠0): Cleric (marke (f:=f) p R μ):=by
    refine ⟨?_,fun T _ _ _ _ V k u _ _ _ _=> Eventually.of_forall fun x=> marke_cov (V x) (k x) μ h⟩
    rw[show marke p R μ ∘ input G f=bal 1 (marke p R μ) from funext (fun v=>by simp[bal])];exact memo_mkr _ h hμ he
lemma dyed_lush (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det≠0)(hY:Cloaked Y): Cleric (lush Y):=by
    refine ⟨?_,?_⟩
    · exact ContDiffAt.sum (fun i _=> memo_t hY (input G f) (Army.powL (v:=id) contDiffAt_id) (input_zero G f) i i)
    intro T _ _ _ _ V k u hv h0 ht hp
    let U(z):= Lattice.gauge (k z) (V z); have hx: U 0=1:=by unfold U;rw[hp,h0];exact strip_roots _
    filter_upwards [gate_n h hμ he hv h0,accord_n hY hv h0 ht hp,tune_n hY V hv h0,tune_n hY U (ht.slant hv) hx] with x he hh h₁ h₂
    let P:=trench (k x); have ht:=trench_orthogonal (k x); change (tidal Y (U x)).trace=(tidal Y (V x)).trace; rw [show tidal Y (U x)=_ from ht.carry ((swapping _ _ h hμ he h₁ h₂ hh).armV),Matrix.trace_mul_comm _ _ ,← Matrix.mul_assoc,ht.right,one_mul]
lemma gauge_fleur (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det≠0)(hY:Cloaked Y) (hv:Army V 0)(hp:V 0=1):
    ∀ᶠ z in 𝓝 0, (shellB p R μ (V z)*beamH (aroma p R Y) (V z)).trace/2 - lush Y (V z) =arrived p R μ Y (V z)-μ^2*(shellB p R μ (V z)*tidal Y (V z)).trace + aroma p R (ashore p R μ Y) (V z):=by
    filter_upwards [gate_n h hμ he hv hp,tune_n hY V hv hp,meet_mail_n V hv hp hY] with x hv ht hh; exact scale_g _ h hμ hv ht hh
end YM.Trace.Det
