import YM.TraceExtension.Loft.Peak

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} (d i:Axis)(q:G.ColorIndex)
variable {V:∀ w,Peat G (g w)} {R:W→PathData G}{μ:W→ℝ}
variable {F H: Maze G f}
lemma cob_plus (h:ContDiffAt ℝ ω F 0)(p:ContDiffAt ℝ ω H 0) : cob d i q (F+H)= cob d i q F+cob d i q H:=by unfold cob; simp only [pani]; simp_rw[clip_add i q _ _ h p]; ring
lemma cob_s (h:ContDiffAt ℝ ω F 0)(p:ContDiffAt ℝ ω H 0) : cob d i q (F-H)=cob d i q F-cob d i q H:=by unfold cob; simp only [pani]; simp_rw [clip_sub i q _ _ h p];ring
lemma cob_c (t:ℝ)(h:ContDiffAt ℝ ω F 0):cob d i q (t • F)=(t:ℂ)*cob d i q F:=by unfold cob; simp only[pani]; simp_rw[clip_smul i q _ _ h t];ring
lemma pet_snug {E:W→ℝ}(Tn:Tendsto (fun w=>(g w).val) L atTop) (w:∀ v, Maze G (g v))(ha:0<a)(h:∀ z, Pet Prod.fst (0:Site (g z)) (w z) a (E z) 2)(hp:∀ z,0≤E z)(p:Tendsto E L (𝓝 0))(M':ℝ)(he:∀ z,E z≤M')(hM:0≤ M'): Rose L (fun z=> cob d i q (w z)) 0:=by
    refine Rose.chain (cog_neap d i q Tn w (show Pico _ _ _ from ⟨a,M',ha,hM,fun z=> (h z).tilt (he z) le_rfl le_rfl⟩)) ?_
    unfold Rose; rw[sub_zero]
    let t:TresF (Fin 2):=![step d,-step d]; let f z := ((2:ℕ).factorial:ℝ)⁻¹ * (ramt 2 (Fin 2) a* E z)* ‖t‖^ (2:ℕ)
    refine squeeze_zero_norm' ?_ (show Tendsto f L (𝓝 0) from ?_)
    · exact Eventually.of_forall fun z=> norm_neap (p:=t) (malt (h z) ha (hp z) _ 0 2) le_rfl
    unfold f; simpa using (((p.const_mul (ramt 2 (Fin 2) a)).const_mul (((2:ℕ).factorial:ℝ)⁻¹)).mul_const (‖t‖^(2:ℕ)))
lemma heap_low {E:W→ℝ}(Tn:Tendsto (fun w=>(g w).val) L atTop) (ha:0<a)(h:∀ z,Pet Prod.fst (0:Site (g z)) (V z∘ input G (g z)) a (E z) 4) (hp:∀ z,0≤ E z) (p':Tendsto E L (𝓝 0))(M':ℝ)(he:∀ z,E z≤M')(hM:0≤M') (hw:Parked (fun w=>shellB p (R w) (μ w) ∘ input G (g w)) 2): Rose L (fun z=> cob d i q (sailM p (R z) (μ z) (V z))) 0:=by
    obtain ⟨T,hT,H⟩:= beamer G 2
    obtain ⟨η,C,hη,hC,g'⟩:= hw.spins.top
    let v:= min (a/(2+2+1:ℝ)) η; have hv:0<v:=lt_min (by positivity) hη
    let u:=v/((↑(2:ℕ):ℝ)+2);have hu:0<u:=by unfold u; positivity
    let D:ℝ:= (Fintype.card (Loc G 1):ℝ)*countCost u; have hD:0≤D:=mul_nonneg (by positivity) (count_pos hu).le
    let U(t:ℝ):=((2:ℝ)^(2:ℕ)*‖ContinuousLinearMap.mul ℝ ℝ‖*(T*t)*C*D)*D; have hx(t)(ht:0≤t):0≤U t:=by unfold U; positivity
    apply pet_snug d i q Tn (a:=u) (fun z=>sailM p (R z) (μ z) (V z)) hu (E:=U∘ E) _ (fun z=>hx _ (hp z)) ?_ (U M') _ (hx _ hM)
    · intro z; let Z:=shellB p (R z) (μ z)∘ input G (g z); let F:=beamH (V z) ∘ input G (g z)
      have he : PetW (0:Site (g z)) (fun q=>F q) v (T*E z) 2:=by
         have hp' := H _ _ _ _ _ ha.le (hp z) (h z); refine hp'.tiny ?_ (mul_nonneg hT (hp z)) le_rfl le_rfl; exact (min_le_left ..)
      have hz:= (he.spotV.cross_r ((g' z).tiny (show v≤η from min_le_right ..) hC le_rfl le_rfl) hv (mul_nonneg hT (hp z)) hC).spotV; have hh:= hz.grade hu (by change 0 ≤ (2:ℝ)^(2:ℕ)*_*_*_*D; have ht:=hp z; positivity)
      simp_rw [transpose_mul,transpose_transpose] at hh; rw [mul_assoc _ (Fintype.card _:ℝ) (countCost _)] at hh; exact hh
    · have hv : Continuous U:=by unfold U; fun_prop
      have hz: U 0=0:=by simp [U]
      exact (show Tendsto U (𝓝 0) (𝓝 0) from by simpa only [hz] using hv.tendsto 0).comp p'
    intro z; change U (E z) ≤ U M'; unfold U;
    gcongr; exact he z
-- ∆ response actually sampled on torus
lemma pilB (d i:Axis)(q:G.ColorIndex){Z: Peat G f}{μ:ℝ}(A:Axis→Site f→Peat G f)(h:∀ a x, Cleric (A a x))(he:Memo (shellB p M μ ∘ input G f) 0)(hp: Cleric Z):
    cob d i q (sailM p M μ ((∑ a, elm a (A a) 0)-Z))= (∑ a, cob d i q (elm a (fun x=> sailM p M μ (A a x)) 0))-cob d i q (sailM p M μ Z):=by
    let J(a):= elm a (A a) 0
    have hh(a):Cleric (J a):= elm_cleric (A a) a (h a) _
    have hf: Cleric (∑ i,J i):= (clergy G f).sum_mem (fun i _=>hh i)
    let X:= ∑ i,J i
    change cob d i q (sailM p M μ ((∑ i,J i)-Z))=_; rw[cob_near d i q (arm_sail_s hf hp),cob_s d i q (hearth_s hf he) (hearth_s hp he)]; congr 1
    rw[cob_near d i q (arm_sail_t (p:=p) _ (fun i _=> hh i)), cob_total d i q (fun i=>hearth_s (hh i) he)]; exact sum_congr rfl fun a _=> cob_near _ _ _ (arm_sail_e (A a) a (h a) _)
lemma col_cut (V:Site f→ Maze G f)(h:Traverse V)(a:Axis): cob d i q (elm a V 0)=0:=by
   let S(j:Fin 4):Cover:= Pull.steps j • step a
   have hx: elm a V 0= ∑ j:Fin 4, (Pull.cash j) • (V (wrap f (S j))-V (wrap f (-S j))):=by
       unfold elm Pull.dTap; refine sum_congr rfl fun j _=> ?_; unfold S; rw[map_neg,map_nsmul,wrap_step]; simp
   rw[hx,cob_total d i q (F:=fun j=> Pull.cash j • (V (wrap f (S j))- V (wrap f (-S j)))) (fun v=> (show ContDiffAt ℝ ω _ _ from (((h.team (wrap f (S v))).sub (h.team (wrap f (- S v))))|>.const_smul (Pull.cash v))))]; apply sum_eq_zero fun j _=>?_ ; rw [cob_c d i q (Pull.cash j) (F:= V (wrap f (S j))- V (wrap f (-S j))) ((h.team _).sub (h.team _)), cob_s _ _ _ (h.team _) (h.team _), cob_in d i q h _, cob_in d i q h (wrap f (-S j))]; simp
variable (Tn:Tendsto (fun w=>(g w).val) L atTop){ZZ:∀ w,Dart G (g w)}{R:W→PathData G}{μ ε:W→ℝ}
include Tn
lemma vanish_cob (b':Axis) (hV: ∀ w, Viz (ZZ w) p (R w) a (fun _=> C) (fun _=> ε w) (ε w))(h:∀ w,Dart.March (ZZ w))(he:Tendsto ε L (𝓝 0))(hε:∀ w,0≤ε w∧ε w≤1)(hh:Flare g R p α A)(ht:0 < α)(ha:0<a)(hp:0≤ C)(hb:0<b)(hμ:∀ w, b ≤ μ w ∧ μ w≤c):
    Tendsto (fun w=>cob d i q (sailM p (R w) (μ w) (aroma p (R w) ((ZZ w).Y b' 0)))) L (𝓝 0) :=by
    have hQ:=(hh.house ht hb hμ 2).2.2.1
    choose B ζ P D hD hF hx hK using hh.tanks
    let Y(w)(a b):= fun x=> (ZZ w).J a b x; have hr w:=hb.trans_le (hμ w|>.1); have hs(w): (stock p (R w) (μ w) (1:Config G (g w))).det≠0:= (hull_m (hr w) le_rfl (hD w) (hF w) (hx w) (hK w)|>.1.det_pos.ne')
    let Z(w):= sailM p (R w) (μ w) (f:=g w); let J(w) a b x:= Z w (Y w a b x); let Ξ(w) b:= Z w ((ZZ w).E b 0); let G'(w) b:= sailM p (R w) (μ w) (aroma p (R w) ((ZZ w).Y b 0))
    have hm(w): Memo (shellB p (R w) (μ w) ∘ input G (g w)) 0:= (gate_shell (hD w) (hr w) (hs w) (Army.powL (v:=id) contDiffAt_id) (input_zero ..)).1
    have hu(w)(a b:Axis): Traverse (J w a b):= traverse_pay (hD w) (hr w) (hs w) _ ((hV w).sound.heart ..) (polish (ZZ w) (h w) _ _)
    let t:TresF (Fin 2):=![step d,-step d]
    have HE:= heap_low (p:=p) (V:=fun w=>(ZZ w).E b' 0) d i q Tn (show 0<a/5 from div_pos ha (by norm_num)) (fun w=> pea_loom ((hV w).sound.plum b' _) ((hV w).E ..) (hε w|>.1) ha.le) (fun i=>(hε i).1) he 1 (fun i=>(hε i).2) zero_le_one hQ
    unfold Rose at HE; rw[sub_zero] at HE; refine (show Tendsto (fun w=> -cob d i q (Ξ w b')) L (𝓝 0) from by have h:=HE.neg; rw[neg_zero] at h;exact h).congr' ?_
    filter_upwards with w
    let K:= ((∑ a:Axis,elm a ((ZZ w).J a b'))-(ZZ w).E b') 0; symm
    change cob d i q (G' w b')=_
    rw[show cob d i q (G' w b')=cob d i q (Z w K) from congr_arg PanZ (funext fun x=> congr_arg (fun p:ℂ=> ((pitchf (g w):ℂ)⁻¹)^ (2:ℕ)*p) (clip_eq i q (stiff ((hV w).sound.fin b' 0) (hm w)).symm _ _))]
    simp only [K, Pi.sub_apply, Finset.sum_apply]; rw[pilB d i q (fun a x=> (ZZ w).J a b' x) (fun a x=> (hV w|>.sound.heart a b' x).1) (hm w) ((hV w|>.sound.plum b' 0).1)]; change (∑ a,cob d i q (elm a (J w a b') 0))- cob d i q (Ξ w b')= _; simp_rw [show ∀ a:Axis,cob d i q (elm a (J w a b') 0)=0 from fun a=>col_cut d i q _ (hu w a b') a]; simp
end YM.Trace.Lamp
