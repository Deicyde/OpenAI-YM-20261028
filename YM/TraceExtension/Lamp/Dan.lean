import YM.TraceExtension.Lamp.MetaV
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
variable {W:Type*}{g:W→Side}{L:Filter W}{F:∀ w, WildM G (g w) k k}
def ico (p q:Track):Backs 0:= ((0,p),q)
lemma ripple (F:WildM G f k k)(i j:Loc G k)(p q:Cover): carb 0 F i j ![] (ico (pitchf f • reel p) (pitchf f• reel q))= pier (F 0) (wrap f p) (wrap f q) i j:=by
    have he (p:Cover)(i:Loc G k): barca (0: Site f) (pitchf f • reel p) i= relay (wrap f p) i:=by ext1 j; unfold barca; rw[← (reel_roll ..).exp]; unfold relay tune; simp [cell]
    have hv(p: Fin 0→ Phase (Lines G f 1)): art F 0 p=approached (F 0):=by rw [Subsingleton.elim p ![]]; exact art_zero F
    unfold pier carb ico; dsimp only; rw[he p,he q,hv]
-- driver convergence; y compact
lemma carb_cap {p:Fin n→Loc G 1}(i j:Loc G k)(h:Pella (g:=g) (fun _=>0) F n): Honor (fun w=> carb 0 (F w) i j p) m:=by
    obtain ⟨A,C,ha,hC,f⟩:=h.top; refine ⟨_,?_,fun w x=> carb_a i j p ha hC (f w) x⟩; exact mul_nonneg (guardC_n ha) (mul_nonneg (mul_nonneg (guardC_n ha) (ramt_n ha)) hC)
lemma Honor.follows {F:W→X→ℂ}(h:Honor F 1)(x:X) {y:W→X}(he:Tendsto y L (𝓝 x)): Rose L (fun w=> F w (y w)) (fun w=>F w x):=by
    obtain ⟨C,hC,H⟩:=h.top; apply squeeze_zero_norm' (a:=fun w=> C* ‖y w-x‖) ?_ ?_
    · refine Eventually.of_forall fun w=>?_
      apply Convex.norm_image_sub_le_of_norm_fderiv_le (f:=F w) (𝕜:=ℝ) _ _ convex_univ (Set.mem_univ _) (Set.mem_univ _)
      · intro x _; exact ((H w x).analytic).differentiableAt (by simp)
      intro x _; have ht:= (H w x).norm_le 1 le_rfl; rwa[norm_iteratedFDeriv_one] at ht
    simpa using ((he.sub_const x).norm.const_mul C)
-- maybe takes ∞
private lemma hookr (a: Axis)(v:G.ColorIndex): barca (0:Site f) (pitchf f • step a) (mood G a v)=relay (step a) (mood G a v):=by
    ext1 i; unfold barca; rw[←reel_i a,← (reel_roll f (step a)).exp, wrap_step,sub_zero]; rfl
lemma Tempo.via (Q:Tendsto (fun w=>(g w).val) L atTop) (h:∀ w,Tempo (F w))(K:∀ i j x y,Tendsto (fun w=>w0 (F w 0) i j x y) L (𝓝 0))(ht:Pella (g:=g) (fun _=>0) F 1)(i j:Loc G k)(z:Fin 1→Loc G 1): Tendsto (fun w=> carb 0 (F w) i j z (0:Backs 1)) L (𝓝 0):=by
    obtain ⟨a,ha⟩:∃ a,z= ![a]:= ⟨_, show z= ![z 0] from funext fun i=>by fin_cases i; rfl⟩
    subst z; rcases a with ⟨a,v⟩; obtain ⟨a,rfl⟩:= axisEquiv.surjective a
    let t:=pitchf ∘ g; let A:=fun w=>carb 0 (F w) i j (![mood G a v]:Fin 1→_)
    let X:Backs 1:=((![step a],0),0)
    have hv:Tendsto (fun w=> t w • X) L (𝓝 0):=by simpa [t] using (gran Q|>.void).smul_const X
    have he:= carb_cap i j (p:=![mood G a v]) (m:=1) ht
    apply Rose.alight (Rose.side (he.follows 0 hv))
    refine (shock_up Q h K i j a v).congr' (Eventually.of_forall fun w=> ?_)
    let V:= F w; let m:= g w; change xylo V _ _ _ _= A w _
    let P:=t w • X; have hc(p:Loc G k): relay (0:Site m) p=barca (0:Site (g w)) (0:Track) p:=by ext1 i; unfold relay tune barca; simp [axes,mode,cell]
    have he: (![relay (step a:Site (g w)) (mood G a v)] : Fin 1→ Phase (Lines G (g w) 1))=fun k:Fin 1=> barca (0:Site (g w)) (P.1.1 k) (mood G a v):=by
        funext i; fin_cases i; exact (hookr a v).symm
    change relay (0:Site m) i ⬝ᵥ art _ 1 (![relay (step a:Site m) (mood G a v)]) *ᵥ relay 0 j= carb 0 (F w) i j (![mood G a v]) P
    have hx : (![mood G a v]:Fin 1→ _) =fun _ :Fin 1=> mood G a v:=funext fun i=>by fin_cases i;rfl
    rw [carb,hx, hc i,hc j, he,show P.1.2=0 from smul_zero _, show P.2=0 from smul_zero _]

lemma Tempo.pike (Q:Tendsto (fun w=>(g w).val) L atTop)(K:∀ i j x y,Tendsto (fun w=>w0 (F w 0) i j x y) L (𝓝 0))(ht:Pella (g:=g) (fun _=>0) F 0)(i j:Loc G k): Tendsto (fun w=> carb 0 (F w) i j (![]:Fin 0→_) 0) L (𝓝 0)∧Tendsto (fun w=> fderiv ℝ (carb 0 (F w) i j (![]:Fin 0→_)) 0) L (𝓝 0):=by
    let X(w):= carb 0 (F w) i j (![]:Fin 0→_); let U(w):= fderiv ℝ (X w) 0
    have hp(x y:Cover): Tendsto (fun w=>(pitchf (g w):ℂ)⁻¹ * X w (pitchf (g w) • ico (reel x) (reel y))) L (𝓝 0):=by
       apply (K i j x y).congr'; filter_upwards with w; unfold X w0; rw [show pitchf (g w) • ico _ _ = ico (pitchf (g w) • reel x) (pitchf (g w) • reel y) from ?_,ripple]
       unfold ico; exact Prod.ext (Prod.ext (smul_zero _) rfl) rfl
    have hx: Tendsto (fun w=>((pitchf (g w):ℂ)⁻¹)*X w 0) L (𝓝 0):=by have ht:=hp 0 0; simp_rw [reel_home,show ico 0 0=0 from rfl,smul_zero] at ht;exact ht
    have hY:=carb_cap (p:=(![]:Fin 0→_)) (m:=2) i j ht
    have hv:= (gran Q).void; have hh: Tendsto (fun w=> (pitchf (g w):ℂ)) L (𝓝 0):=by exact (Complex.ofRealCLM.continuous.tendsto 0).comp hv
    constructor
    · change Tendsto (fun w=> X w 0) _ _; have he:=hh.mul hx; rw [mul_zero] at he; refine he.congr' (Eventually.of_forall fun w=>mul_inv_cancel_left₀ (by exact_mod_cast (pitch_pos (f:=g w)).ne') _ )
    have ht(p q:Cover) : Tendsto (fun w=> U w (ico (reel p) (reel q))) L (𝓝 0):=by
       let f:= ico (reel p) (reel q)
       have he:= brief (gran Q) X f 1 hY; simp only[sum_range_succ,sum_range_zero, zero_add,pow_one,neap0, neap1,pow_zero,one_mul,mul_add] at he
       have H:= Rose.alight (Rose.side he) (hp p q); have hy:=H.sub hx; rw[sub_zero] at hy; apply hy.congr'; filter_upwards with w; simp only[Function.comp_apply,inv_mul_cancel_left₀ (show ((pitchf (g w)):ℂ)≠0 by exact_mod_cast (pitch_pos (f:=g w)).ne'),add_sub_cancel_left];rfl
    -- evaluation linear form from basis norm ISA lea
    let J : Axis→ Backs 0→L[ℝ]ℝ:=fun i=> ContinuousLinearMap.proj (R:=ℝ) i ∘L (ContinuousLinearMap.snd .. ∘L ContinuousLinearMap.fst ..); let K: Axis→Backs 0→L[ℝ]ℝ:= fun i=> ContinuousLinearMap.proj (R:=ℝ) i ∘L ContinuousLinearMap.snd ..
    have hh(w): U w= (∑ i:Axis,(J i).smulRight (U w (ico (step i) 0))) + (∑ i:Axis,(K i).smulRight (U w (ico 0 (step i)))):=by
       apply ContinuousLinearMap.ext; intro p; rw[_root_.add_apply,_root_.sum_apply,_root_.sum_apply];simp_rw [ContinuousLinearMap.smulRight_apply, ← map_smul (U w),← map_sum, ←map_add]; apply congr_arg; ext1 <;> try rfl
       case fst=> apply Prod.ext (Subsingleton.elim ..); ext1 i; fin_cases i <;> simp [ico,Fin.sum_univ_four,J,K]
       case snd=> ext1 i; fin_cases i <;> simp [ico,Fin.sum_univ_four,J,K]
    have hx(i:Axis):Tendsto (fun w=> U w (ico (step i) 0)) L (𝓝 0):=by have he:= ht (step i) 0; rw[reel_i,reel_home] at he; exact he
    have hz(i:Axis):Tendsto (fun w=> U w (ico 0 (step i))) L (𝓝 0):=by have he:= ht 0 (step i); rw [reel_i,reel_home] at he;exact he
    change Tendsto U L (𝓝 0);rw[funext hh]
    have he:=(tendsto_finsetSum univ (fun i (_:i ∈ univ)=> (show Continuous (fun z:ℂ=> (J i).smulRight z) by fun_prop).continuousAt.tendsto.comp (hx i))).add (tendsto_finsetSum univ (fun i (_:i∈univ)=> (show Continuous (fun z:ℂ=> (K i).smulRight z) by fun_prop).continuousAt.tendsto.comp (hz i)))
    simpa using he
end YM.Trace.Lamp
