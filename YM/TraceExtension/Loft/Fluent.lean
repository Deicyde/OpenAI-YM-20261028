import YM.TraceExtension.Loft.Gondola
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {α W:Type} [Fintype α][DecidableEq α] {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n:ℕ}{σ τ A C D μ ε:ℝ}
variable (d i:Axis)(q:G.ColorIndex)
def ridge (p:Clip)(M:PathData G)(μ:ℝ)(f:Side):= suite fun d i=> yard d i q (marke p M μ∘ input G f)
lemma ridge_down (F:Funds α) (h:(F+μ^2 • 1).det≠0) :
    HasDerivAt (fun v:ℝ=>Real.log (F+(μ+v)^2 • 1).det) ((2*μ)*trace (F+μ^2 • 1)⁻¹) 0:=by
    let U:= fun v:ℝ=> F+(μ+v)^2 • 1; have hp:Memo U 0:=by intro j k; change ContDiffAt ℝ ω (fun v:ℝ=>F j k + ((μ+v)^2)*(1:Funds α) j k) 0; fun_prop
    have he:U 0=F+μ^2 • 1:=by simp[U]
    have hu:(U 0).det ≠ 0:= he ▸ h; have ht : directionM U 0 1=(2*μ) • (1:Funds α):=by
       have hh:HasDerivAt (fun v:ℝ=> (μ+v)^2) (2*μ) 0:=by convert (((hasDerivAt_id' (0:ℝ)).const_add μ).pow 2) using 1 <;> first | rfl | simp
       ext j k; change deriv (fun v:ℝ=> F j k+ ((μ+v)^2)*(1:Funds α) j k) 0=_; exact ((hh.mul_const _).const_add _).deriv
    have hx:=((hp.det_val.log hu).differentiableAt (by simp)).hasDerivAt; rw[deriv,trace_log_first hp hu, ht,he,Matrix.mul_smul,mul_one,trace_smul] at hx; exact hx
lemma ridge_d (hs:M.Bounds p σ C D)(hm:0 < μ)(h:(Det.stock p M μ (1:Config G f)).det ≠ 0): HasDerivAt (fun t:ℝ=> yard d i q (marke p M (μ+t) ∘ input G f)) (-(μ:ℂ)*umbra d i q p M μ f) 0:=by
   let F:=zell p M μ f; let H:=wentG G μ f
   let f' z:= trace (F z); let g' z:=trace (H z); let K:= μ • f' -(2*μ) • g'; let X t:=marke p M (μ+t) ∘ input G f
   have hp: ContDiffAt ℝ ω (uncurry X) 0:=by
       let V(z: ℝ × Link G f):=input G f z.2; let U(z:ℝ× Link G f):=flare p M (V z); let T (z:ℝ×Link G f):=mail (V z); let A(z):=Det.stock p M (μ+z.1) (V z); let P(z):= ammo (μ+z.1) (V z)
       have hw: Army V 0:=Army.powL (v:=Prod.snd) contDiffAt_snd
       have hv: Memo T 0:= memo_flash hm hw|>.1
       have he: Memo U 0:=by
           refine memo_damage _ (F:=fun z=> burn p M (V z)) ?_; exact Work.F02.mainTerm_contDiffAt hs ((Army.powL (v:=Prod.snd) contDiffAt_snd).mul (Army.comp (g:=V) (w:=Prod.fst) hw contDiffAt_fst))
       have hh (k:ℕ): Memo (fun z:ℝ×Link G f => (μ+z.1)^2 • (1:Funds (Lines G f k))) 0:=fun i j=>by
          change ContDiffAt ℝ ω (fun z:ℝ × Link G f=> (μ+z.1)^2*(1:Funds (Lines G f k)) i j) 0; fun_prop
       have hA: Memo A 0:= (he.twice (hv.cross hv.spot)).twice (hh 1); have hB: Memo P 0:= (hv.spot.cross hv).twice (hh 0)
       exact ((hA.det_val.log (show (A 0).det ≠ 0 from by simpa[A,V])).div_const 2).sub (hB.det_val.log (show (P 0).det≠0 by simp only[P,Prod.fst_zero,add_zero];exact (ammo_safe _ hm).det_pos.ne'))
   have hx:=exchange_y d i q (K:=K) hp (show _ =ᶠ[𝓝 0] K from ?_)
   swap
   · have hz:= gate_n hs hm h (Army.powL (G:=G) (n:=f) (v:=id) contDiffAt_id) (input_zero ..)
     filter_upwards [hz] with z hz; let V:=input G f z
     have ht:= ((ridge_down (flare p M V+mail V*(mail V)ᵀ) hz).div_const 2).sub (ridge_down (tonic V) (μ:=μ) (ammo_safe V hm|>.det_pos.ne'))
     change deriv (fun s=>X s z) 0=_; rw[show deriv (fun s=>X s z) 0= _ from ht.deriv]; change 2*μ*trace (F z)/2-2*μ*trace (H z)= μ*trace (F z)-2*μ*trace (H z); ring
   have hv f k (U: WildM G f k k)(h: Memo U 0): ContDiffAt ℝ ω (fun z=>trace (U z)) 0:= ContDiffAt.sum (f:=fun i z=>U z i i) (fun i _=> h i i)
   obtain ⟨ht,hH⟩:=gate_shell hs hm h (Army.powL (v:=id) contDiffAt_id) (input_zero G f)
   have hf:ContDiffAt ℝ ω f' 0:=hv _ _ F ht; have hh:ContDiffAt ℝ ω g' 0:=hv _ _ H hH
   rw[show -(μ:ℂ)*umbra d i q p M μ f=yard d i q K from ?_]; exact hx
   let L(C: Maze G f):= Lamp.cob d i q C
   have he:L K=(μ:ℂ)*L f'- (↑(2*μ:ℝ):ℂ)* L g':=by
      have hh'(x y):clipP i q K x y=(μ:ℂ)*clipP i q f' x y-(↑(2*μ:ℝ):ℂ)*clipP i q g' x y:=by
         unfold K; rw [clip_sub _ _ _ _ (F:=μ • f') (H:=(2*μ) • g') (hf.const_smul μ) (hh.const_smul (2*μ)),clip_smul _ _ _ _ hf,clip_smul _ _ _ _ hh];
      unfold L Lamp.cob; simp only [pani,hh']; ring
   let N:ℂ:=(Fintype.card (Site f):ℂ)⁻¹; change _*( -(N*L f')+2*(N * L g'))=N*L K;rw[he]; push_cast;ring
lemma ridge_deriv (hs:M.Bounds p σ C D)(hm:0 < μ)(h:(Det.stock p M μ (1:Config G f)).det ≠ 0): HasDerivAt (fun t:ℝ=> ridge q p M t f) (-(μ:ℂ)*suite (fun d i=>umbra d i q p M μ f)) μ:=by
    let F(d i:Axis)(t:ℝ):= yard d i q (marke p M t∘ input G f); let V(d i:Axis):=umbra d i q p M μ f
    have ht(d i:Axis): HasDerivAt (F d i) (-(μ:ℂ)*V d i) μ:=by
       have he:=ridge_d d i q hs hm h; let g:=fun t:ℝ=>t-μ
       have hv: HasDerivAt g 1 μ := (hasDerivAt_id _).sub_const _; rw [← show g μ=0 from sub_self _] at he
       have hh:=he.scomp μ hv; rw[one_smul] at hh
       exact hh.congr_of_eventuallyEq (Eventually.of_forall fun x=>by dsimp only[Function.comp_apply,g]; rw[add_sub_cancel])
    have he : HasDerivAt (fun x=> ridge q p M x f) (∑ d,∑ i,(if d=i then 0 else -(μ:ℂ)*V d i)) μ:=by
       refine HasDerivAt.fun_sum (fun d (_:d∈univ)=> HasDerivAt.fun_sum (fun i _=> (show HasDerivAt (fun x=>if d=i then 0 else F d i x) (if d=i then 0 else -(μ:ℂ)*V d i) μ from ?_)))
       by_cases h:d=i
       · simpa only[h,↓reduceIte] using (hasDerivAt_const μ (0:ℂ))
       simp only[h,↓reduceIte];exact ht d i
    rw[show -(μ:ℂ)*suite (fun d i=>umbra d i q p M μ f)= (∑ d,∑ i,(if d=i then 0 else -(μ:ℂ)*V d i)) from ?_]; exact he
    unfold suite; simp only [mul_sum, mul_ite, mul_zero]; rfl
end YM.Trace.Loft
