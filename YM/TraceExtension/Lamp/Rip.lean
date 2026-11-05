import YM.TraceExtension.Lamp.Lock
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} (d i b:Axis)(q:G.ColorIndex)
lemma neap_der (F: ℝ→ℂ)(k:ℕ) : neap k F 0 1=(k.factorial:ℂ)⁻¹* iteratedDeriv k F 0:=by rw [iteratedDeriv_eq_iteratedFDeriv];simp [neap,Complex.real_smul]
lemma neap_prop {F H:X→ℂ}{v:X}(hF:ContDiffAt ℝ ω F 0)(hH:ContDiffAt ℝ ω H 0)(he:F 0=0):
    neap 3 (fun x=> F x*H x) 0 v=neap 1 F 0 v*neap 2 H 0 v+neap 2 F 0 v* neap 1 H 0 v+neap 3 F 0 v*neap 0 H 0 v:=by
    let A(s:ℝ):= (0:X)+s • v
    have hz: A 0=0:=by simp [A]
    let f:=F ∘ A;let g:=H∘ A; rw [← chord_n _ _ 3 (hF.mul hH),←chord_n _ _ 1 hF,← chord_n _ _ 2 hH,← chord_n _ _ 2 hF,← chord_n _ _ 1 hH,← chord_n _ _ 3 hF, ← chord_n _ _ 0 hH]
    have hA: ContDiffAt ℝ ω A 0:=by unfold A; fun_prop
    have hf: ContDiffAt ℝ ω f 0:= (show ContDiffAt ℝ ω F (A 0) from hz.symm ▸ hF).comp _ hA
    have hp: ContDiffAt ℝ ω g 0:= (show ContDiffAt ℝ ω H (A 0) from hz.symm ▸ hH).comp _ hA
    change neap 3 (f*g) 0 1=neap 1 f 0 1 * neap 2 g 0 1+neap 2 f 0 1 * neap 1 g 0 1 + neap 3 f 0 1 * neap 0 g 0 1; simp_rw[neap_der]; rw[iteratedDeriv_mul (hf.of_le le_top) (hp.of_le le_top)]
    have hy: f 0=0:=by rw [show f 0= F (A 0) from rfl,hz,he]
    simp only[Finset.sum_range_succ];norm_num [Nat.factorial,Nat.choose,hy];ring

def Doss(K: Cover)(p:TresF (Fin 2)):= mode (axes (p 0+p 1)) K-1
lemma doss_bill (W:Type*)(K:Cover)(n:ℕ): Honor (fun _ :W=> Doss K) n:=by
    let P:TresF (Fin 2)→L[ℝ] Track:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin 2=> Track) 0 + ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin 2=> Track) 1
    -- pick f so lift valid; otherwise entire directional bound
    obtain ⟨f,hp⟩ : ∃ f:Side,lift (wrap f K)=K:=by
       let f:Side:=⟨2*(Laurent.size K +1),by omega⟩; refine ⟨f,lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩⟩
       have hs :(K i).natAbs≤ Laurent.size K:= single_le_sum (f:=fun i=> (K i).natAbs) (fun i _=>Nat.zero_le _) (mem_univ i); dsimp [f];omega
    let X(y:Track):= mode (axes y) K; let x:=wrap f K
    have he(y): X y=mode (axes y) (lift (x-0)):=by unfold X; rw[sub_zero,show lift x=K from hp]
    have hx: Honor (fun _:W=>X) n:=by
        have ht:=fun y:Track=> sea_mark (k:=n) x y zero_lt_one 0
        refine ⟨_,?_,fun _ y=> (ht y).germ (Eventually.of_forall fun z=>(he z).symm)⟩; positivity
    have hc: Honor (fun _ : W=>fun _:TresF (Fin 2)=> (1:ℂ)) n:=⟨_,zero_le_one,fun _ _=>allows_const _ norm_one.le⟩
    exact (hx.dam P).subc hc
lemma sum_brew (v:Dish): lawn d b v 0+lawn d b v 1=(v.2:ℝ) • step b:=by unfold lawn flee; simp
lemma snack (k:ℕ)(K:Cover)(v:Dish) : neap k (Doss K) 0 (lawn d b v)=(v.2:ℂ)^k * neap k (Doss K) 0 (lawn d b (0,1)):=by
    let A:= lawn d b
    have he(t:ℝ): Doss K (0+t • A v) = Doss K (0 + t • ((v.2:ℝ) • A (0,1))):=by
       unfold Doss;simp only[zero_add,Pi.smul_apply,← smul_add];unfold A;rw [sum_brew,sum_brew];simp
    have hp:ContDiffAt ℝ ω (Doss K) 0:=by obtain ⟨C,hC,h⟩:= (doss_bill Unit K 1).top; exact (h Unit.unit _).analytic
    rw[← chord_n _ _ _ hp,show (fun s:ℝ=> Doss K (0+s • lawn d b v))=_ from funext he,chord_n 0 _ k hp, neap_tide, Complex.real_smul]; push_cast; rfl
lemma stamp_slope (K:Cover): neap 1 (Doss K) 0 (lawn d b (0,1))=Complex.I * K b:=by
    let A:=lawn d b (0,1)
    have hp: ContDiffAt ℝ ω (Doss K) 0:=by obtain ⟨C,hC,h⟩:= (doss_bill Unit K 1).top; exact (h Unit.unit _).analytic
    rw[← chord_n 0 A 1 hp,neap_der]; simp only [Nat.factorial_one,Nat.cast_one,_root_.inv_one,one_mul,iteratedDeriv_one]
    let V(t:ℝ):= Complex.I* (t:ℂ)*(K b); let F(t:ℝ):= Doss K (0+t • A); have hv : F=fun t=> Complex.exp (V t)-1:=by
       funext t; unfold F Doss V; simp only [zero_add,Pi.smul_apply, ← smul_add, A,sum_brew]; simp only[  show (((0,1):Dish).snd:ℝ)=1 by norm_num, one_smul]; simp [mode,axes, mul_ite,apply_ite Complex.ofReal,ite_mul,mul_assoc]
    change deriv F _=_; rw [hv]; let X:= (fun t=> Complex.exp (V t)); have hx:HasDerivAt V (Complex.I*(K b:ℂ)) 0:=by unfold V; simpa using! (((Complex.ofRealCLM.hasDerivAt (x:=0)).const_mul Complex.I).mul_const (K b:ℂ))
    apply HasDerivAt.deriv; simpa only[V,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_mul] using hx.cexp.sub_const 1
lemma dolce (K:Cover){F:TresF (Fin 2)→ℂ}(h:ContDiffAt ℝ ω F 0) :
    Deb (fun a:Dish=> neap 3 (fun p=> Doss K p * F p) 0 (lawn d b a))= -(K b:ℂ)*neap 2 F 0 (![step d,-step d]) :=by
    have hp:ContDiffAt ℝ ω (Doss K) 0:=by obtain ⟨C,hC,h⟩:= (doss_bill Unit K 1).top; exact (h Unit.unit _).analytic
    have hx: Doss K 0=0:=by simp [Doss,axes, mode]
    let U a:=neap 3 (fun p=>Doss K p*F p) 0 (lawn d b a)
    have ht (x:ℤ): FlopZ (fun y=> U (x,y))=(neap 1 (Doss K) 0 (lawn d b (0,1))) * ((x:ℂ)^2 * neap 2 F 0 (![step d,-step d])):=by
       let N:=fun i=> neap i (Doss K) 0 (lawn d b (0,1)); have hu(a:Dish) : U a= (a.2:ℂ)^ (1:ℕ)* N 1*neap 2 F 0 (lawn d b a) +(a.2:ℂ)^ (2:ℕ) *N 2 * neap 1 F 0 (lawn d b a)+(a.2:ℂ)^ (3:ℕ)*N 3* neap 0 F 0 (lawn d b a):=by unfold U; rw [neap_prop hp h hx, snack d b 1 K a, snack d b 2 K a,snack d b 3 K a]
       rw [flopi]; simp only [hu,lawn,flee_run, neap1,neap2,neap0,map_add,map_smul,_root_.add_apply,_root_.smul_apply,Complex.real_smul]; unfold N; simp only [lawn,flee_run, neap1,neap2,map_add,map_smul,_root_.add_apply,_root_.smul_apply,Complex.real_smul]; push_cast; ring
    change Complex.I*PanZ (fun x:ℤ=> FlopZ (fun y=> U (x,y)))=_; rw [pani];simp_rw [ht]; rw[stamp_slope]; push_cast; ring_nf; simp
lemma doss_l (K:Cover)(x:Dish) :
    cell (wrap f (ra d x.1)+wrap f (reab d b x)) (wrap f K)-1=Doss K (pitchf f • lawn d b x):=by
    unfold Doss; rw[reeling,cell_wrap, rolls.exp (rolls.combine (reel_roll f (ra d x.1)) (reel_roll f (reab d b x)))]; congr 2; ext k; simp[axes]
lemma ride_l (Q:Tendsto (fun w=>(g w).val) L atTop) (F:∀ w,Maze G (g w))(h:Pico (fun _=>0) F 2)(K:Cover):
    Rose L (fun w=> lux d i q b (F w ∘ rideC (wrap (g w) K) - F w)) (fun w=> -(K b:ℂ)*cob d i q (F w)):=by
    let V w:= molt 0 ![mood G i q,mood G i q] (F w); let t:=pitchf ∘ g
    let T (w:W)(x):=Doss K x*V w x
    let A:TresF (Fin 2):= ![step d,-step d]; let X:TresF (Fin 2):= ![0,step b];
    have hs:=joined i q F h (n:=4)
    have hp:Honor T 4:=Honor.prod (ContinuousLinearMap.mul ℝ ℂ) (doss_bill W K 4) hs
    have he:=disk_brief (gran Q) T A X hp; have hh:= roseRate (-(K b:ℂ)) (cog_neap d i q Q F h |>.side)
    obtain ⟨a,ha,Hv⟩:=hs.top; obtain ⟨b',C,hb,hC,hV⟩:=h.top
    have hx(w:W) (x:Dish) : T w (t w • lawn d b x)= cue d i q b (F w ∘ rideC (wrap (g w) K)-F w) x:=by
       unfold T V t; rw[Function.comp_apply, ← cue_at,← doss_l]; unfold cue; let V:= rideC (n:=g w) (G:=G) (wrap (g w) K)
       have ht: ContDiffAt ℝ ω (F w) 0:= (hV w).1
       rw[clip_sub i q _ _ (show ContDiffAt ℝ ω (F w ∘ V) 0 from ContDiffAt.comp 0 (g:=F w) ((map_zero V).symm ▸ ht) V.contDiff.contDiffAt) ht,clip_rot i q _ _ _ ht]; ring
    apply Rose.chain _ (he.chain (Rose.chain _ hh))
    · apply Rose.skip (Eventually.of_forall fun x=>?_); dsimp only
      unfold lux; simp_rw [← hx,lawn,flee_run]; rfl
    apply Rose.skip (Eventually.of_forall fun x=>?_); dsimp only; have ht:=dolce d b K (F:=V x) ((Hv x 0).analytic); simp_rw[lawn,flee_run] at ht; exact ht
end YM.Trace.Lamp
