import YM.TraceExtension.Lamp.Silo
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W}
lemma Rose.alight {X:Type}[NormedAddCommGroup X]{F H:W→X}{m:X}(h:Rose L F H)(he:Tendsto H L (𝓝 m)):Tendsto F L (𝓝 m):=by
    have ht:Tendsto ((F-H)+H) L (𝓝 (0+m)):= h.add he; rwa[sub_add_cancel,zero_add] at ht
lemma whirl_fee (f:W→ℂ)(L: Ultrafilter W)(h:DashQ L f):∃ x,Tendsto f L (𝓝 x) :=by
    obtain ⟨A,ha,hp⟩:=h
    have ht:(↑(Ultrafilter.map f L): Filter ℂ)≤𝓟 (Metric.closedBall 0 A):=by
       rw[le_principal_iff]; change Metric.closedBall 0 A∈ Filter.map f ↑L; rw[Filter.mem_map]; refine hp.mono (fun i hi=>?_); exact Metric.mem_closedBall.mpr ((by simpa only[dist_zero_right] using hi))
    obtain ⟨x,hx,h⟩:=(isCompact_closedBall (0:ℂ) A).ultrafilter_le_nhds _ ht;exact ⟨x,h⟩
lemma base0kill {F:W→ X→ℂ}{t:W→ℝ}(hp:Wilt L t) (p:X)(h:Honor F 3)(hv:∀ k∈({1,2,3} : Finset ℕ), ∀ᶠ w in L, F w (t w • ((k:ℝ) • p))=0) :
    Tendsto (fun w=> (t w:ℂ)⁻¹^(2:ℕ)* F w 0) L (𝓝 0):=by
    let A k x:=(t x:ℂ)⁻¹ ^ (2:ℕ) *∑ i ∈ range (2+1), (t x:ℂ)^i * neap i (F x) 0 ((k:ℝ) • p)
    have hh(k:ℕ)(hk:k∈({1,2,3}:Finset ℕ)): Tendsto (A k) L (𝓝 0):=by
        apply Rose.alight (Rose.side (brief hp F ((k:ℝ) • p) 2 h)); apply tendsto_const_nhds.congr'; filter_upwards [hv k hk] with x hx; rw [hx,mul_zero]
    have he := (((hh 1 (by decide)).const_mul (3:ℂ)).sub ((hh 2 (by decide)).const_mul (3:ℂ))).add (hh 3 (by decide))
    rw[mul_zero,sub_self,zero_add] at he; apply he.congr'; filter_upwards with x
    unfold A; simp only [sum_range_succ,neap_tide,sum_range_zero,neap0, Complex.real_smul]; push_cast; ring
lemma pin_zero {F:W→ X→ℂ}{t:W→ℝ}(hp: Wilt L t)(p:X)(h:Honor F 2)(hv:∀ k∈ ({1,2}:Finset ℕ),∀ᶠ w in L,F w (t w • ((k:ℝ) • p))=0): Tendsto (fun w=> (t w:ℂ)⁻¹*F w 0) L (𝓝 0):=by
    let A k x:=(t x:ℂ)⁻¹^ (1:ℕ)*∑ i∈range (1+1), (t x:ℂ)^i * neap i (F x) 0 ((k:ℝ) • p)
    have hh(k:ℕ)(hk:k∈({1,2}:Finset ℕ)): Tendsto (A k) L (𝓝 0):=by
       apply Rose.alight (Rose.side (brief hp F ((k:ℝ) • p) 1 h)); apply tendsto_const_nhds.congr';filter_upwards[hv k hk] with x hx;rw [hx,mul_zero]
    have he:= ((hh 1 (by decide)).const_mul 2).sub (hh 2 (by decide)); rw [mul_zero, sub_zero] at he; apply he.congr'; filter_upwards with x; unfold A; simp only[sum_range_succ, sum_range_zero,neap_tide,neap0,Complex.real_smul];push_cast; ring
lemma split_first {F: W→ X→ℂ}{t:W→ℝ}{p:X}{u:ℂ}(hp:Wilt L t)(h:Honor F 2)(ht:Tendsto (fun w=> (t w:ℂ)⁻¹*F w 0) L (𝓝 0))(hx:Tendsto (fun w=> fderiv ℝ (F w) 0 p) L (𝓝 u)) : Tendsto (fun w=> (t w:ℂ)⁻¹*F w (t w • p)) L (𝓝 u):=by
    have hh:= brief hp F p 1 h; simp only [pow_one, sum_range_succ, Finset.sum_range_zero,zero_add,neap0,neap1,pow_zero,one_mul,mul_add] at hh
    apply Rose.alight hh; have he:= ht.add hx; rw [zero_add] at he; apply he.congr'; filter_upwards with i; rw [inv_mul_cancel_left₀ (show (t i:ℂ)≠0 by exact_mod_cast (hp.pos i|>.ne'))]

-- exact symmetric interpolation; no branch sign origin needed. coefficient K may be complex.
lemma dual_even {F:W→ X→ℂ}{t:W→ℝ}{p:X}{u:ℂ}(hp: Wilt L t)(h:Honor F 3)(hh:Tendsto (fun w=> (t w:ℂ)⁻¹ ^ (2:ℕ)*F w 0) L (𝓝 0))(hx:Tendsto (fun w=> neap 2 (F w) 0 p) L (𝓝 u)) (ρ:W→ ℂ)(hV:Tendsto ρ L (𝓝 1))(hT:∀ w, F w (t w • -p)=ρ w* F w (t w • p)):
    Tendsto (fun w=> (t w:ℂ)⁻¹ ^(2:ℕ)*F w (t w • p)) L (𝓝 u):=by
    let A(w):=(t w:ℂ)⁻¹ ^ (2:ℕ); let X(w):=F w (t w • p); let Y(w):=F w 0
    have he:= Rose.alight (pan_brief hp F p h) hx
    have hw : Tendsto (fun w=> A w*X w*((1+ρ w)/2)) L (𝓝 u):=by
        have hv:= he.add hh; rw[add_zero] at hv; apply hv.congr'; refine Eventually.of_forall fun x=>?_
        dsimp only; rw[pani]; simp only[Int.cast_zero, Int.cast_one,Int.cast_neg,one_smul,neg_smul,zero_smul,smul_zero,hT]; unfold A X; ring
    have hv:Tendsto (fun w=> (1+ρ w)/2) L (𝓝 1):=by convert (hV.const_add _).div_const _ using 1; norm_num
    have ht:=hw.div hv one_ne_zero; rw[div_one] at ht; apply ht.congr'; filter_upwards [hv.eventually_ne (show (1:ℂ)≠0 from one_ne_zero)] with w hz; exact mul_div_cancel_right₀ _ hz

variable (J: Tendsto (fun w=> (g w).val) L atTop)
include J
lemma roll_l (Z:Cover)(x:Cover): Tendsto (fun w=> cell (wrap (g w) Z) (wrap (g w) x)) L (𝓝 1):=by
    have hp:= (gran J).void.smul_const (reel Z)
    let f:=fun z:Track=>mode (axes z) x
    have hf: ContDiffAt ℝ ω f 0:= ((Firm.mode x zero_lt_one).analytic_real 0).contDiffAt
    have hv:f 0=1:=by simp [f,mode,axes]
    rw [zero_smul] at hp; have he:=hf.continuousAt.tendsto.comp hp
    rw [hv] at he; refine he.congr' ?_
    filter_upwards with z; rw[cell_wrap]; exact ((reel_roll ..).exp x).symm
lemma roll_hit (i:Axis)(q:Cover): Tendsto (fun w=>(pitchf (g w):ℂ)⁻¹*(1-cell (wrap (g w) q) (step i))) L (𝓝 (-Complex.I*(q i))):=by
    let t:= pitchf ∘ g
    let A(x:ℝ):=1-Complex.exp (Complex.I*(x:ℂ)*(q i:ℂ))
    have ht(x:W): 1-cell (wrap (g x) q) (step i)=A (t x):=by
        unfold A t; rw [← wrap_step, cell_wrap, rolls.exp (reel_roll _ q)]; simp [reel,axes,mode,mul_ite,mul_assoc]
    have hv: HasDerivAt A (-Complex.I*(q i)) 0:=by
        have hp: HasDerivAt (fun x:ℝ=> Complex.I*(x:ℂ)*(q i:ℂ)) (Complex.I*(q i)) 0:=by simpa using! (((Complex.ofRealCLM.hasDerivAt (x:=0)).const_mul Complex.I).mul_const (q i:ℂ))
        simpa only [Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_mul, ← neg_mul] using (hp.cexp.const_sub 1)
    have hh:= hasDerivAt_iff_tendsto_slope.mp hv
    have hz:= hh.comp (show Tendsto t L (𝓝[≠] 0) from tendsto_nhdsWithin_iff.mpr ⟨(gran J).void,Eventually.of_forall fun i=> (gran J|>.pos i|>.ne')⟩)
    simp_rw[ht]
    apply hz.congr'
    filter_upwards with z; change slope _ _ _ = _; simp [slope, A,Complex.real_smul, t]
end YM.Trace.Lamp
