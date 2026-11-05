import YM.TraceExtension.Det.Lull

/-!
# Real finite Ward identity with simple mass, on LEFT chart. Carries S' contact through both determinants.
  No trying to invert singular spin in charged term.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff

section charge
variable {ι κ:Type}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
variable (H V : Funds ι) (M T:Matrix ι κ ℝ)(u:ℝ)
lemma move_r {A R:Funds ι}{G J:Funds κ}(h:H*M=-T)(hp:A=H+M*Mᵀ+u • 1)(hk:G=Mᵀ*M+u • 1)(hr:R*A=1)(hg:G*J=1): R*M=M*J+ R*T*J:=by
    have ht : A*M=M*G-T:=by rw [hp,hk,Matrix.add_mul, Matrix.add_mul, h,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_one, Matrix.mul_assoc]; abel
    have hu : R*M*G= M+R*T:=by
       have hz : M=R*(M*G-T):=by rw[← ht,← Matrix.mul_assoc,hr,Matrix.one_mul]
       conv_rhs=>lhs;rw[hz]
       rw [Matrix.mul_sub,← Matrix.mul_assoc,sub_add_cancel]
    rw[show R*M=R*M*G*J by rw [Matrix.mul_assoc (R*M),hg,Matrix.mul_one],hu,Matrix.add_mul]
omit [DecidableEq ι] in
lemma glideMat {P R:Funds ι}(hR:Rᵀ=R) : (R * Pᵀ).trace = (R*P).trace:=by
    rw[← Matrix.trace_transpose (R * P), transpose_mul,hR, trace_mul_comm _ R]
omit [DecidableEq ι] [DecidableEq κ] in
lemma gap_u {R:Funds ι}{J:Funds κ}(U:Funds ι)(h:R*M=M*J+R*T*J):
    (R*(M*Mᵀ)*U).trace=(J*((Mᵀ*U)*M)).trace + (((J*Mᵀ*U)*R)*T).trace:=by
    rw [← Matrix.mul_assoc,h,Matrix.add_mul,Matrix.add_mul, Matrix.trace_add]; congr 1
    · rw [Matrix.mul_assoc M J, Matrix.mul_assoc M,Matrix.trace_mul_comm]; congr 1; simp only [Matrix.mul_assoc]
    let L:=J*Mᵀ*U; change (R*T*J*Mᵀ*U).trace=_; rw [show R*T*J*Mᵀ*U=(R*T)*L by unfold L;simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]; congr 1; unfold L; simp only [Matrix.mul_assoc]
omit [DecidableEq ι] [DecidableEq κ] in
lemma clue {R:Funds ι}{J:Funds κ}(h:R*M=M*J+ R*T*J)(hr:Rᵀ=R)(hg:Jᵀ=J): (R*(V*(M*Mᵀ))).trace=(J*((Mᵀ*V)*M)).trace + (((J*Mᵀ*Vᵀ)*R)*T).trace:=by
   rw [← glideMat hr]; simp only [transpose_mul,transpose_transpose]; rw [← Matrix.mul_assoc,gap_u M T _ h]; congr 1; rw[show Mᵀ*Vᵀ*M=(Mᵀ*V*M)ᵀ by simp [Matrix.mul_assoc],glideMat hg]

lemma stag (H' X:Funds ι) {A R:Funds ι}{G J:Funds κ} (h:H*M=-T)(hk:A=H+M*Mᵀ+u • 1)(hv:G=Mᵀ*M+u • 1)(hr:R*A=1)(hj:G*J=1)(hH:Hᵀ=H)(hR:Rᵀ=R)(hJ:Jᵀ=J) :
    (R*(H'+H*V+Vᵀ*H+X)).trace/2-V.trace=
    ((R*(H'+((V*M)*Mᵀ+M*(V*M)ᵀ))).trace/2 - (J*((V*M)ᵀ*M+Mᵀ*(V*M))).trace) - u*(R*V).trace + ((R*X).trace/2 - (((J*Mᵀ*(V+Vᵀ))*R)*T).trace):=by
    have hp:= move_r H M T u h hk hv hr hj
    have hs : (R*(Vᵀ*H)).trace=(R*(H*V)).trace:=by rw [← glideMat hR (P:=H*V),transpose_mul,hH]
    have ht : (R*(M*(V*M)ᵀ)).trace= (R*(V*M*Mᵀ)).trace:=by rw [← glideMat hR (P:=V*M*Mᵀ)]; simp only [transpose_mul,transpose_transpose]
    have he : (J*((V*M)ᵀ*M)).trace=(J*(Mᵀ*(V*M))).trace:=by rw [← glideMat hJ (P:=Mᵀ*(V*M))]; simp only [transpose_mul,transpose_transpose]
    have hv' : (R*(H*V)).trace=(V.trace-(R*(M*Mᵀ)*V).trace)-u*(R*V).trace:=by
        have hx:H=A-M*Mᵀ-u • 1:=by rw [hk]; abel
        rw [hx,Matrix.sub_mul, Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,← mul_assoc R A, ← Matrix.mul_assoc R (M*Mᵀ),hr,Matrix.one_mul,smul_mul_assoc, Matrix.one_mul,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_smul]; rfl
    rw [Matrix.mul_add,Matrix.mul_add R, Matrix.mul_add R, Matrix.trace_add,Matrix.trace_add,Matrix.trace_add,hs]
    rw[hv',gap_u M T V hp]; rw [Matrix.mul_add R,Matrix.mul_add R, Matrix.trace_add,Matrix.trace_add (R*_),ht,Matrix.mul_add J, Matrix.trace_add,he, Matrix.mul_assoc V M,clue V M T hp hR hJ, ← Matrix.mul_assoc Mᵀ]
    rw[Matrix.mul_add (J*Mᵀ), Matrix.add_mul,Matrix.add_mul, Matrix.trace_add]; ring

variable {F:Type*} [AddCommGroup F][Module ℝ F]
def trapw (C:Matrix κ ι ℝ)(D:ι → κ → F): F:= ∑ i, ∑ j, C j i • D i j
omit [DecidableEq ι] [DecidableEq κ] in
lemma trap_pay (C:Matrix κ ι ℝ)(L:F→ₗ[ℝ]ℝ)(D:ι → κ → F):L (trapw C D)=(C*of (fun i j=> L (D i j))).trace:=by
    unfold trapw; rw [map_sum]; simp_rw[map_sum,map_smul]; rw[sum_comm]; rfl
end charge

variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{Y:Gal G f}{α C D μ:ℝ}
    {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T][FiniteDimensional ℝ T][CompleteSpace T]
    (U:Config G f)

def stock (p:Clip)(R:PathData G)(μ:ℝ)(U:Config G f):=flare p R U+mail U*(mail U)ᵀ+μ^2 • (1:Funds _)
def marke (p:Clip)(R:PathData G)(μ:ℝ)(U:Config G f):= Real.log (stock p R μ U).det/2 - Real.log (ammo μ U).det
def shellB (p:Clip)(R:PathData G)(μ:ℝ)(U:Config G f):=(stock p R μ U)⁻¹
def shellG (μ:ℝ)(U:Config G f):=(ammo μ U)⁻¹
def shoreM (p:Clip)(R:PathData G)(μ:ℝ)(Y:Gal G f)(U:Config G f):= (shellG μ U*(mail U)ᵀ * (tidal Y U+(tidal Y U)ᵀ))*shellB p R μ U
def shoreZ (p:Clip)(R:PathData G)(μ:ℝ)(Y:Gal G f)(U:Config G f):Link G f:= trapw (shoreM p R μ Y U) (jeps U)
def shoreX (p:Clip)(R:PathData G)(μ:ℝ)(Y:Gal G f)(U:Config G f):Link G f:= trapw (shellB p R μ U) (refrain Y U)
def ashore (p:Clip)(R:PathData G)(μ:ℝ)(Y:Gal G f)(U:Config G f):Link G f:= (1/2:ℝ) • shoreX p R μ Y U - shoreZ p R μ Y U
def lush (Y:Gal G f)(U:Config G f):=(tidal Y U).trace

def arrived (p:Clip)(R:PathData G)(μ:ℝ)(Y:Gal G f)(U:Config G f):= beamG (marke p R μ) U (Y U)
omit [FiniteDimensional ℝ T] [CompleteSpace T] in
lemma stocked (h:R.Bounds p α C D)(hμ:0<μ)(K:T → Config G f)(hp:Army K 0): Memo (stock p R μ ∘ K) 0 ∧ Memo (ammo μ ∘ K) 0:=by
    let F(x:T):= flare p R (K x)
    have hx: Memo F 0:=by
        refine memo_damage _ (F:=fun x=> burn p R (K x)) ?_
        exact Work.F02.mainTerm_contDiffAt (A:=fun v:T × Link G f=> input G f v.2*K v.1) h ((Army.powL (v:=Prod.snd) contDiffAt_snd).mul (Army.comp (g:=K) (w:=Prod.fst) hp contDiffAt_fst))
    have he := memo_flash hμ hp |>.1
    exact ⟨(hx.twice (he.cross he.spot)).twice (Memo.raw _ _), (he.spot.cross he).twice (Memo.raw _ _)⟩
lemma memo_mkr (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ U).det ≠ 0): ContDiffAt ℝ ω (bal U (marke p R μ)) 0:=by
    let V(z:Link G f):= input G f z*U
    obtain ⟨hp,hv⟩:= stocked h hμ V ((Army.powL (v:=id) contDiffAt_id).mul (Army.park U _))
    have hh: V 0=U:=by simp [V]
    exact ((hp.det_val.log (by rw[Function.comp_apply,hh];exact he)).div_const 2).sub (hv.det_val.log (by rw[Function.comp_apply,hh];exact (ammo_safe U hμ).det_pos.ne'))
lemma rhyme (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ U).det ≠ 0):
    arrived p R μ Y U = ((shellB p R μ U)*directionM (fun s=> stock p R μ (tendr Y s U)) 0 1).trace/2 - ((shellG μ U)*directionM (fun s=> ammo μ (tendr Y s U)) 0 1).trace:=by
    let B:= bal U (marke p R μ); let K(s:ℝ):= tendr Y s U
    obtain ⟨hp,hv⟩:= stocked h hμ K ((Army.powL (v:=fun s:ℝ=>s • Y U) (by fun_prop)).mul (Army.park U _))
    have hK: K 0=U:=tendr_o U; let T:=stock (f:=f) p R μ; let G':= ammo (G:=G) (n:=f) μ
    have ht : (T (K 0)).det≠0:=by rw[hK];exact he
    have hh : (G' (K 0)).det≠0:=(ammo_safe _ hμ).det_pos.ne'
    let L(s:ℝ):= B (s • Y U)
    have hj : HasFDerivAt B (fderiv ℝ B 0) ((0:ℝ) • Y U):= by rw [zero_smul]; exact ((memo_mkr U h hμ he).differentiableAt (by simp)).hasFDerivAt
    have hL: HasDerivAt L (arrived p R μ Y U) 0:= by change HasDerivAt (B ∘ (fun s:ℝ=>s • Y U)) (fderiv ℝ B 0 (Y U)) 0; exact hj.comp_hasDerivAt 0 (ray_id (Y U))
    have he' := ((hp.det_val.log (show (((T ∘ K) 0).det)≠0 from ht)).differentiableAt (by simp))
    have ht':= (hv.det_val.log (show ((G' ∘ K) 0).det ≠0 from hh)).differentiableAt (by simp)
    have hx:= trace_log_first hp ht 1
    have hy:= trace_log_first hv hh 1
    simp only [Function.comp_apply,hK] at he' ht' hx hy
    have hu := hL.unique ((he'.hasDerivAt.div_const _).sub ht'.hasDerivAt)
    change arrived p R μ Y U=fderiv ℝ (fun z=> Real.log (stock p R μ (K z)).det) 0 1/2-fderiv ℝ (fun z=> Real.log (ammo μ (K z)).det) 0 1 at hu
    rw [hx,hy] at hu; exact hu
lemma scale_g (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ U).det≠0)(hY:Tune Y U)(hh:∀ᶠ u:BaseSites G f in 𝓝 0,Y (Lattice.gauge (switchSite u) U)=armor (switchSite u) (Y U)) :
    (shellB p R μ U * beamH (aroma p R Y) U).trace/2 - lush Y U =
    arrived p R μ Y U- μ^2 * (shellB p R μ U *tidal Y U).trace + aroma p R (ashore p R μ Y) U:=by
    let W(s:ℝ):= tendr Y s U; let A(s:ℝ):= flare p R (W s); let H:= flare p R U; let B:= shellB p R μ U; let J:=shellG μ U; let V:= tidal Y U; let M(s):=mail (W s)
    let P:=mail U
    have hA: Memo A 0:= memo_damage _ (rate_burn U h)
    have ht: Army W 0:=(Army.powL (v:=fun s:ℝ=> s • Y U) (by fun_prop)).mul (Army.park U _)
    have hM: Memo M 0:= memo_flash hμ ht |>.1; have h0: M 0=P:= by unfold M W; rw [tendr_o]
    have hv: directionM M 0 1=V*P:= rising U hY hh
    have hs : directionM (fun s=> (M s)ᵀ) 0 1=(V*P)ᵀ:=by rw [← hv]; rfl
    have hp: directionM (fun s=>stock p R μ (W s)) 0 1=directionM A 0 1+(V*P*Pᵀ+ P*(V*P)ᵀ):=by
        rw[show (fun s=>stock p R μ (W s))= (A+fun s=> M s*(M s)ᵀ)+ (fun _=>μ^2 • 1) from rfl]; rw [direction_add (hA.twice (hM.cross hM.spot)) (Memo.raw _ _), direction_add hA (hM.cross hM.spot), direction_zero,add_zero,direction_prod hM hM.spot,hv,hs,h0]
    have hq:directionM (fun s=>ammo μ (W s)) 0 1=(V*P)ᵀ*P+Pᵀ*(V*P):= by
       rw[show (fun s=>ammo μ (W s))=(fun s=>(M s)ᵀ*M s)+(fun _=>μ^2 • 1) from rfl, direction_add (hM.spot.cross hM) (Memo.raw _ _), direction_zero, add_zero,direction_prod hM.spot hM,hv,hs,h0]
    have hx : aroma p R (ashore p R μ Y) U=(B*tensw p R Y U).trace/2- (J*Pᵀ*(V+Vᵀ)*B*tuneM p R U).trace:=by
       let L:=fderiv ℝ (burn p R U) 0; unfold aroma ashore; rw [map_sub,map_smul,smul_eq_mul, show fderiv ℝ _ _ (shoreX p R μ Y U)=(B*_).trace from trap_pay B L.toLinearMap (refrain Y U), show fderiv ℝ _ _ (shoreZ p R μ Y U)=(J*Pᵀ*(V+Vᵀ)*B*tuneM p R U).trace from trap_pay _ L.toLinearMap (jeps U)]; congr 1
       rw [mul_comm]; exact mul_one_div ..
    have hz: Hᵀ=H:= damage_symm _ (burn_cov U h)
    have hw: Bᵀ=B:=by unfold B shellB; rw[Matrix.transpose_nonsing_inv, show (stock p R μ U)ᵀ=stock p R μ U from ?_]; unfold stock; simp only [transpose_add,transpose_mul,transpose_transpose, transpose_smul,transpose_one]; rw [show (flare p R U)ᵀ= _ from hz]
    have hh': Jᵀ=J:=by unfold J shellG; rw [Matrix.transpose_nonsing_inv]; congr 1; unfold ammo tonic; simp
    rw [hx,solo U h hY,rhyme U h hμ he]; change (B * _).trace/2-V.trace = ((B*directionM (fun s=> stock p R μ (W s)) 0 1).trace/2-(J*directionM (fun s=>ammo μ (W s)) 0 1).trace) - μ^2 * _ + _; rw[hp,hq]
    exact stag H V P _ (μ^2) _ _ (A:=stock p R μ U) (G:=ammo μ U) (hum U h) rfl rfl (Matrix.nonsing_inv_mul _ he.isUnit) (Matrix.mul_nonsing_inv _ (ammo_safe U hμ).det_pos.ne'.isUnit) hz hw hh'
end YM.Trace.Det
