import YM.TraceExtension.Det.Victor

/-!
# Strip the mail insert. Use signed difference account only locally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}{Y:Gal G f}{α C D μ:ℝ}
    {T:Type}[NormedAddCommGroup T][NormedSpace ℝ T][FiniteDimensional ℝ T][CompleteSpace T]
    (χ:Site f→ ℝ)(b:Axis) (U:Config G f)
-- χ the single b component
variable (G) in
def mine: Matrix (Lines G f 0) (Lines G f 1) ℝ:= of fun i j=> χ i.1*(if j=(i.1,coord b,i.2.2) then 1 else 0)
variable (G) in
def deal: Funds (Lines G f 1):= of fun i j=> let x:= i.1; (χ (x+step (axisEquiv.symm i.2.1))-χ x)*(if j=(x,coord b,i.2.2) then 1 else 0)
variable (G) in
def teat (r:ℕ): Funds (Lines G f r):= diagonal fun i => χ (i.1+step b)-χ i.1
lemma mined (x:Link G f)(y : Site f): gaugeColor (mine G χ b*ᵥ x) y= χ y • edgeColor x (y,b):=by
    ext1 i; change (∑ j, mine _ χ b (y,vac,i) j*x j)=_; change (∑ j, (χ y*(if j=(y,coord b,i) then 1 else 0))*x j)= _
    rw [sum_eq_single (y,coord b,i)]; simp only [if_true,mul_one]; rfl
    · intro d _ hd;simp[hd]
    simp
lemma deal_apply (x:Link G f)(y:Site f)(a:Axis): edgeColor (deal G χ b*ᵥ x) (y,a)= (χ (y+step a)-χ y) • edgeColor x (y,b):=by
    ext1 i; change (∑ j, deal _ χ b (y,axisEquiv a,i) j*x j)=_; unfold deal; rw [sum_eq_single (y,coord b,i)]; simp only [Matrix.of_apply,if_true, Equiv.symm_apply_apply,mul_one]; rfl
    · intro z _ hz;simp [hz]
    simp
lemma tea_b (x:Link G f)(y:Site f)(a:Axis): edgeColor (teat G χ b _*ᵥ x) (y,a)=(χ (y+step b)-χ y) • edgeColor x (y,a):=by
    ext1 i; change (teat G χ b 1 *ᵥ x) (y,coord a,i)=_; rw[teat,mulVec_diagonal];rfl
lemma tea_g (x:BaseSites G f)(y:Site f) : gaugeColor (teat G χ b _*ᵥ x) y=(χ (y+step b)-χ y) • gaugeColor x y:=by
    ext1 i; change (teat G χ b 0 *ᵥ x) (y,vac,i)=_; rw[teat,mulVec_diagonal];rfl
section swap
variable (k:Coats G f)
local notation "R#"=> trench k
local notation "Q#"=> troop k
lemma manage : mine G χ b*R#=Q#*mine G χ b :=by
    apply testers; intro x y; rw [← mulVec_mulVec,← mulVec_mulVec, troop,Stationary.trench,bill_pay,bill_pay]; apply congr_arg; apply gaugeColor.injective; ext1 i; rw[mined,armorG_at,mined,map_smul,armor_at]
lemma manager : deal G χ b*R#=R#*deal G χ b:=by
    apply testers; intro x y; rw[← mulVec_mulVec,← mulVec_mulVec,Stationary.trench,bill_pay,bill_pay]; apply congr_arg; apply edgeColor.injective; ext1 ⟨i,j⟩; rw [deal_apply,armor_at,armor_at,deal_apply,map_smul]
lemma management : teat G χ b 1*R#=R#*teat G χ b 1 ∧ teat G χ b 0*Q#=Q#*teat G χ b 0 :=by
    constructor
    · apply testers; intro x y;rw [← mulVec_mulVec,← mulVec_mulVec,Stationary.trench,bill_pay,bill_pay]; apply congr_arg; apply edgeColor.injective; ext1 ⟨i,j⟩; rw [tea_b,armor_at,armor_at,tea_b,map_smul]
    apply testers; intro x y;rw [← mulVec_mulVec,← mulVec_mulVec,troop,bill_pay,bill_pay]; apply congr_arg; apply gaugeColor.injective; ext1 i; rw[tea_g,armorG_at,armorG_at,tea_g,map_smul]
end swap
-- ideal V transl. sym discard curvature.
def sy {ι:Type}(V:Funds ι):= (1/2:ℝ) • (V+Vᵀ)
def wB (χ:Site f→ ℝ)(b:Axis)(Y:Gal G f)(U:Config G f):= sy (tidal Y U - mail U*mine G χ b - deal G χ b) + (1/2:ℝ) • teat G χ b 1
def wG (χ:Site f→ ℝ)(b:Axis)(U:Config G f):= sy (mine G χ b*mail U) -(1/2:ℝ) • teat G χ b 0

def mica (p:Clip)(R:PathData G)(μ:ℝ)(χ:Site f→ℝ)(b:Axis)(U:Config G f):= trapw (shellG μ U*mine G χ b*shellB p R μ U) (jeps U)

private lemma saira {κ: Type}[Fintype κ]{M:Funds κ}(X:Funds κ)(h : Mᵀ=M): (M*sy X).trace=(M*X).trace:=by rw [sy,Matrix.mul_smul,Matrix.trace_smul,Matrix.mul_add,Matrix.trace_add,glideMat h,smul_eq_mul]; ring
lemma mica_val (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ U).det≠0):
    (shellB p R μ U*tidal Y U).trace=(shellB p R μ U*(deal G χ b-(1/2:ℝ) • teat G χ b 1)).trace+(1/2:ℝ)*(shellG μ U*teat G χ b 0).trace + aroma p R (mica p R μ χ b) U + ((shellB p R μ U*wB χ b Y U).trace+(shellG μ U*wG χ b U).trace):=by
    let M:=shellB p R μ U; let J:=shellG μ U; let P:=mail U; let Q:=mine G χ b; let S:= tuneM p R U
    have hv: Mᵀ=M:=by unfold M shellB; rw [Matrix.transpose_nonsing_inv]; congr 1; unfold stock; simp only [transpose_add,transpose_smul,transpose_one,transpose_mul,transpose_transpose]; rw [show (flare p R U)ᵀ=(flare p R U) from damage_symm _ (burn_cov U h)]
    have hh: Jᵀ=J:=by unfold J shellG; rw [Matrix.transpose_nonsing_inv]; congr 1; unfold ammo tonic; simp
    have hp : (M*(P*Q)).trace=(J*(Q*P)).trace+aroma p R (mica p R μ χ b) U:=by
       unfold aroma mica
       have ht:M*P=P*J+ M*S*J:=move_r _ P S (μ^2) (A:=stock p R μ U) (G:=ammo μ U) (hum U h) rfl rfl (Matrix.nonsing_inv_mul _ he.isUnit) (Matrix.mul_nonsing_inv _ (ammo_safe U hμ).det_pos.ne'.isUnit)
       rw [show fderiv ℝ _ _ _=((J*Q*M)*S).trace from trap_pay _ (fderiv ℝ (burn p R U) 0).toLinearMap (jeps U),← Matrix.mul_assoc,ht,Matrix.add_mul,Matrix.trace_add]
       congr 1
       · rw [Matrix.mul_assoc,Matrix.trace_mul_comm P,Matrix.mul_assoc]
       rw [show M*S*J*Q=M*S*(J*Q) by rw [Matrix.mul_assoc],Matrix.trace_mul_comm]; congr 1; simp only[Matrix.mul_assoc]
    change (M*tidal Y U).trace=(M*_).trace+ (1/2:ℝ)*(J*_).trace+ aroma p R (mica p R μ χ b) U+((M*wB χ b Y U).trace+(J*wG χ b U).trace)
    unfold wB wG; simp only [Matrix.mul_sub,Matrix.mul_add,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_add,Matrix.trace_smul,saira _ hv,saira _ hh,smul_eq_mul]
    rw [show mail U=P from rfl,show mine G χ b= Q from rfl,hp]; ring
lemma w_cross (k:Coats G f)(h: tidal Y (Lattice.gauge k U)*trench k=trench k*tidal Y U):
    wB χ b Y (Lattice.gauge k U)*trench k=trench k*wB χ b Y U ∧ wG χ b (Lattice.gauge k U)*troop k=troop k*wG χ b U:=by
    let P:=trench k; let Q:=troop k; let V:=Lattice.gauge k U
    have hh {ι:Type}[Fintype ι][DecidableEq ι](P:Funds ι)(h:Military P)(A B:Funds ι)(hx:A*P=P*B): sy A*P=P*sy B:=by rw[sy,sy,smul_mul_assoc,Matrix.mul_smul,Matrix.add_mul,Matrix.mul_add,hx,h.transpose_cross h hx]
    constructor
    · unfold wB; rw[Matrix.add_mul,Matrix.mul_add,smul_mul_assoc,Matrix.mul_smul,(management χ b k).1]; congr 1; refine hh _ (trench_orthogonal _) _ _ ?_
      rw[Matrix.sub_mul, Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,h,manager, Matrix.mul_assoc (mail _), manage,← Matrix.mul_assoc (mail _),mail_carry, Matrix.mul_assoc]
    unfold wG; rw[Matrix.sub_mul,Matrix.mul_sub,smul_mul_assoc,Matrix.mul_smul,(management χ b k).2]; congr 1; refine hh _ (troop_orthogonal _) _ _ ?_
    rw[Matrix.mul_assoc,mail_carry,← Matrix.mul_assoc,manage, Matrix.mul_assoc]
variable {V:T→ Config G f}
omit [FiniteDimensional ℝ T] [CompleteSpace T] in
lemma cam_c (hv:Army V 0)(i j): ContDiffAt ℝ ω (fun z=> jeps (V z) i j) 0:=by
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
lemma mica_part (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ U).det≠0)(k:Coats G f):
    mica p R μ χ b (Lattice.gauge k U)= armor k (mica p R μ χ b U):=by
    let P:=trench k; let Q:= troop k; let V:=Lattice.gauge k U
    let F(U:Config G f):=shellG μ U*mine G χ b*shellB p R μ U
    obtain ⟨hv,hq⟩:=shell_guard U k h hμ he
    have ht: F V*P=Q*F U:=by
       change F _*trench k=troop k*_; unfold F V; rw [Matrix.mul_assoc _ (shellB p R μ _),hv,← Matrix.mul_assoc, Matrix.mul_assoc (shellG μ _), manage,← Matrix.mul_assoc,hq]; simp only [Matrix.mul_assoc]
    obtain ⟨X,hX⟩:=juke_form U;obtain ⟨Y,hY⟩:= juke_form V
    change trapw (F V) (jeps V)=armor k (trapw (F U) (jeps U)); unfold jeps; simp_rw [hY,hX]; apply trap_guard _ _ (armor k) (P:=P) (Q:=Q) (trench_orthogonal _) (troop_orthogonal _) ht
    intro x y; rw [← hY, ← hX, show P*ᵥ x=armor k x from bill_pay .., show Q*ᵥ y=armorG k y from bill_pay ..]; exact lull_turn U k x y
lemma cloak_mica (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det ≠ 0): Cloaked (mica p R μ χ b):=by
    refine ⟨?_,?_⟩
    · let V:=input G f; have hv: Army V 0:=Army.powL (v:=id) contDiffAt_id
      obtain ⟨hp,hh⟩:= gate_shell h hμ he hv (input_zero _ _)
      have ht:= (hh.cross (V:=fun z=> mine G χ b) (Memo.raw _ _)).cross hp
      unfold mica trapw; refine ContDiffAt.sum fun i _=>ContDiffAt.sum fun j _=>(ht j i).smul (cam_c hv _ _)
    intro T _ _ _ _ V k u hV hv _ _
    filter_upwards [gate_n h hμ he hV hv] with x hx; exact mica_part _ _ _ h hμ hx _
lemma w_memo (hY:Cloaked Y)(hv:Army V 0)(hp:V 0=1): Memo (wB χ b Y ∘ V) 0 ∧ Memo (wG χ b ∘ V) 0:=by
    have ht:= memo_t hY V hv hp; have hm:= memo_flash (μ:=1) zero_lt_one hv|>.1; let F:=mine G χ b
    have hu (z w:T→ Funds (Lines G f 1))(h:Memo z 0)(he:Memo w 0): Memo (fun y=> z y-w y) 0:= fun i j=>(h i j).sub (he i j)
    have hf:= hu _ (fun _=> deal G χ b) (hu _ _ ht (hm.cross (U:=fun x=> mail (V x)) (V:=fun _=>F) (Memo.raw _ _))) (Memo.raw _ _)
    have hz:=Memo.cross (Memo.raw F (0:T)) hm
    exact ⟨(Memo.debit (1/2:ℝ) (hf.twice hf.spot)).twice (Memo.raw _ _),fun i j=>(Memo.debit (1/2:ℝ) (hz.twice hz.spot) i j).sub contDiffAt_const⟩
omit [FiniteDimensional ℝ T] [CompleteSpace T] in
lemma mica_lim (h:R.Bounds p α C D)(hμ:0<μ)(he:(stock p R μ (1:Config G f)).det≠0)(hv:Army V 0)(hp:V 0=1):
    ∀ᶠ z in 𝓝 0, let U:=V z;
      (shellB p R μ U*tidal Y U).trace=(shellB p R μ U*(deal G χ b-(1/2:ℝ) • teat G χ b 1)).trace+(1/2:ℝ)*(shellG μ U*teat G χ b 0).trace + aroma p R (mica p R μ χ b) U + ((shellB p R μ U*wB χ b Y U).trace+(shellG μ U*wG χ b U).trace):=by filter_upwards[gate_n h hμ he hv hp] with x hx; exact mica_val _ _ _ h hμ hx
end YM.Trace.Det
