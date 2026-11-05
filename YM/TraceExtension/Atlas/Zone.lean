import YM.TraceExtension.Atlas.Horns
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{J:Scaling S}{V:∀ i,Vane C i}{Z:Arch C}
variable (h₁:Scribe X J V Z F.sector 𝓛 F.room.kernel H)

open StressFlux TraceExtension
variable {L L':Register G}
section
variable {S:Table L}{S':Table L'}
lemma lifted_eq (f:Active S≃ₗ[ℂ] Active S') {C:Carpet S'}{B:Carpet S} (h:LiftB f.toLinearMap C=B)(v): C (f v) (f v)= B v v:= congr_arg (fun B:Carpet S=> B v v) h
lemma comp_eq (B:Carpet S)(p q:Active S)(c:ℂ)(hq:q=c • p){z:ℂ}(hx:B q q=z)(hp:B p p=z)(hn:z≠0): c^2=1:=by
    have ht:B (c • p) (c • p)=c^2*B p p:=by rw[B.map_smul,_root_.smul_apply,map_smul,smul_eq_mul,smul_eq_mul,← mul_assoc, pow_two]
    apply mul_right_cancel₀ hn
    rw [← hp, ← ht,← hq,hx,hp,one_mul]
end
-- exact precess.X nuance sign branch Cal.
section
variable {r:ℝ}{P : change S 4}
variable (ht:XScope (H:=H) F h r P)

def AtAngle(r:ℝ)(P:change S 4): Prop:= XScope (H:=H) F h r P ∧ BranchV F 𝓛 H (P (stepField C))

include h h₁ ht
lemma filmS {w:Active (F₀)}(hw:w.val=stepField C): ∃ t:Active S, t.val=P w.val ∧ (scannerX F.room.kernel r).val t t=(scannerX H 1).val w w∧ 0 < ((scannerX H 1).val w w).re:=by
    obtain ⟨U,hU,hF,hA,hL⟩:= activeShip F h h₁ ht
    have hp := positive_turn (H:=H) h w (by rintro e; exact scale_alive h H (hw.symm.trans (congr_arg Subtype.val e)))
    rw [show starA H w=w from Subtype.ext (by rw [star_act,hw,(legitimacy F h h₁).1])] at hp
    refine ⟨U w,?_, ?_,hp⟩
    · rw[← coverV_act H F.room.kernel U w, hw,hL]
    exact lifted_eq U hA w

variable (hv: ∀ (J:Scaling S),StarPath X H J F.room.kernel 𝓛 → ∀ w Y,Gondola X H J 𝓛 w Y → Scribe X J w Z F.sector 𝓛 F.room.kernel H)
omit ht
include hv
lemma unique_v (hS:AtAngle (𝓛:=𝓛) (H:=H) F h r P){Q: change S 4}(hx:AtAngle (𝓛:=𝓛) (H:=H) F h r Q): P (stepField C)=Q (stepField C):=by
   obtain ⟨u,hu,hU⟩:= gardens F h _ hS.2 hv; obtain ⟨t,ht,hT⟩:= gardens F h _ hx.2 hv
   let f:Active (F₀):=⟨stepField C,sceneV H⟩;
   obtain ⟨p,hp,hA,hP⟩:= filmS F h h₁ hS.1 (w:=f) rfl; obtain ⟨q,hq,hB,-⟩:= filmS F h h₁ hx.1 (w:=f) rfl
   let c:=t/u; have he: 0 < c:=by unfold c; positivity
   have hf : Q (stepField C)=c • P (stepField C):=by rw[hT,hU, smul_smul,show c*u=t from div_mul_cancel₀ _ hu.ne']
   have hq' : q=(↑c:ℂ) • p:= Subtype.ext (by change q.val=(↑c:ℂ) • p.val; rw[hp,hq]; change Q (stepField C)=_; rw[hf, RCLike.real_smul_eq_coe_smul (K:=ℂ)];rfl)
   let B:= (scannerX F.room.kernel r).val
   have ht': ((c:ℂ)^2)=1:=by
       have hn:(scannerX H 1).val f f≠0:= fun h=> by rw [h] at hP; exact lt_irrefl _ hP
       exact comp_eq ( (scannerX F.room.kernel r).val) p q (c:ℂ) hq' hB hA hn
   have hc:c=1:=by norm_cast at ht'; nlinarith
   rw [hc,one_smul] at hf; exact hf.symm
end
variable (P:ℕ→change S 4)(hc:Tendsto (fun k=> moveV (S:=S) 4 (J.U k 4) (P k)) atTop (𝓝 1))(hp:∀ᶠ k in atTop,XScope (H:=H) F h (J.r k) (P k))
include h h₁
-- transports leading.W.C all frame modification budget near identity
include hc
lemma return_l: Tendsto (fun i=> moveV (S:=S) 4 (P i) (J.U i 4)) atTop (𝓝 1):= step_round (fun i=>actMove (S:=S) 4 (J.U i 4) (P i)) hc
include hp hc
lemma vocal : ∃ d:ℕ→ℝ,Tendsto (fun i=> BQ Z V i*d i) atTop (𝓝 (d2 G)) ∧ ∀ᶠ i in atTop, d i<0 ∧ (J.r i)^4 • lum F= (4*d i) • (P i (stepField C)):=by
    let B:= Bel C.book; let Q:= stepField C; let t:=lum F
    have he:∀ᶠ i:ℕ in atTop,∃ d:ℝ,(J.r i)^4 • t =(4*d) • P i Q:=by
       filter_upwards [hp] with i hi; obtain ⟨c,hχ⟩:=underLine F h hi.frame
       let f:= P i; have hz:t=c • f Q:=by rw[← show f (c • Q)=c • f Q from f.toLinearMap.restrictScalars ℝ|>.map_smul .., ← hχ]; exact (f.apply_symm_apply t).symm
       refine ⟨c*(J.r i)^ (4:ℕ)/4,?_⟩; rw[hz,smul_smul,mul_div_cancel₀ _ (by norm_num),mul_comm c _]
    let d(i):=if ht:∃ d:ℝ,(J.r i)^4 • t=(4*d) • P i Q then ht.choose else 0; have hX:=he.mono fun i hi=> (show (J.r i)^4 • t=(4*d i) • P i Q from by unfold d; rw [dif_pos hi]; exact hi.choose_spec)
    let M(i):= BQ Z V i; let R(i):= (P i).symm ( (M i * J.r i^ (4:ℕ)) • t); let y:= (4:ℝ) • Q
    have hx:Tendsto R atTop (𝓝 (d2 G • y)):=by
       have hp:= Dash.arcing (return_l F h h₁ P hc) (h₁.goal S); unfold y; rw[smul_smul,mul_comm]
       apply hp.congr (fun i=> ?_); let z:= (M i*J.r i^ (4:ℕ)) • t; change (P i).symm ((J.U i 4) ((J.U i 4).symm z))= _;rw [LinearEquiv.apply_symm_apply]
    have hp:Tendsto (fun i=> (M i*d i) • y) atTop (𝓝 (d2 G • y)):=by
       refine hx.congr' (hX.mono fun i hi=> ?_); let f:=(P i).symm; change f _=(M i*d i) • y
       rw [mul_smul (M i),hi,smul_smul,show ∀ a:ℝ,f (a • P i Q)=a • f (P i Q) from fun a=> f.toLinearMap.restrictScalars ℝ|>.map_smul .., show f (P i Q)=Q from LinearEquiv.symm_apply_apply ..]; unfold y; module
    have hy:Tendsto (fun i=> M i*d i) atTop (𝓝 (d2 G)):= by
       let P:ℝ→ₗ[ℝ] B.Field 4 := LinearMap.toSpanSingleton ℝ _ y
       have hv:y≠0:= smul_ne_zero (by norm_num:(4:ℝ)≠0) (scale_alive h H)
       obtain ⟨W,hW⟩:= P.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (show Injective P from smul_left_injective ℝ hv))
       have he(c:ℝ): W (c • y)=c:= LinearMap.congr_fun hW _
       have ht:= W.continuous_of_finiteDimensional.continuousAt.tendsto.comp hp; change Tendsto (fun i=> W (_ • y)) _ _ at ht; simpa only [Function.comp_def,he] using ht
    refine ⟨d, hy,(hX.and ((hy.eventually (gt_mem_nhds (force_neg h))).and (h₁.grows.eventually_gt_atTop 0))).mono fun i ⟨hi,hK,hT⟩=> ?_⟩; refine ⟨?_,hi⟩; change M i*d i < 0 at hK; change 0 < M i at hT; nlinarith only [hK,hT]
lemma latium: ∀ᶠ k in atTop,AtAngle (H:=H) (𝓛:=𝓛) F h (J.r k) (P k):=by
    obtain ⟨d,hD,hV⟩:=vocal F h h₁ P hc hp
    filter_upwards [hp,hV] with i hi ⟨hx,hC⟩
    let r:= (J.r i)^ (4:ℕ); have hr:0 < r:=pow_pos (J.positive i) _; let c:= -(4*d i); have hc:0<c:=by unfold c; linarith
    have hz:= illuminated (F:=F) (reach_right F h h₁) (r/c) (div_pos hr hc); refine ⟨hi,?_⟩; convert hz using 1
    apply smul_right_injective _ hc.ne'; change c • _=c • _; rw [smul_smul,mul_div_cancel₀ _ hc.ne',smul_neg]; unfold c; rw[neg_smul, ← hC]
end YM.Trace.Pilot
