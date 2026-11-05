import YM.UVExtension.Eyelet.Boot
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Eyelet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Next.Foundations Concert lp
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d :ℕ} {F:Frame G d} (H: Hol G) (p: BudgetPoint){R:Rep G n} {ι:Type}
section lp
variable {E:ι→Type} [∀ i,NormedAddCommGroup (E i)]
lemma castL (f:↥(lp E 1)) : HasSum (fun i=> ‖f i‖) ‖f‖:=by simpa using! lp.hasSum_norm (by simp) f
lemma fence {v:∀ i,E i} (h:Summable (fun i=> ‖v i‖)): Memℓp v 1:=by
    have hv:0<(1:ENNReal).toReal:=by simp
    refine (memℓp_gen ?_)
    simpa using h
end lp
abbrev Roc (d:ℕ)(H:Hol G)(n:Side)(p:BudgetPoint):= ↥(lp (fun i:Eyelet.Slot n=> Gondola d H i.1 p) 1)
abbrev Coil (G:Gauge)(n:Side)(p:BudgetPoint):= ↥(lp (fun i:StockTag n=> Stream G p i) 1)
abbrev Cow (G:Gauge)(n:Side)(p:BudgetPoint)(d:ℕ)(H:Hol G):= Roc d H n p × Coil G n p
variable {p}
def fee (p:BudgetPoint){n:Side}(X:Support n):ℝ:= Real.exp (p.supportExponent*coverNumber p.B X)
lemma toll_pos (p:BudgetPoint){n:Side}(X:Support n): 0< fee p X:=Real.exp_pos _
lemma tailor (K:Keeper R.p R.activities)(i:StockTag n)(f:Config G n→ℂ) : f∈ Bolt R.p i ↔ SlotFit R 0 (cart K i) f∧∃ a:ℝ,∀ U,‖f U‖≤ a:=by
   let P:=R.p; let A:=R.activities.forced; let T:=K.code (i,0); have he:(A T).support=i.val.1:= K.support _; have hs:(A T).inventory=i.val.2 := K.inventory _
   constructor
   · intro hx; obtain ⟨hr,hB,h,hP,hQ,hC⟩:=show Tail P i f from hx; refine ⟨⟨h,hB,(he.symm ▸ hr),fun hv => he.symm ▸ hP hv,fun U hu=>?_⟩,hC⟩
     have hy : (A T).support ∩ flags P.threshold U=(A T).inventory:= he.symm ▸ hs.symm ▸ hQ U hu
     exact ⟨hy,K.pass _ U hy⟩
   rintro ⟨⟨h,hb,hr,hP,hV⟩,hA⟩; exact ⟨he ▸ hr,hb,h,fun hv=>he ▸ hP hv,fun U hu=>he ▸ hs ▸ (hV U hu).1,hA⟩
variable (P:Coefficient F n)(v:ℝ)
structure Eligible (P:Coefficient F n)(H:Hol G)(R:Rep G n)(v:ℝ):Prop where
   hK: Nonempty (Keeper R.p R.activities)
   form : P.Format 0 H R
   pay : ∃ a, P.remBound 0 R v a

variable {v H P}
namespace Eligible
variable (h:Eligible P H R v)
include h
lemma vigor : 0<v:=by obtain ⟨w,a,b,-,-,-,hp,-⟩:=h.pay; exact hp
lemma monies {t:ℝ} (hL:P.remBound 0 R v t) : ∃ a b:ℝ,a+b≤ t ∧
    (∃ e:Eyelet.Slot n→ℝ,(∀ i,R.p.supBounds 0 i.1.val (graft P i) (e i)) ∧ SumBudget (fun i=> fee R.p i.1.val*e i) a) ∧
    (∃ f:StockTag n→ℝ,(∀ j, 0≤ f j ∧∀ U,‖bud P j (R:=R) U‖ ≤ f j) ∧ SumBudget (fun i=> fee R.p i.val.1 *f i) (v*b)):=by
   obtain ⟨K⟩:= h.hK
   obtain ⟨a,b,h₀,h₁,hv,hp,⟨e,ht,hF⟩,f,hϕ,hq⟩:= priced P K h.form.origin hL
   refine ⟨a,b,hv,⟨e ∘ (key n).symm,?_ ,?_⟩,f∘ cart K,?_,?_⟩
   · intro i; obtain ⟨i,rfl⟩:=(key n).surjective i; rw [Function.comp_apply,(key n).symm_apply_apply]; exact hF _
   · apply sumBudget_pass (key n).toEmbedding _ _ (fun i hi=> absurd ((key n).surjective i) hi); simp only [Equiv.coe_toEmbedding,Function.comp_apply,Equiv.symm_apply_apply]; exact ht
   · intro i; rw [Function.comp_apply]; refine ⟨(hq _).1,fun U=>?_⟩; rw [show bud P i (R:=R) U= (ageing P K).forced (cart K i) U from (congr_fun (stowed K P i) U).symm]; exact (hq _).2 U
   have he i: (R.activities.forced (cart K i)).support=i.val.1:= K.support _
   simp only [comp_apply]; simp_rw [← he]; exact _root_.YM.Push.AbsoluteSums.budget_pull _ (cart K).injective hϕ -- find

def fernP (i:Eyelet.Slot n): Birth H i.1 R.p d:= ⟨graft P i,by
    let K:=h.hK.some; let P':=ageing P K
    obtain ⟨a,hL⟩:=h.pay; obtain ⟨u,v,-,⟨e,he,hf⟩,hp⟩:= monies h hL; obtain ⟨j,hj⟩:= (key n).surjective i; subst i
    have hx:= dye P K h.form; exact ⟨hx.smooth _,hx.identity_null j,hx.projects j,_,he _⟩⟩ -- Birth d order

def sapP (i:StockTag n): Bolt (G:=G) R.p i:= ⟨bud P i (R:=R),by
    obtain ⟨K⟩:=h.hK; obtain ⟨a,hA⟩:=h.pay; obtain ⟨t,v,-,-,f,hf,H⟩:= monies h hA; refine (tailor K _ _).mpr ⟨?_,_,(hf i).2⟩; have hx:= rack_format K P h.form (o:=0); rw [show bud P i (R:=R) = (rack K P).forced (cart K i) from (stowed K P i).symm]; exact ⟨hx.invariant _,hx.borel _,hx.supported _,hx.carried _,hx.forcing _⟩⟩

def goals (i:Eyelet.Slot n): Gondola d H i.1 R.p := (fee R.p i.1.val:ℂ) • twig _ (h.fernP i)

def team (i:StockTag n): Stream G R.p i := ((fee R.p i.val.1/v:ℝ):ℂ) • twig _ (h.sapP i)
lemma shifts {t:ℝ}(hp:P.remBound 0 R v t): ∃ a b:ℝ,a+b≤ t ∧ SumBudget (fun i=> ‖h.goals i‖) a ∧ SumBudget (fun i=> ‖h.team i‖) b:=by
    obtain ⟨a,b,hq,⟨e,hE,hB⟩,f,hF,hT⟩:= h.monies hp
    have hr (j: Eyelet.Slot n):(‖twig (tin d H j.1 R.p) (h.fernP j)‖:ℝ) ≤ e j:= (pays d H j.1 R.p (h.fernP j)).1 (hE j)
    have hs (j:StockTag n) : ‖twig (sink (G:=G) R.p j) (h.sapP j)‖ ≤ f j:= (debts R.p _ (h.sapP j)).1 ((hF j).2)
    have hx:= h.vigor
    refine ⟨a,b,hq,Local.sumBudget_mono hB (fun _=>norm_nonneg _) (fun i=>?_) le_rfl, Local.sumBudget_mono (Local.sumBudget_mul_left hT (inv_pos.mpr hx).le) (fun _=> norm_nonneg _) (fun i=>?_) (by rw [inv_mul_cancel_left₀ hx.ne'])⟩
    · rw [goals,norm_smul,Complex.norm_real,Real.norm_of_nonneg (toll_pos ..|>.le)]; exact mul_le_mul_of_nonneg_left (hr i) (toll_pos ..|>.le)
    unfold team; have he :0≤fee R.p i.val.1/v:= (div_pos (toll_pos ..) hx).le; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg he]
    exact (mul_le_mul_of_nonneg_left (hs i) he).trans_eq (by rw [div_eq_mul_inv]; ring)

def tollE : Roc d H n R.p:=⟨h.goals,fence (by obtain ⟨a,hA⟩:=h.pay; obtain ⟨c,b,w,F,K⟩:= h.shifts hA; exact F.2.1)⟩
def tollK : Coil G n R.p:=⟨h.team,fence (by obtain ⟨a,hA⟩:=h.pay; obtain ⟨c,b,w,F,K⟩:=h.shifts hA; exact K.2.1)⟩
lemma costs {t:ℝ}(hp:P.remBound 0 R v t) : ‖h.tollE‖+‖h.tollK‖ ≤ t:=by
    obtain ⟨a,b,ht,hA,hK⟩:=h.shifts hp; exact (add_le_add ((castL h.tollE).tsum_eq.symm.trans_le hA.2.2) ((castL h.tollK).tsum_eq.symm.trans_le hK.2.2)).trans ht
end Eligible
end YM.UVExtension.Eyelet
