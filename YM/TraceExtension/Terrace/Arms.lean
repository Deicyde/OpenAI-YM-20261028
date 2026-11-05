import YM.TraceExtension.Terrace.Stilt
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
abbrev Dust:ℝ:=1/10000
abbrev Tau (P:Levels G)(i:ℕ)(x:ℝ):= watch P (x*Dust) i
lemma Tau_pos (P:Levels G) (i:ℕ) (x:ℝ):0 < Tau P i x:=Real.exp_pos _
lemma Tau_add (P:Levels G)(i:ℕ)(x y:ℝ): Tau P i (x+y)= Tau P i x * Tau P i y:=by unfold Tau watch; rw[add_mul,add_mul,Real.exp_add]
lemma Tau_minus (P:Levels G)(i:ℕ)(x y:ℝ): Tau P i (x-y)=Tau P i x/Tau P i y:=by unfold Tau watch; rw[sub_mul,sub_mul,Real.exp_sub]
lemma Tau_neg (P:Levels G)(i:ℕ)(x:ℝ): Tau P i (-x)=(Tau P i x)⁻¹:=by unfold Tau watch; rw[neg_mul,neg_mul,Real.exp_neg]
lemma Tau_pow (P:Levels G)(i:ℕ)(x:ℝ)(j:ℕ): Tau P i (j*x)=Tau P i x^j:=by unfold Tau watch; rw[mul_assoc,mul_assoc,Real.exp_nat_mul]; rw [mul_assoc]
lemma tau_mono (P:Levels G)(i): Monotone (Tau P i):=fun _ _ h=> Real.exp_monotone (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ) ≤ Dust)) (gate_le _ ((P.fits.delayed _))|>.le))
lemma toll_small {P:Levels G}{x:ℝ}(hp:0<x) {f:ℕ→ℝ}(ht:Ticket P 0 f):∀ᶠ i:ℕ in atTop, f i ≤ Tau P i x:=(ht _ (mul_pos hp (by norm_num : (0:ℝ)<Dust))).mono fun i h=> h.2
lemma credit (A:Levels G)(d i:ℕ): 0 < fly A d i:=by unfold fly fog; positivity [bell A i]
lemma grantK (P:Levels G)(h:G.Simple)(θ:PostT P) {f:ℕ→ℕ}(ht:∀ᶠ i in atTop,f i≤ summit P i)(d:ℕ):Ticket P 0 (fun i=> (fly P d (f i))⁻¹):=by
   let k:= winter G d
   simp_rw [fly,MergeProof.fog,inv_inv]; refine ((stickK _ h θ).pows h k).mono (ht.mono fun i hi=>?_); exact ⟨pow_nonneg (bell ..|>.le) _,pow_le_pow_left₀ (bell ..|>.le) (monoBeta P h hi) _⟩
lemma coreK (P:Levels G)(h:G.Simple)(θ:PostT P){f:ℕ→ℕ}(ht:∀ᶠ i in atTop,f i≤ summit P i):Ticket P 0 (fun i=> (P.params (f i)).columns):=by
    apply Ticket.mono ( (sapTree h P 2 zero_le_two).push (LyreK P h)); filter_upwards [ht,bond P h θ] with i hi he
    exact ⟨zero_le_one.trans (P.params _).columns_ge,(θ.share _).trans ((lypos P h hi).trans he.2.1)⟩
lemma gainsK {C:Family G}(h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels) :∀ᶠ i:ℕ in atTop, Tau (C.path.levels) i 500 ≤ gainChart C.path (summit (C.path.levels) i) (basin _ K i):=by
   filter_upwards [glacier _ h θ K] with i hi
   apply Real.exp_monotone; norm_num; change _ ≤ 1/8 * gap C.path.levels (basin C.path.levels K i) (summit C.path.levels i); linarith only[hi, gate_le _ (C.path.levels.fits.delayed i)]
variable {C:Family G}(h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> tilesAt C.S
open Relay
include h θ K
-- payment not perturbative. support PRICE.
lemma breeze(d:ℕ) : ∀ᶠ i:ℕ in atTop,let j:=basin (A) K i; let k:=summit (A) i; let a:=C.S.a; let w:= (a j)^d*Tau (A) i 400; let u:=4*(1+((A).params k).columns)
      w*‖alto C.path j d‖*(u/gainChart C.path k j) ≤ fly (A) d j/2∧ 2*(a i)^d*Tau (A) i 1*(stakes C i j/w) ≤ Tau (A) i (-300):=by
    let P:=C.path.levels; let j':=basin (A) K; let k':=summit (A)
    let u i:=4*(1+(P.params (k' i)).columns); let q i:= (C.S.a i/C.S.a (j' i))^d
    have hB:Ticket (A) 0 (fun i=>2*u i*(fly (A) d (j' i))⁻¹):= ((sapTree h P 2 zero_le_two).push ((sapTree h P 4 (by positivity)).push ((sapTree h P 1 zero_le_one).sum (coreK P h θ (Eventually.of_forall fun i=> le_refl (k' i))) h))).push (grantK _ h θ ((open_budget P h θ K).mono fun _ h=> h.le) _)
    have hP:Ticket (A) 0 (fun i=> 2*q i*stakes C i (j' i)):= ((sapTree h P 2 zero_le_two).push ((hullK _ K h θ).pows h d)).push (stakeK K h θ)
    filter_upwards [toll_small (x:= 100) (by norm_num) hB,toll_small (x:=99) (by norm_num) hP,gainsK (C:=C) h θ K] with i hX hQ hi
    let k:=k' i; let j:=j' i; let a:= Tau P i; let v:= fly P d j; let b:=(C.S.a j)^d; have hz:0<b:=pow_pos (C.S.a_pos j) _; have hv :0<v:=credit ..; let Cx:=u i; let Z:= stakes C i j; let G:=gainChart C.path k j; let W:= (C.S.a i)^d;have ha:=Tau_pos P i
    intro j₀ k₀ a₀ w u₀
    constructor
    · change b*a 400* _*(Cx/G) ≤ v/2; rw [alto_norm]; change b*a 400*b⁻¹*_ ≤ _; have hs : a 400 * (2*Cx*v⁻¹) ≤ G:= (mul_le_mul_of_nonneg_left hX (Tau_pos P i 400|>.le)).trans ((Tau_add P i 400 100).symm.le.trans (by norm_num; exact hi))
      have hh:0<G:=Real.exp_pos _; field_simp at hs ⊢; linarith only[hs]
    change 2*W*(a 1)*(Z/(b*a 400)) ≤ a (-300); set e:=a 1
    have hQ:2*(W/b)*Z≤ a 99:=by rw [show W/b=q i from (div_pow ..).symm];exact hQ
    have hb := mul_le_mul_of_nonneg_right hQ (Tau_pos P i 1|>.le); have he:a 99 * e=a (-300)*a 400:=by unfold e a; rw [←Tau_add,←Tau_add]; norm_num
    change _*e≤ _ at hb; rw [he] at hb
    have ha:0<a 400:= Tau_pos ..; field_simp at *; linarith only [hb]
end YM.Trace.Terrace
