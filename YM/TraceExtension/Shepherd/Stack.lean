import YM.TraceExtension.Shepherd.Stairs
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Gauge Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n)
local notation "W!"=> R.path
local notation "r!"=> R.clip.relaxation
local notation "b!"=> R.p.threshold
local notation "M!"=> R.p.B
local notation "d!"=> R.p.supportExponent
variable {σ A v δ t:ℝ}(h:R.Lawful σ A v δ t)(H:Geo.Width R.p R.clip σ)
abbrev trail (t:Barley) := t.elim (Low.length W!) (fun i=> (tooth R i).length)
abbrev wide (G: Gauge)(d:ℝ):= Real.exp (85*d)
private lemma cost_top (t:Barley) : M!*coverNumber M! (fort R t)≤ M!*85+trail R t:=by
    rcases t with a|i; exact Geo.low_geometry ..
    let T:= tooth R i; have hp: M!*coverNumber M! (fort R (.inr i))≤ M!+(rowD i*(2*M!)+ T.length):= Next.Scheduling.Wages.traversed _ _ _ R.p.B_pos
    have hh: rowD i ≤ 4:=by
       rcases i with i|i
       · have h:=High.significant i; change High.arity _ ≤ _; omega
       exact (show 2 ≤ (4:ℕ) by decide)
    apply hp.trans; change _ ≤ _+T.length; nlinarith only [Nat.mul_le_mul_right (2*M!) hh]
include h H
lemma uniform_amt (p:Barley) : Real.exp (d!*coverNumber M! (fort R p)) ≤ wide G d! * Real.exp ((σ/2)*(trail R p:ℝ)):=by
    let y:ℝ:= M!;let x:ℝ:=trail R p; let a:ℝ:=coverNumber M! (fort R p); have hy : 0< y:= Nat.cast_pos.mpr R.p.B_pos;have hd:= R.p.exponent_pos; have hs:=h.paths.width
    have hx:a ≤ 85+x/y:=by
        have ht : y*a ≤ y*85+x:= by unfold x y a; exact_mod_cast cost_top R p
        suffices h : a-85 ≤ x/y by linarith only[h]
        apply (le_div_iff₀ hy).mpr; linarith only [ht]
    unfold wide; rw [← Real.exp_add]; apply Real.exp_monotone; have hh:x ≥ 0:=Nat.cast_nonneg _; have hv:= H.2.2
    apply (mul_le_mul_of_nonneg_left hx hd.le).trans; have he : d!/y*x ≤ σ/4*x:=mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right (le_add_of_nonneg_right (zero_le_one)) hy.le).trans hv) hh; rw [div_mul_eq_mul_div] at he; rw [mul_add,← mul_div_assoc]; change _ ≤ 85*d!+(σ/2)*x; nlinarith only [he,mul_nonneg hs.le hh]
def crown (σ A:ℝ):= (wide G R.p.supportExponent*momentPrice 1 (σ/4))*VerifiedReset.Geo.lowerSize R.clip A
def massT (p:Barley)(f: Barley→ℝ):= f p * Real.exp (R.p.supportExponent * coverNumber R.p.B (fort R p))
lemma phaseHit : SumBudget (fun i:Low=> phial R i * Real.exp (d!*coverNumber M! (fort R (.inl i)))) (crown R σ A):=by
    have hp :0 ≤ σ:=H.1.le; let f(i:Low):= i.mark W! R.clip; let a:= crown R σ A
    let M:= momentPrice 1 (σ/4); have hM:0 < M:= momentPrice_pos 1 (by have h:=H.1; positivity)
    refine Extra.Multi.Budget.mono (budget_scale (x:=wide G d!*M) (by have hw:= Real.exp_pos (85*d!); unfold wide; positivity) (Geo.lower_budget G R.path h.paths)) (fun i=> ?_) ?_ le_rfl
    · exact mul_nonneg (phial_nonneg ..) (Real.exp_pos _).le
    intro i; refine (mul_le_mul_of_nonneg_left (uniform_amt R h H (.inl i)) (phial_nonneg ..)).trans ?_
    let L:ℝ:= i.length W!; have hL: 0 ≤ L:= Nat.cast_nonneg _; let Y:=wide G d!; have hy:0≤ Y:= (Real.exp_pos _).le
    unfold phial;change |f i| * (L+1)*Real.exp (L / r!)*(Y*Real.exp (σ/2*L)) ≤ Y*M*(_* _)
    have hv: L+1 ≤ M*Real.exp (σ/4*L):=by simpa [add_comm (1:ℝ)] using! spendMoment 1 (η:=σ/4) (by have h:= H.1; positivity) hL
    have hk : L/r! ≤ σ/4*L:=by apply (div_le_iff₀ R.clip.radius_pos).mpr; nlinarith only[H.2.1,hL,mul_le_mul_of_nonneg_right H.2.1 hL]
    calc
      _ ≤ |f i| * (M*Real.exp (σ/4*L))*Real.exp (σ/4*L)*(Y*Real.exp (σ/2*L)):=by gcongr
      _ = _:=by rw [show σ*(_ : ℝ) = σ/4*L+(σ/4*L+ σ/2*L) from (show σ*(i.length W!:ℝ)= _ from by unfold L; ring),Real.exp_add,Real.exp_add]; change _=Y*M*(|f i| * _); ring

def bedste (A v:ℝ):= wide G d!* ( |R.beta| *(b!^3*A+b!^4*A) + b!^2*v)
lemma heightT : SumBudget (fun t:Fleece=> massT R (.inr t) (bingo R)) (bedste R A v):=by
    let b(i:Fleece):= (tooth R i).budget σ
    let c(i:Fleece):= |wake R (.inr i)| * b!^(rowD i) * b i
    have hp:= R.p.threshold_pos
    have Hc : SumBudget c (|R.beta| *(b!^3*A+b!^4*A) + b!^2*v):=by
       have H1:=budget_scale (x:= (b!^2)) (by positivity) h.paths.two
       apply Cost.sum _ ?_
       · rw [show |R.beta| * (_+_)=|R.beta| *b!^3*A + |R.beta| *b!^4*A by ring]; apply Cost.sum
         · exact budget_scale (x:= |R.beta| * b!^3) (by positivity) h.paths.three
         exact budget_scale (x:= |R.beta| * b!^4) (by positivity) h.paths.four
       simpa only [comp_def,c,wake,Sum.elim_inr,abs_one,one_mul,rowD] using! H1
    apply Extra.Multi.Budget.mono (budget_scale (x:=wide G d!) (Real.exp_pos _).le Hc) _ _ le_rfl
    · exact fun i=> mul_nonneg ((abs_nonneg _).trans (canto R _ 1)) (Real.exp_pos _).le
    intro i; let T:=tooth R i;let L:ℝ:= T.length; have he: (σ/2)*L ≤ σ*L:= mul_le_mul_of_nonneg_right (half_le_self h.paths.width.le) (Nat.cast_nonneg _)
    unfold massT; apply le_trans (mul_le_mul_of_nonneg_left (uniform_amt R h H (.inr i)|>.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone he) (Real.exp_pos _).le)) ((abs_nonneg _).trans (canto R _ 1))) (le_of_eq ?_)
    change |wake R _| * (T.magnitude * _)*(wide G d!*_) = wide G d!*(|_| * _*(T.magnitude* Real.exp (σ*L))); ring
-- integrated doses at σ
lemma grand : SumBudget (fun t=> massT R t (bingo R)) ((2*b!*|R.beta|)* crown R σ A+ bedste R A v):=by
    apply Cost.sum _ (heightT R h H); have hp:= R.p.threshold_pos; apply Extra.Multi.Budget.mono (budget_scale (x:= 2*b!*|R.beta|) (by positivity) (phaseHit R h H)) _ _ le_rfl
    · exact fun i=> mul_nonneg ((abs_nonneg _).trans (canto R _ 1)) (Real.exp_pos _).le
    intro i; change |R.beta| * prime R i*_ ≤ _; unfold prime phial; nlinarith only [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ i.length W!+ (1:ℝ) from le_add_of_nonneg_left (Nat.cast_nonneg _)) (show 0 ≤ (2:ℝ)* |R.beta| *b!*|i.mark W! R.clip| * Real.exp (i.length W!/r!)*Real.exp (d!*coverNumber M! (fort R (.inl i))) by positivity)]
lemma salary (d:ℝ)(hv:0≤d): SumBudget (fun i=> massT R i (fun i=>balm R i d)) ((|R.beta| *((2*kindle G) * d * b!))*crown R σ A+ 2*bedste R A v):=by
    have hp := R.p.threshold_pos; have he : 0 ≤ kindle G:=by have h:=G.colorScale_pos; unfold kindle;positivity
    apply Cost.sum _ _
    · convert budget_scale (x:=|R.beta| *(2*kindle G*d*b!)) (by positivity) (phaseHit R h H) using 2 with i; change |R.beta| * thyme R i d* _= _; unfold thyme; ring
    convert budget_scale (x:=(2:ℝ)) zero_le_two (heightT R h H) using 2 with i; dsimp [Function.comp,massT, balm,bingo]; ring
end YM.Trace.Shepherd
