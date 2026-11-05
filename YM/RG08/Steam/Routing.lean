import YM.RG08.Steam.Valves
import YM.RG08.Forms.Powers

/-!
# Bounds for all fixed positive-order formal connected heat propagation
-/
noncomputable section
namespace YM.RG08.Steam
open Forms Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I:Type}{n p q e a r j :ℕ}{d:Ground I}{σ δ C D B W:ℝ}

def taps (j e n a r:ℕ) := 0<r ∧ 0<a ∧ r≤a+2 ∧ (a<e ∨ (a=e ∧ (n<r ∨ (j=0 ∧ n≤r))))
variable {Γ Γ':Forms.Line I}{V V':Grain I}

private lemma taps_side {p':ℕ} (hc:p'<e) (ht:taps j p' n a r):taps p e q a r:=by unfold taps at *; omega

private lemma coupon_lap {F F':Grain I}(h:Cot d σ δ C (F e (n+2)) (F' e (n+2)))(hk:WireCot d σ δ B Γ Γ')(hd:0≤δ) : Cot d σ δ ((((n:ℝ)+2)*(n+1)/2)*(2*C*B)) (unilateral Γ F e n) (unilateral Γ' F' e n):=by
 unfold unilateral;rw [← abs_of_nonneg (by positivity : (0:ℝ)≤ (((n:ℝ)+2)*(n+1)/2))]; simpa only [abs_of_nonneg (by positivity:(0:ℝ)≤(((n:ℝ)+2)*(n+1)/2))] using (h.lap' hk hd).smul ((((n:ℝ)+2)*(n+1)/2))

private lemma coupon_move {p:ℕ}(he:p=n){F F':Flake p I}(h:Cot d σ δ C F F'):Cot d σ δ C (move he F) (move he F'):=by subst he; exact h

private lemma coupon_pair {F F':Flake (p+1) I}{G G':Flake (q+1) I} (h:Cot d σ δ C F F')(H:Cot d σ δ D G G')(hk:WireCot d σ δ B Γ Γ')(hd:0≤δ): Cot d σ δ (((p:ℝ)+1)*(q+1)/2*(3*(C*B*D))) (pair Γ F G n) (pair Γ' F' G' n):=by
 unfold pair; split_ifs with he
 · simpa only [abs_of_nonneg (by positivity:(0:ℝ)≤(((p:ℝ)+1)*(q+1)/2))] using (coupon_move he (h.bridge' H hk hd)).smul (((p:ℝ)+1)*(q+1)/2)
 exact Cot.zero _ (by have hx:=h.gain; have hv:=H.gain; have he:=hk.near.gain; positivity)

/-- `W` lumps billed widths on this use into one input price including Γ first. Separately δ
can measure the cutoff power (also for Γ'). From degree e only charge strictly HIGHER input
rank for the nonlinear/heat correction (j>0). All comparisons simultaneous.
Polynomial absolute and difference fees BEFORE seeing the price W or diameter/moment width,
number of cells, period, scale, stage, types. -/
theorem navigation (j e n:ℕ):∃ P:ℝ→ℝ, Wage P ∧
 ∀ {I:Type}(d:Ground I)(σ δ W:ℝ)(V V':Grain I)(Γ Γ':Forms.Line I), Eligible V→Eligible V'→ WireCot d σ δ W Γ Γ'→ 0≤δ → 1≤W →
 (∀ a r,taps j e n a r→Cot d σ δ W (V a r) (V' a r)) →
 Cot d σ δ (P W) (burn Γ V j e n) (burn Γ' V' j e n):=by
 induction j using Nat.strong_induction_on generalizing e n with
 | h j ih=> cases j with
   | zero=>
     refine ⟨_,Wage.input,?_⟩
     intro I d σ δ W V V' Γ Γ' hv hv' _ _ hW h
     rw [spark,spark]
     have he:0≤W:=zero_le_one.trans hW
     by_cases hs:n=0
     · subst hs;exact Cot.scalar _ he
     by_cases hy:e=0
     · subst hy;rw [hv.dark,hv'.dark];exact Cot.zero _ he
     by_cases hf:n≤e+2
     · apply h; unfold taps;omega
     have hx {V : Grain I}(hv:Eligible V):V e n=0:=Classical.not_not.mp fun h=> hf (hv.head _ _ h)
     rw [hx hv,hx hv'];exact Cot.zero _ he
   | succ j=>
     obtain ⟨P,hP,HP⟩:=ih j (by omega) e (n+2)
     -- choose Q indexed by i mod small to avoid dependent subtype
     have U (i b k:ℕ):=ih (min i j) (by omega) b k
     choose Q hQ HQ using U
     let N (x:ℝ):ℝ:= (((n:ℝ)+2)*(n+1)/2)*(2*P x*x)
     let R (x:ℝ)(c i a:ℕ):ℝ:=((c:ℝ)+1)*((↑(n-c):ℝ)+1)/2*(3*(Q i a (c+1) x*x*Q (j-i) (e-a) (n-c+1) x))
     let S(x:ℝ):=∑ c∈range (n+1),∑ i∈range (j+1),∑ a∈range (e+1),R x c i a
     have hN : Wage N:= (Wage.constant _ (by positivity)).mul (((Wage.constant (2:ℝ) (by positivity)).mul hP).mul Wage.input)
     have hR (c i a:ℕ):Wage (fun x=> R x c i a):=(Wage.constant _ (by positivity)).mul ((Wage.constant (3:ℝ) (by positivity)).mul (((hQ i a _).mul Wage.input).mul (hQ (j-i) ..)))
     have hS : Wage S:= Wage.sum _ _ fun c _=> Wage.sum _ _ fun i _=> Wage.sum _ _ fun a _=> hR c i a
     refine ⟨_,(Wage.constant |((j+1:ℝ)⁻¹)| (abs_nonneg _)).mul (hN.add hS),?_⟩
     intro I d σ δ W V V' Γ Γ' hv hv' hΓ hd hW h
     rw [blaze,blaze]; apply Cot.smul; unfold wheels
     apply Cot.add (coupon_lap (HP _ _ _ _ _ _ _ _ hv hv' hΓ hd hW (fun a b he=>h _ _ ?_)) hΓ hd)
     · apply Cot.sum _ _ _ _ (fun c hc=> ?_) hd
       apply Cot.sum _ _ _ _ (fun i hi=>?_) hd
       refine Cot.sum _ _ _ _ (fun a ha=> ?_) hd
       have hb:i≤j:=by simpa [Nat.lt_succ_iff] using hi
       have hz:a≤e:=by simpa [Nat.lt_succ_iff] using ha
       have hr (b c k:ℕ)(he:b≤j)(hu:c<e): Cot d σ δ (Q b c k W) (burn Γ V b c k) (burn Γ' V' b c k):=by
         have := HQ b c k d σ δ W V V' Γ Γ' hv hv' hΓ hd hW (fun a r ht=>h _ _ (taps_side hu ht))
         simpa [min_eq_left he] using this
       have hh {V:Grain I}(hv:Eligible V)(Γ)(i k:ℕ):burn Γ V i 0 k=0:= by rw [(live hv i).dark];rfl
       by_cases he:a=0
       · subst he; simp_rw [hh hv,hh hv',pair_zero_left]; exact Cot.zero _ ((hR c i 0).nn hW)
       by_cases he':e-a=0
       · rw [he',hh hv,hh hv',pair_zero_right,pair_zero_right]; exact Cot.zero _ ((hR c i a).nn hW)
       exact coupon_pair (hr i a (c+1) hb (by omega)) (hr (j-i) (e-a) (n-c+1) (by omega) (by omega)) hΓ hd
     · exact hd
     unfold taps at *;omega

def Residual (e n a r:ℕ) := taps 1 e n a r
/-- Connected propagation off the linear diagram. Uses strictly lower positive g-degrees
or same g-degree with strictly greater field rank. -/
theorem postage (e n:ℕ) : ∃ P,Wage P ∧
 ∀ {I:Type}(d:Ground I)(σ δ W t:ℝ)(V V':Grain I)(Γ Γ':Forms.Line I), Eligible V→Eligible V'→ WireCot d σ δ W Γ Γ'→ 0≤δ → 1≤W → |t|≤W →
 (∀ a r,Residual e n a r→Cot d σ δ W (V a r) (V' a r))→
 Cot d σ δ (P W) (cinder Γ V t e n) (cinder Γ' V' t e n):=by
 choose P hP HP using (fun j=>navigation (j+1) e n)
 let f(j:ℕ)(x:ℝ):= x^(j+1)*P j x
 have hw (j):Wage (f j):=(show Wage (fun (x:ℝ)=>x^(j+1)) from ⟨1,j+1,by linarith,fun x hx=>⟨by dsimp only; exact pow_nonneg (show 0≤x by linarith) _,by simp⟩⟩).mul (hP j)
 refine ⟨_,Wage.sum (range (3*e)) f (fun i _=>hw i),?_⟩
 intro I d σ δ W t V V' Γ Γ' hv hv' hΓ hd hW ht h
 apply Cot.sum _ _ _ _ ?_ hd
 intro j _
 refine ((HP j _ σ δ W V V' Γ Γ' hv hv' hΓ hd hW (fun a r hz=>h a r ?_)).smul _).mono le_rfl ?_ hd
 · unfold Residual taps; unfold taps at hz;omega
 unfold f;rw [abs_pow];gcongr;exact (hP j).nn hW
end YM.RG08.Steam
