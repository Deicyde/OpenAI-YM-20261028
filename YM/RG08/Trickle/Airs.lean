import YM.RG08.Trickle.Triangle

/-! # Time PDE, all degree, signed clocks. -/
noncomputable section
namespace YM.RG08.Trickle
open Function Finset PowerSeries Forms Steam Jetty Skiff Glyph Cloud
open scoped BigOperators Topology PowerSeries Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {R I:Type} [Fintype I]
variable [CommRing R][Algebra ℝ R](K:I→I→ℝ)

/-- K uses /2 here as in HJ slab. -/
def lerp (D:Cloud.Gauge I R)(v u:R):R:=∑ i,∑ j,(2*K i j) • (D i u * D j v)

/-- Formal product rule in charge convention. -/
theorem slab_second (D:Cloud.Gauge I R)(h:∀ i j,K i j=K j i)(v u:R) : slab K D (v*u)=slab K D v *u+v*slab K D u+lerp K D v u :=by
 let c(i j:I):=K i j • (D i u * D j v)
 let T:=∑ i,∑ j,c i j
 have he (i j:I) : K i j • D i (D j (v*u))=(K i j • D i (D j v))*u+(v*(K i j • D i (D j u)))+c i j+c j i:=by
   rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,Derivation.leibniz,Derivation.leibniz];unfold c
   rw [h j i]; simp only [smul_eq_mul,Algebra.smul_def]; ring
 have hh:∑ i,∑ j,c j i=T:=Finset.sum_comm
 rw [slab_do,slab_do,slab_do]; unfold lerp
 simp_rw [he,sum_add_distrib,hh,Finset.sum_mul,Finset.mul_sum,two_mul,add_smul,Finset.sum_add_distrib]
 change (( _+_)+T)+T=_+_+(T+T); abel

variable {K}
structure Note (D:Cloud.Gauge I R)(K:I→I→ℝ)(V F:Season R) : Prop where
 wind : flight (pendulum R) F=slab K (season D) F + lerp K (season D) V F

variable {V F:Season R}{D:Cloud.Gauge I R}
lemma Note.heat (hK:∀ i j,K i j=K j i)(h:Clockwise D K V)(hf:Note D K V F):flight (pendulum R) (rise V * F)=slab K (season D) (rise V * F):=by
 rw [Derivation.leibniz,h.linear,hf.wind,smul_eq_mul,smul_eq_mul,slab_second K (season D) hK,mul_add]
 have he : rise V * lerp K (season D) V F=lerp K (season D) (rise V) F:=by
    unfold lerp season; simp_rw [Finset.mul_sum,mul_smul_comm,lift_rise _ h.cold];apply sum_congr rfl; intro i _;apply sum_congr rfl;intro j _; congr 1;ring
 rw [he];ring
lemma Note.stamp (hK:∀ i j,K i j=K j i)(h:Clockwise D K V)(hf:Note D K V F)(e j:ℕ) : takeoff (rise V * F) e j=rfactor j • ((slab K D)^[j] (takeoff (rise V * F) e 0)):=by
 induction j with
 | zero=>simp [rfactor]
 | succ j ih=>
    have he:(j+1:ℝ)≠0:=by positivity
    apply untangle he
    rw [←dial,hf.heat hK h,observe,ih,Function.iterate_succ_apply',smul_smul,earns]
    exact (slab K D).map_smul ..

variable {l:ℕ}{Γ:Forms.Line I}{P:Steam.Grain I}{S:GrainS I}

def flows (l:ℕ)(Γ:Forms.Line I)(P:Steam.Grain I)(S:GrainS I)(f:Pearl) : Season (Inn I):=PowerSeries.mk (fun e=>∑ j∈range (l+3*e+1),Polynomial.monomial j (shine l (skate Γ P S j) f e))
def mark (l:ℕ)(S:GrainS I)(f:Pearl):PowerSeries (Inn I):=PowerSeries.mk (shine l S f)

lemma overheat (hp:Eligible P)(hs:Lit l S)(f:Pearl)(e j:ℕ)(hj:l+3*e<j):shine l (skate Γ P S j) f e=0:=by
 have he(n:ℕ):skate Γ P S j e n=0:=Classical.not_not.mp fun h=>by have :=(full hs hp h).1;omega
 unfold shine brook during; simp_rw [he,Pi.zero_apply]
 change ∑ n∈range _,parley (0:Flake n I)=0; simp only [parley_zero,sum_const_zero]
lemma earning (hp:Eligible P)(hs:Lit l S)(f:Pearl)(e j:ℕ) : takeoff (flows l Γ P S f) e j=shine l (skate Γ P S j) f e:=by
 rw [flows,takeoff,PowerSeries.coeff_mk,Polynomial.finsetSum_coeff]; simp_rw [Polynomial.coeff_monomial, Finset.sum_ite_eq'];split_ifs with h
 · rfl
 rw [overheat hp hs f _ _ (by simp only [mem_range] at h;omega)]
lemma sunrise (hp:Eligible P)(hs:Lit l S)(f:Pearl)(t:ℝ) : summer t (flows l Γ P S f) = Trickle.mark l (spin l Γ P S t) f:=by
 ext e
 rw [summer_range _ (l+3*e) _ _ (fun i hi=>?_),Trickle.mark,PowerSeries.coeff_mk]
 · unfold Skiff.spin; simp_rw [earning hp hs,shine,brook,during_sum,during_smul,parley_sum,parley_smul,Finset.smul_sum]; rw [Finset.sum_comm]
 rw [earning hp hs,overheat hp hs _ _ _ (by omega)]
lemma flare (hp:Eligible P)(hs:Lit l S)(f:Pearl):summer 0 (flows l Γ P S f)=Trickle.mark l S f:=by
 ext e;rw [summer_initial,earning hp hs,Skiff.start,Trickle.mark,coeff_mk]

omit [Fintype I] in
private lemma film (f g:Season (Inn I))(e j:ℕ) : takeoff (f*g) e j= (∑ t∈range (j+1),∑ a∈range (e+1), takeoff f a t * takeoff g (e-a) (j-t)):=by
 unfold takeoff;rw [PowerSeries.coeff_mul,Polynomial.finsetSum_coeff]
 simp_rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
 exact Finset.sum_comm

/-- Symbol clocks computed directly at all degrees of g. -/
theorem notes (hp:Eligible P)(hs:Lit l S)(hP:waxed P)(hS:Combed S)(hΓ:∀ i j,Γ i j=Γ j i)(f:Pearl):
   Note (axes I) (half Γ) (Glyph.kernel Γ P) (flows l Γ P S f):=by
 constructor
 ext e j:2
 change takeoff _ e j=takeoff _ e j
 rw [dial,take_add,observe]; unfold lerp
 simp_rw [take_sum,take_smul,film,watch, Finset.smul_sum,earning hp hs,window hp]
 conv_lhs=> rw [shine]
 let N:=l+e+1; let S'(i:ℕ):=skate Γ P S i
 let P'(i:ℕ):=burn Γ P i
 let M(x y:I)(i a:ℕ):= (2* half Γ x y) • (axes I x (shine l (S' i) f a)*axes I y (showV (P' (j-i)) (e-a)))
 have hj:(j+1:ℝ)≠0:=by positivity
 simp_rw [rushing,parley_smul,Finset.smul_sum,smul_smul,mul_inv_cancel₀ hj,one_smul,parley_add,Finset.sum_add_distrib,parley_sum]
 rw [timid _ (comb Γ _ hS j) (drink hs hp) _ hΓ e f]; congr 1
 change (∑ n∈range N,∑ c∈range (n+1),∑ i∈_,∑ a∈_,parley ((2:ℝ) • pair _ (brook f (S' i) a (c+1)) (P' (j-i) (e-a) (n-c+1)) n))=∑ x,∑ y,∑ i∈range (j+1),∑ a∈range (e+1), M x y i a
 rw [Glyph.square _ _ _ _ M]
 refine Eq.trans (b:=∑ i∈range (j+1), ∑ a∈range (e+1),∑ n∈range N,∑ c∈range (n+1),parley ((2:ℝ) • pair Γ (brook f (S' i) a (c+1)) (P' (j-i) (e-a) (n-c+1)) n)) ?_ (Finset.sum_congr rfl fun i hi=>Finset.sum_congr rfl fun a ha =>?_)
 · rw [show (∑ n∈range N,∑ c∈range (n+1),∑ i∈range (j+1),∑ a∈ range (e+1),parley ((2:ℝ) • pair Γ (brook f (S' i) a (c+1)) (P' (j-i) (e-a) (n-c+1)) n))=∑ n∈range N,∑ i∈range (j+1), ∑ a∈range (e+1),∑ c∈range (n+1),parley ((2:ℝ) • pair Γ (brook f (S' i) a (c+1)) (P' (j-i) (e-a) (n-c+1)) n) from ?_,Finset.sum_comm]; apply sum_congr rfl; intro i _;exact Finset.sum_comm
   apply sum_congr rfl; intro n _; rw [Finset.sum_comm];apply sum_congr rfl;intro i _;exact Finset.sum_comm
 have hb:a≤e:=by simpa [Nat.lt_succ_iff] using ha
 have hn:N=l+(a+(e-a))+1:=by dsimp [N];omega
 rw [hn,joint _ (comb Γ P hS i) (drink hs hp) _ (waxed_burn hP _ _) (live hp _) _ a (e-a) f]
 apply Finset.sum_congr rfl; intro x _;apply Finset.sum_congr rfl;intro y _;unfold M; congr 1; unfold half;ring
end YM.RG08.Trickle
