import YM.RG08.Glyph.Towers

/-! Finite-volume rank stencil recursion solves nonlinear PDE. -/
noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Cloud Finset Function MvPolynomial
open scoped BigOperators Topology Classical PowerSeries
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}[Fintype I]{Γ:Line I}{V:Grain I}

def kernel (Γ:Line I)(V:Grain I):Season (Inn I):= PowerSeries.mk (fun e=>∑ j∈range (3*e+1), Polynomial.monomial j (showV (burn Γ V j) e))
def stock (V:Grain I):PowerSeries (Inn I):=PowerSeries.mk (showV V)

lemma window (hV:Eligible V)(e j:ℕ):takeoff (kernel Γ V) e j=showV (burn Γ V j) e:=by
 rw [kernel,takeoff,PowerSeries.coeff_mk,Polynomial.finsetSum_coeff];simp_rw [Polynomial.coeff_monomial,Finset.sum_ite_eq'];split_ifs with h
 · rfl
 unfold showV
 simp_rw [show ∀ n,burn Γ V j e n=0 from fun n=>Steam.off hV j e n (by simp only [mem_range] at *;omega),parley_zero,sum_const_zero]

lemma frozen (hV:Eligible V):tiny (kernel Γ V):=by
 unfold tiny;ext j:1
 rw [Polynomial.coeff_zero]; change takeoff _ 0 j=0; rw [window hV]
 unfold showV;simp [(live hV _).dark, parley_zero]

lemma breaktime (hV:Eligible V)(t:ℝ):summer t (kernel Γ V)=stock (ember Γ V t):=by
 ext e
 rw [summer_range _ (3*e) _ _ (fun i hi=>?_)]
 · rw [stock,PowerSeries.coeff_mk]
   simp_rw [window hV,showV,ember,parley_sum,parley_smul,Finset.smul_sum]
   rw [ Finset.sum_comm]
 · rw [window hV]; unfold showV;simp_rw [show ∀ n, burn Γ V i e n=0 from fun n=>Steam.off hV i e n (by omega),parley_zero,sum_const_zero]

lemma morning (hV:Eligible V): summer 0 (kernel Γ V)=stock V:=by
 ext e;rw [summer_initial,window hV,spark,stock,PowerSeries.coeff_mk]

omit [Fintype I] in
private lemma take_mul (f g:Season (Inn I))(e j:ℕ) : takeoff (f*g) e j= (∑ t∈range (j+1),∑ a∈range (e+1), takeoff f a t * takeoff g (e-a) (j-t)):=by
 unfold takeoff;rw [PowerSeries.coeff_mul,Polynomial.finsetSum_coeff]
 simp_rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
 exact Finset.sum_comm

theorem cloudy (hV:Eligible V)(h:waxed V)(hΓ:∀ i j,Γ i j=Γ j i):Clockwise (axes I) (half Γ) (kernel Γ V):=by
 let K:=half Γ
 let f:=kernel Γ V
 let E:=axes I
 let B:=burn Γ V
 change Clockwise E K f
 refine ⟨frozen hV,?_⟩
 ext e j :2
 change takeoff _ e j=takeoff _ e j
 rw [dial,take_add,observe]; unfold Cloud.join
 simp_rw [take_sum,take_smul,take_mul,watch]
 unfold f
 simp_rw [window hV, Finset.smul_sum]
 have hj (i:ℕ):0<(i+1:ℝ):=by positivity
 have hat:B (j+1) e=fun n=>((j+1:ℝ)⁻¹) • wheels Γ B j e n:=funext fun n=>blaze ..
 let N(i r:I)(t a:ℕ):=K i r • (E i (showV (B t) a)* E r (showV (B (j-t)) (e-a)))
 change (j+1:ℝ) • showV (B (j+1)) e = slab K E (showV (B j) e) + ∑ i,∑ r,∑ t∈range (j+1),∑ a∈range (e+1),N i r t a
 conv_lhs => rw [showV]
 simp_rw [hat,wheels,parley_smul,Finset.smul_sum,smul_smul,mul_inv_cancel₀ (ne_of_gt (hj j)),one_smul,parley_add, Finset.sum_add_distrib,parley_sum]
 rw [gentle (B j) (waxed_burn h _ j) (live hV j) Γ hΓ e]
 congr 1
 rw [square _ _ _ _ N]
 refine Eq.trans (b:=∑ i∈range (j+1),∑ a∈range (e+1),∑ n∈range (e+3),∑ c∈range (n+1),parley (pair Γ (B i a (c+1)) (B (j-i) (e-a) (n-c+1)) n)) ?_ (Finset.sum_congr rfl fun i hi=>Finset.sum_congr rfl fun a ha =>?_)
 · -- reorder LHS with variable (n+1) c sum
   rw [show (∑ n∈range (e+3),∑ c∈range (n+1),∑ t∈range (j+1),∑ a∈range (e+1),parley (pair Γ (B t a (c+1)) (B (j-t) (e-a) (n-c+1)) n))=
          ∑ n∈range (e+3),∑ t∈range (j+1),∑ a∈range (e+1),∑ c∈range (n+1),parley (pair Γ (B t a (c+1)) (B (j-t) (e-a) (n-c+1)) n) from ?_,Finset.sum_comm];apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
   apply sum_congr rfl;intro n _;rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _; exact Finset.sum_comm
 have hb:a≤e:=by simpa [Nat.lt_succ_iff] using ha
 have he:=quiet Γ a (e-a) (B i) (B (j-i)) (live hV i) (live hV (j-i)) (waxed_burn h _ _) (waxed_burn h _ _)
 rw [show a+(e-a)=e by omega] at he
 exact he
end YM.RG08.Glyph
