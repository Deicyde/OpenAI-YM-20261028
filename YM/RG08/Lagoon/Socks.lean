import YM.RG08.Jetty.Chests
import YM.Planned.PRIMARY_INTEGRAL_295.Carrier
import YM.Work.G05.Taylor

/-!
# Test transfer in the prescribed addresses, before profile testing, TPS
positive height. Payload prelength. f0 estimates through requested d
without *analytic radius* wrt g.
-/
noncomputable section
namespace YM.RG08.Lagoon
open Jetty Laurent Function Finset Lattice Pert.Bulk Planned.PrimaryIntegral295
open Place Carrier
open scoped Topology BigOperators Classical ContDiff RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n d:ℕ}{σ B:ℝ}{h:0<σ}

def aisle (a:ℝ)(x:E4): Pearl→ₗ[ℝ] Pearl where
 toFun f := ⟨f.val ∘ (fun w=>a • w+x), HasTemperateGrowth.comp (show HasTemperateGrowth _ from f.property) (show HasTemperateGrowth ((fun _:E4=>a) • (⇑(ContinuousLinearMap.id ℝ E4):E4→E4) +(fun _=>x)) from ((HasTemperateGrowth.const a).smul (ContinuousLinearMap.id ℝ E4).hasTemperateGrowth).add (HasTemperateGrowth.const _))⟩
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def bead (a:ℝ)(_M:ℕ)(f:Pearl):=aisle a 0 f
lemma reborn {a:ℝ}{x u:E4}(f:Pearl)(n:ℕ):iteratedFDeriv ℝ n ((aisle a x f).val) u=a^n • iteratedFDeriv ℝ n f.val (a • u + x):=by
 let v:Pearl:=aisle 1 x f
 have hv:v.val=fun z=> f.val (z+x):=by funext z;change f.val (1 • z+x)=_;rw [one_smul]
 rw [show (aisle a x f).val=(fun z=> v.val (a • z)) from by rw [hv];rfl,iteratedFDeriv_comp_const_smul _ (v.order _),hv]
 change a^n • iteratedFDeriv ℝ n (fun z=>f.val (z+x)) (a • u) = _
 rw [iteratedFDeriv_comp_add_right]
lemma purse_cast {u:E4}(a:ℝ)(x:E4)(s:Jet d)(f:Pearl):openJet s u (aisle a x f)=a^s.1.val * openJet s (a • u+x) f:=by unfold openJet loot; dsimp only [LinearMap.coe_mk,AddHom.coe_mk];rw [reborn];rfl
lemma spending {τ:ℝ}(k:0<τ)(b:E4)(a:ℝ)(ha:|a|≤1)(hs:τ*|a| ≤ σ)(f:Pearl):
    beam d h (aisle a b f) ≤ beam d k f * Real.exp (τ*‖b‖) :=by
 apply beam_le; exact mul_nonneg (beam_nn ..) (Real.exp_pos _).le
 intro i x
 rw [purse_cast,abs_mul,abs_pow]
 apply ((mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) ha)).trans (beam_opens d k f i _)).trans
 rw [mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (beam_nn ..);apply Real.exp_le_exp.mpr
 have hz:‖a • x+b‖≤ |a| *‖x‖+‖b‖:=by simpa [norm_smul,Real.norm_eq_abs] using norm_add_le (a • x) b
 nlinarith only [k,hz,hs,norm_nonneg x]

lemma normJet (d:ℕ){K:Tensor.T E4 ℝ d}(A:ℝ)(hA:0≤A)(ha:∀ i:Cargo d,‖K (basis ∘ i)‖≤ A):‖K‖≤ 4^d * A:=by
 apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hA)
 intro x
 have he : K x=∑ i:Cargo d,(∏ j,x j (i j))•K (basis ∘ i):=by
    calc
      K x = K (fun j=>∑ k:Axis,x j k • basis k) :=
        congrArg K (funext fun j=>by ext i;simp)
      _ = _ := by
        rw [K.map_sum]; apply sum_congr rfl;intro i _
        exact K.map_smul_univ (fun j=>x j (i j)) (fun j=>basis (i j))
 rw [he];apply (norm_sum_le ..).trans
 apply (sum_le_sum (g:=fun (_:Cargo d)=> (∏ j,‖x j‖)*A) (fun i (_:i∈(univ:Finset (Cargo d)))=>?_)).trans_eq
 · have hc : Fintype.card (Cargo d) = 4^d := by
     change Fintype.card (Fin d → Fin 4) = 4^d
     simp only [Fintype.card_fun,Fintype.card_fin]
   simp only [sum_const,card_univ,nsmul_eq_mul,hc,Nat.cast_pow,Nat.cast_ofNat]
   ring
 rw [norm_smul,Real.norm_eq_abs,Finset.abs_prod]
 refine mul_le_mul (prod_le_prod (fun j _=> abs_nonneg _) (fun j _=>?_)) (ha i) (norm_nonneg _) (prod_nonneg (fun i _=>norm_nonneg _))
 rw [← YM.basis_inner];simpa only [basis_norm,one_mul] using abs_real_inner_le_norm (basis (i j)) (x j)

lemma vault (k:Fin (d+1))(f:Pearl)(x:E4):‖iteratedFDeriv ℝ (k:ℕ) f.val x‖≤4^(k:ℕ)*(beam d h f * Real.exp (σ*‖x‖)):=normJet k _ (mul_nonneg (beam_nn ..) (Real.exp_pos _).le) (fun i=>by rw [Real.norm_eq_abs];exact beam_opens _ _ _ ⟨k,i⟩ x)

def profile (i:Cargo n)(x:E4):ℝ:=∏ j,x (i j)
def pal (i:Cargo n):Pearl:=by
  refine ⟨profile i,?_⟩
  have hcoord (j:Fin n) : HasTemperateGrowth (fun x:E4=>x (i j)) := by
    simpa only [YM.basis_inner] using
      (Function.hasTemperateGrowth_inner_right (basis (i j)))
  have hprod (s:Finset (Fin n)) :
      HasTemperateGrowth (fun x:E4=>∏ j∈s,x (i j)) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.prod_empty] using
          (HasTemperateGrowth.const (E:=E4) (1:ℝ))
    | @insert j s hjs ih =>
        have hh := (hcoord j).mul ih
        change HasTemperateGrowth (fun x:E4=>x (i j) * (∏ k∈s,x (i k))) at hh
        simpa only [Finset.prod_insert hjs] using hh
  exact hprod Finset.univ

lemma diagonal (K:Tensor.T E4 ℝ n)(x:E4): Tensor.diagonal K x =∑ i:Cargo n,(K (basis ∘ i)) * ((pal i).val x):=by
 have hx:(fun _:Fin n=>x)=(fun _:Fin n=>∑ i:Axis,x i • basis i):= _root_.funext fun j=>by ext i;simp
 unfold Tensor.diagonal;rw [hx,K.map_sum (fun _ i=>x i • basis i)]
 apply sum_congr rfl; intro i _
 rw [K.map_smul_univ (fun j=> x (i j)) (fun j=> basis (i j)),smul_eq_mul,mul_comm];rfl

def spokes (n:ℕ)(x:E4)(f:Pearl):Pearl:=∑ i:Cargo n, (Tensor.coeff (aisle 1 x f).val n 0 (basis ∘ i)) • pal i
def partialW (d:ℕ)(x:E4)(f:Pearl):Pearl:= ∑ i∈range (d+1), spokes i x f
lemma spoke_read (n:ℕ)(x:E4)(f:Pearl): (spokes n x f).val=Tensor.diagonal (Tensor.coeff (aisle 1 x f).val n 0):=by
 funext y;rw [diagonal]
 simp_rw [spokes,Submodule.coe_sum,Finset.sum_apply,Submodule.coe_smul_of_tower,Pi.smul_apply,smul_eq_mul] -- simp lemma check
lemma partialV (f:Pearl)(x:E4)(d:ℕ):(partialW d x f).val=Work.G05.blockTaylor d (aisle 1 x f).val:=by simp only [partialW,Submodule.coe_sum,spoke_read,Work.G05.blockTaylor]
lemma piecewise (f:Pearl)(s:Cargo n)(x:E4): Tensor.coeff (aisle 1 x f).val n 0 (basis ∘ s)=(n.factorial:ℝ)⁻¹*loot s x f :=by -- replace
 unfold Tensor.coeff loot;rw [reborn,smul_zero,zero_add,one_pow,one_smul];rfl
end YM.RG08.Lagoon
