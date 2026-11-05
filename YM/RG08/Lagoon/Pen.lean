import YM.RG08.Lagoon.Socks
import YM.Contact.OrderLoss

/-!
# Analytic beam payload estimate with remainder address transformer,
paid through arbitrarily many hierarch iterations. f tested with reweighted bounded
derivatives; polynomials evaluated on MISS-F tails later. -/
noncomputable section
namespace YM.RG08.Lagoon
open Jetty Laurent Function Finset Lattice Pert.Bulk Contacts
open scoped Topology BigOperators Classical ContDiff RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {s d n:ℕ}{σ τ B:ℝ}{h:0<σ}{k:0<τ}

def service (a:ℝ)(v:E4)(n:ℕ)(f:Pearl):= a^n • spokes n v f
def trail (a:ℝ)(v:E4)(s:ℕ)(f:Pearl):Pearl:= aisle a 0 (aisle 1 v f - partialW s v f)
lemma offload (n:ℕ)(a:ℝ)(v:E4)(f:Pearl):aisle a 0 (spokes n v f)=service a v n f:=by
 apply Subtype.ext;funext w
 change (spokes n v f).val (a • w+0)=a^n * (spokes n v f).val w
 rw [add_zero,spoke_read, YM.Tensor.homogeneous];rfl
lemma train (s:ℕ)(a:ℝ)(v:E4)(f:Pearl):
 aisle a v f=(∑ i∈range (s+1),service a v i f)+trail a v s f:=by
 unfold trail; rw [map_sub,partialW,map_sum];simp_rw [offload];rw [add_comm,sub_add_cancel];apply Subtype.ext;funext w; change _=f.val (1 • (a • w+0)+v); rw [add_zero,one_smul];rfl

lemma borne (s:Cargo n)(f:Pearl)(v:E4)(k:0<τ)(ht:‖v‖≤B)(hn:n≤d):
 |Tensor.coeff (aisle 1 v f).val n 0 (basis ∘ s)| ≤ (n.factorial:ℝ)⁻¹ * (beam d k f * Real.exp (τ*B)):=by
 rw [piecewise,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]; apply mul_le_mul_of_nonneg_left _ (by positivity)
 exact (beam_opens _ _ _ (⟨⟨n,by omega⟩,s⟩:Jet d) _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht k.le)) (beam_nn d k f))

/-- cost finite combination, polynomial budget C_y prototype or assembly. For each
input width σ and evaluation order d. -/
lemma spoken (h:0<σ)(k:0<τ)(B:ℝ)(n:ℕ)(d:ℕ)(hn:n≤d):∃ C:ℝ,1≤C ∧ ∀ (f:Pearl)(a:ℝ)(v:E4),‖v‖≤B→beam d h (service a v n f)≤ C * |a|^n * beam d k f:=by
 let M:=∑ i:Cargo n, beam d h (pal i)
 let A:= (n.factorial:ℝ)⁻¹ * Real.exp (τ*B);have ha:0 ≤ A:=mul_nonneg (by positivity) (Real.exp_pos _).le
 have hb:0 ≤ M:=sum_nonneg fun i _=>beam_nn ..
 refine ⟨A*M+1,le_add_of_nonneg_left (mul_nonneg ha hb),fun f a v hv=>?_⟩
 have ht : beam d h (spokes n v f) ≤ ∑ i:Cargo n,(A*beam d k f) * beam d h (pal i):=by
    unfold spokes beam;rw [map_sum];apply (norm_sum_le ..).trans;apply sum_le_sum; intro i _;rw [_root_.map_smul,norm_smul,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact (borne i f v k hv hn).trans_eq (by unfold A beam; ring)
 rw [← mul_sum] at ht
 change ‖gleam d h (a^n • spokes n v f)‖≤_
 rw [_root_.map_smul,norm_smul,Real.norm_eq_abs,abs_pow];apply le_trans (mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg _) _)); unfold M
 nlinarith [beam_nn d k f,pow_nonneg (abs_nonneg a) n,mul_nonneg ha hb]

-- derivative bound on the entire Taylor polynomial at arbitrary displaced point,
-- put in auxiliary positive exponential α *before* L. Simpler via beam estimate on spoke itself.
lemma ranked (h:0<σ)(k:0<τ)(B:ℝ)(d:ℕ):∃ C:ℝ,1≤C ∧ ∀ (f:Pearl)(v:E4)(s:ℕ),s≤d→‖v‖≤B→ (beam d h (partialW s v f)) ≤ C*beam d k f:=by
 choose C hC using fun i (hi:i≤d)=> spoken h k B i d hi
 let Z(i:ℕ):ℝ:=if h:i≤d then C i h else 0
 have hz(i:ℕ):0≤Z i:=by
    unfold Z;split
    · rename_i h;exact zero_le_one.trans (hC i h).1
    exact le_rfl
 refine ⟨(∑ i∈range (d+1),Z i)+1,le_add_of_nonneg_left (sum_nonneg fun i _=>hz i),fun f v s hs hv=>?_⟩
 let M:=beam d k f
 have ht : beam d h (partialW s v f)≤(∑ i∈range (s+1),Z i)*M:=by
    unfold beam partialW;rw [map_sum,sum_mul];apply (norm_sum_le ..).trans
    refine sum_le_sum (fun i hi=>?_)
    have hi' : i≤d:=by simp only [mem_range] at hi; omega
    have he:= (hC i hi').2 f 1 v hv; rw [service,one_pow,one_smul,abs_one,one_pow,mul_one] at he
    exact he.trans_eq (by unfold Z M;rw [dif_pos hi'])
 apply ht.trans; refine mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg (range_mono (show s+1≤d+1 by omega)) (fun i _ _=>hz i)).trans (le_add_of_nonneg_right zero_le_one)) (beam_nn ..)

private def Zed (f:Pearl)(v:E4)(s:ℕ):=aisle 1 v f - partialW s v f
lemma trailing (k:0<τ)(B:ℝ)(d:ℕ):∃ C:ℝ,1≤C ∧∀ (f:Pearl)(v:E4)(s:ℕ),s≤d→‖v‖≤B→beam d k (Zed f v s) ≤ C*beam d k f:=by
 obtain ⟨M,hM,ht⟩:=ranked k k B d
 refine ⟨M+Real.exp (τ*B),le_add_of_le_of_nonneg hM (Real.exp_pos _).le,fun f v s hs hv=>?_⟩
 unfold Zed
 calc
 _ ≤ beam d k (aisle 1 v f)+beam d k (partialW s v f):=by unfold beam;rw [map_sub];exact norm_sub_le ..
 _ ≤ _:=by
    have hx:=spending (d:=d) (h:=k) k v 1 (by simp) (by simp) f
    have he:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv k.le)
    have hb:=ht f v s hs hv
    nlinarith [beam_nn d k f]
-- derivative remainder has exact normalized zero before s
lemma tally (s:ℕ)(f:Pearl)(v:E4)(i:ℕ)(hi:i≤s):iteratedFDeriv ℝ i (Zed f v s).val 0=0:=by
 rw [show ↑(Zed f v s)= (aisle 1 v f).val-(partialW s v f).val from rfl, iteratedFDeriv_sub_apply ((aisle 1 v f).order _|>.contDiffAt) ((partialW s v f).order _|>.contDiffAt),partialV,Work.G05.blockTaylor_jets ((aisle 1 v f).order s|>.contDiffAt) _ hi,sub_self]

lemma withheld (k:0<τ)(h:0<σ)(B:ℝ)(d s:ℕ)(hd:s+1≤d):∃ C:ℝ,1≤ C ∧∀ (f:Pearl)(a:ℝ)(v:E4),|a|≤1→ τ*|a| ≤ σ/2 → ‖v‖≤B → beam d h (trail a v s f) ≤ C * |a|^(s+1) * beam d k f:=by
 obtain ⟨M,hM,hm⟩:=trailing k B d
 obtain ⟨u,hu,hw⟩:= cold (s+1) (show (0:ℝ)<σ/2 from half_pos h)
 have h4:(1:ℝ)≤4^d:=one_le_pow₀ (by norm_num)
 let D:= (4^d:ℝ)*M;have hD:1 ≤ D:= one_le_mul_of_one_le_of_one_le h4 hM
 refine ⟨D*(u+1),one_le_mul_of_one_le_of_one_le hD (le_add_of_nonneg_left hu),fun f a v ha he hv=>?_⟩
 let C:=beam d k f; have hC:0≤C:=beam_nn ..
 let F:=Zed f v s
 have hX : beam d k F≤M*C:=hm f v s (by omega) hv
 have hDen(i:ℕ)(hi:i≤d)(x:E4):‖iteratedFDeriv ℝ i F.val x‖≤D*C*Real.exp (τ*‖x‖):=by
    let q : Fin (d+1):= ⟨i,by omega⟩
    apply (show _ from vault (h:=k) q F x).trans
    unfold D
    have hb:=mul_le_mul_of_nonneg_right hX (Real.exp_pos (τ*‖x‖)).le
    have h4b:(4:ℝ)^q.val ≤ 4^d:=pow_le_pow_right₀ (by norm_num) hi
    change _*(_*_)≤_
    exact (mul_le_mul h4b hb (mul_nonneg (beam_nn ..) (Real.exp_pos _).le) (zero_le_one.trans h4)).trans_eq (by ring)
 let A:ℝ:=|a|;have hA:0≤A:=abs_nonneg _
 apply beam_le; change 0≤ (D*(_+_))*A^_*C; positivity
 intro z x
 let i:ℕ:=z.1.val; let r:=‖x‖; have hr:0≤r:=norm_nonneg _
 have hx: |openJet z x (trail a v s f)| ≤ A^i* ‖iteratedFDeriv ℝ i F.val (a • x)‖:=by
    unfold trail;rw [purse_cast,abs_mul,abs_pow,add_zero]; apply mul_le_mul_of_nonneg_left (opens_le _ _ _) (pow_nonneg (abs_nonneg _) _)
 refine hx.trans ?_
 change A^i * _≤ D*(u+1)*A^(s+1)*C*Real.exp (σ*r)
 have hi :i≤d:=by unfold i; omega -- supply z.1
 have ht : Real.exp (τ*‖a • x‖) ≤ Real.exp (σ/2*r):=by
    rw [norm_smul,Real.norm_eq_abs];apply Real.exp_le_exp.mpr; nlinarith only [he,hr,mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he) hr]
 by_cases hp:i≤s
 · let j:=s-i
   have hJ:j+i=s:=by dsimp only [j]; omega
   have hy := Contacts.norm_deriv_from_zero j i (x:=a • x) (B:=D*C*Real.exp (τ*‖a • x‖)) (f:=F.val) (F.order _) (fun l hl => tally s f v _ (by omega)) (by positivity) (fun y hy=> (hDen _ (by omega) y).trans (by gcongr)) -- gcongr τ nonneg needed
   apply le_trans (mul_le_mul_of_nonneg_left hy (pow_nonneg hA i))
   rw [norm_smul,Real.norm_eq_abs,mul_pow]
   have hb:=hw r hr
   unfold warp at hb; rw [Real.exp_neg,←div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)] at hb
   have hN:r^(j+1)≤u*Real.exp (σ/2*r):=((pow_le_pow_left₀ hr (le_add_of_nonneg_left zero_le_one) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right hr) (by omega:j+1≤s+1))).trans hb
   rw [norm_smul,Real.norm_eq_abs] at ht;change Real.exp (τ*(A*r))≤_ at ht
   change A^i*(A^(j+1)*r^(j+1)*(D*C*Real.exp (τ*(A*r))))≤_
   have hE:A^i * A^(j+1)=A^(s+1):=by rw [←pow_add,show i+(j+1)=s+1 by omega]
   calc
   _ ≤ A^i*(A^(j+1)*(u*Real.exp (σ/2*r))*(D*C*Real.exp (σ/2*r))):=by gcongr
   _ = D*u*A^(s+1)*C*(Real.exp (σ/2*r)*Real.exp (σ/2*r)):=by rw [←hE];ring
   _ ≤ _:=by rw [← Real.exp_add,show σ/2*r+σ/2*r=σ*r by ring];gcongr;exact le_add_of_nonneg_right zero_le_one
 apply le_trans (mul_le_mul_of_nonneg_left (hDen i hi _) (pow_nonneg hA i))
 calc
  _ ≤ A^(s+1)*(D*C*Real.exp (σ*r)):=by refine mul_le_mul (pow_le_pow_of_le_one hA ha (by omega)) (mul_le_mul_of_nonneg_left (ht.trans (Real.exp_le_exp.mpr ?_)) (by positivity)) (by positivity) (by positivity); nlinarith only [h,hr]
  _ ≤ D*(u+1)*A^(s+1)*C*Real.exp (σ*r):=by have hv:=mul_nonneg (mul_nonneg (pow_nonneg hA (s+1)) hC) (Real.exp_pos (σ*r)).le; nlinarith [mul_nonneg hu hv, mul_nonneg (zero_le_one.trans hD) (mul_nonneg hu hv)] -- annotate
end YM.RG08.Lagoon
