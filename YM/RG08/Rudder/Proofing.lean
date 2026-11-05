import YM.RG08.Rudder.Pier
import YM.RG08.Isles.Shores

noncomputable section
namespace YM.RG08.Rudder
open scoped Topology BigOperators Classical ENNReal
open Forms Finset Function Exterior AnalyticNext.QuarticMatch.BoxChain Pert.Bulk Lattice Laurent
set_option autoImplicit false
variable {I:Type}{n:ℕ}{σ C:ℝ}{A:Raw I n}

/- Pointwise bound at stamp form diameter. -/
def dim (n:ℕ)(I:Type)(σ:ℝ)(x:Tape n (Market I)):=Real.exp (σ*(carpet I).radius x)
lemma NextTo.fade (h:NextTo A σ C)(hn:0<n)(x:Tape n (Market (Tone I))): |A x| * dim n _ σ x ≤ C:=by
 let y(i:Fin n):=((x i).1,(x i).2.1);let z(i:Fin n):=(x i).2.2
 have H (i j:Fin n): |A x| ≤ C*Real.exp (-σ*(carpet (Tone I)).span (x i) (x j)):=by
   change _ ≤ C*cost σ (x i).1 (x j).1
   rw [←Real.norm_eq_abs]; exact (h z).each y i j
 obtain hh|hh:=mem_insert.mp (show (carpet (Tone I)).radius x∈Ground.paper _ x from Finset.max'_mem ..)
 · unfold dim; rw [hh]
   let i:Fin n:=⟨0,hn⟩
   simpa [(carpet (Tone I)).stay] using H i i
 obtain ⟨⟨i,j⟩,_,hh⟩:=mem_image.mp hh
 unfold dim
 rw [←hh]
 have he:Real.exp (-σ*(carpet (Tone I)).span (x i) (x j))=(Real.exp (σ*(carpet (Tone I)).span (x i) (x j)))⁻¹:=by rw [neg_mul,Real.exp_neg]
 have ht:=H i j; rw [he,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)] at ht;exact ht

variable [Fintype I]

private lemma decay_norm (η:ℝ)(h:0<η)(z:Cover):
 ∑' x:Market I, ENNReal.ofReal (Real.exp (-η*sep x.1 z)) ≤ ENNReal.ofReal (Fintype.card I * (AnalyticNext.QuarticMatch.BoxChain.bill η)):=by
 have he:=accounted z h
 rw [ENNReal.tsum_prod'];simp_rw [tsum_fintype,sum_const,card_univ,nsmul_eq_mul,ENNReal.tsum_mul_left]
 rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
 rw [ENNReal.ofReal_natCast]
 apply mul_le_mul_right ?_ _ -- nat cast ?
 change ∑' x,ENNReal.ofReal (cost η x z) ≤ _
 rw [← ENNReal.ofReal_tsum_of_nonneg he.1 he.2.1];exact ENNReal.ofReal_le_ofReal he.2.2

def debit' (I:Type)[Fintype I] (n:ℕ)(σ:ℝ):ℝ:=(Fintype.card I * AnalyticNext.QuarticMatch.BoxChain.bill (σ/(3*(n:ℝ))))^n
lemma debit'_nn (hs:0<σ)(hn:0<n) : 0≤debit' I n σ:=pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (billed (by have:(0:ℝ)<n:=Nat.cast_pos.mpr hn;positivity)).le) n

/-- Convert pointwise decay (as in the same snapshot's BoxChain.Pricing) into all-roots
analytic norm. -/
lemma regain {F:Flake n (Market I)}(hn:0<n)(hs:0<σ)(hc:0≤C)(hf:∀ x, |F x| * dim n _ σ x ≤ C): Held (carpet I) (σ/2) (debit' I n σ*C) F:=by
 let V:=carpet I
 let η:=σ/(3*(n:ℝ)); have hx:(0:ℝ)<n:=Nat.cast_pos.mpr hn;have hp:0<η:=by unfold η; positivity
 let B:ℝ:=Fintype.card I * AnalyticNext.QuarticMatch.BoxChain.bill η;have hb:0≤B:=mul_nonneg (Nat.cast_nonneg _) (billed hp).le
 rw [ensign];intro i z
 let d (x:Market I):= Real.exp (-η*V.span x z)
 have ht(x:Tape n (Market I)): Forms.row (mark V (σ/2) F) i z x ≤ ENNReal.ofReal C * ∏ i, ENNReal.ofReal (d (x i)):=by
   unfold row;split_ifs with he
   · have hh:∀ S:Finset (Fin n),ENNReal.ofReal (∏ i∈S,d (x i))=∏ i∈S,ENNReal.ofReal (d (x i)):=by intro S; induction S using Finset.induction_on with
     | empty=>simp
     | insert a s ha ih=>rw [prod_insert ha,prod_insert ha,ENNReal.ofReal_mul (Real.exp_pos _).le,ih]
     rw [←hh,←ENNReal.ofReal_mul hc];apply ENNReal.ofReal_le_ofReal
     apply le_trans ?_ (mul_le_mul_of_nonneg_right (hf x) (show 0≤∏ i,d (x i) from by unfold d; exact Finset.prod_nonneg fun _ _=>(Real.exp_pos _).le)) -- signature?
     unfold d dim; rw [show |F x| * Real.exp _ * _= |F x| *(Real.exp (σ*V.radius x)*∏ a:Fin n,Real.exp (-η*V.span (x a) z)) by rw [←mul_assoc],←Real.exp_sum, ←Real.exp_add]
     have he':σ*V.radius x/2 + η*∑ a,V.span (x a) z ≤ σ*V.radius x:=by
       have hv:(∑ a,V.span (x a) z)≤ (n:ℝ)*V.radius x:=by
          have := Finset.sum_le_sum (s:=univ) (fun j (_:j∈univ)=> show V.span (x j) z ≤ V.radius x from he ▸ V.le_radius x j i)
          simpa using this
       have hb':η*(n:ℝ)=σ/3:=by unfold η;field_simp
       have hz:=mul_le_mul_of_nonneg_left hv hp.le; rw [←mul_assoc,hb'] at hz
       nlinarith [V.radius_nn x]
     rw [←Finset.mul_sum];apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _);linarith
   exact zero_le
 unfold debit'
 apply (ENNReal.tsum_le_tsum ht).trans
 rw [ENNReal.tsum_mul_left,all_Δ (a:=fun (_:Fin n) x=>ENNReal.ofReal (d x))]
 have he': ∏ _:Fin n, (∑' x,ENNReal.ofReal (d x))≤ ENNReal.ofReal B ^ n:=by
    simp only [prod_const,card_univ,Fintype.card_fin];gcongr;exact decay_norm η hp z.1
 rw [mul_comm]; apply le_trans (mul_le_mul_left he' _) ?_
 rw [←ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul (pow_nonneg hb n)]

lemma NextTo.held (h:NextTo A σ C)(hn:0<n)(hc:0≤C)(hs:0<σ): Held (carpet (Tone I)) (σ/2) (debit' (Tone I) n σ*C) A:=regain hn hs hc (h.fade hn)
end YM.RG08.Rudder
