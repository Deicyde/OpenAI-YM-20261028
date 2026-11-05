import YM.RG08.Atrium.Shoe
/-! # Finitely many events in full ordered product book. No repeated gain needed
 on calibrated couplings, retention by exact head diagonal ≤1. Also works clock reexpression.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Atrium
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo Trill
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius PowerSeries Matrix
variable {I:Type} [Fintype I]{d n m e k:ℕ}{W B D:ℝ}
variable (H:Parade I d)

structure Day (H:Parade I d)(k:ℕ)(W:ℝ)(M:Sock I) :Prop where
 head : Ordered H (ink M)
 cheap (i:I): |ink M i i|≤1
 paid (i:ℕ)(hi:i≤k): post (dusk i M) W

-- RSI count and placement. Fold n as recursion.
def sun (M:ℕ→Sock I):ℕ→Sock I
 | 0=>1
 | i+1=>M i*sun M i
private lemma swapr {f:ℕ→ℝ}{n:ℕ}{D:ℝ}(he:f 0≤D)(h:∀ i<n,f (i+1)≤f i+B)(hm:0≤B):∀ i≤n,f i≤D+n*B:=by
 suffices ht:∀ i≤n,f i≤D+i*B from fun i hi=>(ht i hi).trans (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hm) _)
 intro i
 induction i with
 | zero=>simpa using he
 | succ i ih=>intro hi;refine (h i hi).trans ?_;push_cast;linarith only [ih (Nat.le_of_lt hi)]

def quota (H:Parade I d)(e:ℕ)(i:I):ℕ:= (turns d)*e+tick H i
-- `nB` W bounds full window, already post at entire length. names choose. costs around W≥ n & slots.
lemma corridor (hW:1≤W)(P:ℕ→Sock I)(hw:(n:ℝ)≤W)(hp:∀ i<n, Day H k W (P i))(e:ℕ)(i j:I)(he:e≤k) :
 |dusk e (sun P n) i j| ≤ (1+(k+1:ℝ)*(Fintype.card I:ℝ)*W^2)^(quota H e i+1):=by
 let C:ℝ:=Fintype.card I; have hC:0 ≤ C:=Nat.cast_nonneg _
 have hW':0 ≤ W:=by linarith
 let R:=1+(k+1:ℝ)*C*W^2; have hr:1 ≤ R:=le_add_of_nonneg_right (by positivity)
 suffices hs:∀ u:ℕ,∀ e≤k,∀ i j:I,quota H e i=u→∀ m≤n,|dusk e (sun P m) i j|≤R^(u+1) from hs _ e he i j rfl _ le_rfl
 intro u;induction u using Nat.strong_induction_on with
 | h u ih=>
    intro e he i j hq
    let f(t:ℕ):= |dusk e (sun P t) i j|
    let M:ℝ:= (k+1:ℝ)*C*W*R^u; have hm:0 ≤ M:=by unfold M;positivity [show 0 ≤ R from zero_le_one.trans hr]
    have hg:R^u ≥ 1:=one_le_pow₀ hr
    have hB:1+(n:ℝ)*M ≤ R^(u+1):=by
        rw [pow_succ]
        apply (add_le_add hg (mul_le_mul_of_nonneg_right hw hm)).trans
        unfold M; nlinarith only [show R-1=(k+1:ℝ)*C*W*W by unfold R;ring] -- nlinarith factors R^u
    suffices hs:∀ m≤n,f m≤1+(n:ℝ)*M from fun m ho=>(hs _ ho).trans hB
    apply swapr (B:=M) ?_ ?_ hm
    · unfold f;rw [sun,dusk_one];split_ifs; rw [Matrix.one_apply];split <;> norm_num;change |(0:ℝ)|≤1;norm_num
    intro m hm'
    rw [show f (m+1)=_ from congrArg (fun A:Sock I=> |dusk e A i j|) (show sun P (m+1) =P m * sun P m from rfl),dusk_mul,Matrix.sum_apply]
    simp_rw [Matrix.mul_apply]
    -- isolate self e=0 M_i term, previous f. others ≤ W*R^u by induction
    let g(b:ℕ)(c:I):=dusk b (P m) i c*dusk (e-b) (sun P m) c j
    let V(b:ℕ)(c:I):=if b=0∧ c=i then f m else 0
    have hL(b:ℕ)(a:I)(hb:b≤e): |g b a| ≤ W*R^u+V b a:=by
        by_cases hx:b=0∧a=i
        · obtain ⟨rfl,rfl⟩:=hx;unfold V g;rw [if_pos ⟨rfl,rfl⟩,abs_mul,Nat.sub_zero];apply (mul_le_of_le_one_left (abs_nonneg _) ((hp m hm').cheap a)).trans; exact le_add_of_nonneg_left (by positivity [show 0 ≤ R from zero_le_one.trans hr])
        unfold V;rw [if_neg hx,add_zero]; by_cases h0:dusk b (P m) i a=0; · unfold g;rw [h0,zero_mul,abs_zero];exact mul_nonneg hW' (by linarith)
        have H':quota H (e-b) a<u:=by
           rcases Nat.eq_zero_or_pos b with rfl|hz
           · obtain ht|ht: i=a ∨ hops H i a:= (hp m hm').head i a h0
             · exact (hx ⟨rfl,ht.symm⟩).elim
             rw [Nat.sub_zero,←hq];unfold quota;have hv:= (tick_rank H).mp ht;omega
           have ht: (e-b+1)≤e:=by omega
           have hT:= Nat.mul_le_mul_left (turns d) ht;rw [mul_add,mul_one] at hT
           have hU:tick H a<turns d:=Nat.lt_succ_of_le (tick_bound H a)
           unfold quota at *;omega
        unfold g;rw [abs_mul];refine mul_le_mul ((hp m hm').paid _ (hb.trans he) i a) ((ih _ H' (e-b) (by omega) a j rfl m hm'.le).trans (pow_le_pow_right₀ hr H')) (abs_nonneg _) hW'
    change |∑ b∈ range (e+1),∑ a,g b a|≤_
    apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g:=fun b=>∑ a:I,(W*R^u+V b a)) (fun b hb=>(abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _=>hL _ a (by simpa only [mem_range,Nat.lt_succ_iff] using hb)))).trans ?_)
    simp_rw [sum_add_distrib]
    unfold V; simp_rw [sum_const,nsmul_eq_mul,card_range,card_univ,Nat.cast_add,Nat.cast_one,ite_and,Finset.sum_ite_irrel,Finset.sum_ite_eq',if_pos (mem_univ _),sum_const_zero,Finset.sum_ite_eq',if_pos (mem_range.mpr (Nat.zero_lt_succ _))]
    rw [add_comm];apply add_le_add_right; unfold M C;rw [mul_assoc,mul_assoc];exact mul_le_mul_of_nonneg_right (by gcongr) (by positivity [show 0 ≤ R from zero_le_one.trans hr])
lemma corridor_bank (I:Type)[Fintype I](H:Parade I d)(k:ℕ):∃ C:ℝ→ℝ,Wage C∧∀{n:ℕ}{W:ℝ}(P:ℕ→Sock I),1≤W→(n:ℝ)≤W→(∀ i<n,Day H k W (P i))→∀ e≤k,post (dusk e (sun P n)) (C W):=by
 let g:ℝ:=(k+1:ℝ)*Fintype.card I;have hg:0≤g:=by unfold g;positivity
 let f(x:ℝ):=1+g*x^2
 have hf: Wage f:=(Wage.constant _ zero_le_one).add ((Wage.constant g hg).mul (by simpa only [sq] using Wage.input.mul Wage.input))
 have hv(n:ℕ): Wage (fun x=>f x^n):=by induction n with
                                          | zero=>simpa using Wage.constant 1 zero_le_one
                                          | succ n ih=>simp_rw [pow_succ];exact ih.mul hf
 let m:=turns d*k+ ((d+1)*d+d)+1
 refine ⟨_,hv m,fun {n W} P hp hn hP e he i j=>(corridor H hp _ hn hP e i j he).trans ?_⟩
 apply pow_le_pow_right₀ (le_add_of_nonneg_right (show 0 ≤ g*W^2 by positivity))
 unfold quota m;have hv:=Nat.mul_le_mul_left (turns d) he;have hb:=tick_bound H i;omega

def duskline (P:ℕ→Sock I)(i j:ℕ):=sun (fun k=>P (i+k)) j
lemma duskline_succ (P:ℕ→Sock I)(i j:ℕ):duskline P i (j+1)=P (i+j)*duskline P i j:=rfl
lemma duskline_add (P:ℕ→Sock I)(i j:ℕ):duskline P i j * sun P i=sun P (i+j):=by
 induction j with
 | zero=>rw [duskline,sun,one_mul,Nat.add_zero]
 | succ j ih=>rw [duskline_succ,mul_assoc,ih,←Nat.add_assoc,sun]

lemma telescope (P Q:ℕ→Sock I)(n:ℕ):sun P n -sun Q n=∑ i∈range n,duskline P (i+1) (n-(i+1))*(P i - Q i)*sun Q i:=by
 induction n with
 | zero=> simp [sun]
 | succ n ih=>
   rw [sun,sun,sum_range_succ,Nat.sub_self,duskline,sun,one_mul,show P n* sun P n-Q n*sun Q n=P n*(sun P n - sun Q n)+(P n-Q n)*sun Q n from by noncomm_ring,ih,Finset.mul_sum]
   congr 1;apply sum_congr rfl;intro i hi
   have he:=mem_range.mp hi
   rw [show n+1-(i+1)=(n-(i+1))+1 by omega,duskline_succ,show i+1+(n-(i+1))=n by omega];simp only [mul_assoc]
lemma corridor_delta (I:Type)[Fintype I](H:Parade I d)(k:ℕ):∃ C:ℝ→ℝ,Wage C∧∀{n:ℕ}{δ W:ℝ}(P Q:ℕ→Sock I),1≤W→(n:ℝ)≤W→0≤δ→(∀ i<n,Day H k W (P i)∧Day H k W (Q i)∧∀ e≤k,post (dusk e (P i-Q i)) (W*δ))→
 ∀ e≤k,post (dusk e (sun P n-sun Q n)) (C W*δ):=by
 obtain ⟨C,hC,X⟩:= corridor_bank I H k
 let t:ℝ:=(Fintype.card I:ℝ);let u:ℝ:=k+1;have ht:0≤t:=Nat.cast_nonneg _;have hu:0≤u:=by unfold u; positivity
 let F(W:ℝ):= W*(u*(t*(u*(t*C W*W))*C W))
 have Ht:=Wage.constant t ht;have Hu:=Wage.constant u hu;have HE:=Wage.input
 refine ⟨F,HE.mul (Hu.mul ((Ht.mul (Hu.mul ((Ht.mul hC).mul HE))).mul hC)),fun {n δ W} P Q hw hn hd hp e he i j=>?_⟩
 rw [telescope]; unfold dusk; rw [Matrix.of_apply,Matrix.sum_apply,tap,map_sum];apply (abs_sum_le_sum_abs _ _).trans
 let M:ℝ:= (u*(t*(u*(t*C W*W))*C W))*δ; have h:0 ≤ M:=by unfold M;have hz:=hC.nn hw;have hw':0 ≤ W:=zero_le_one.trans hw; positivity
 apply (sum_le_sum (s:=range n) (g:=fun _=> M) (fun a ha=>?_)).trans
 swap
 · have ha:=mem_range.mp ha;have hA:=hp a ha
   have hx:( (n-(a+1):ℕ):ℝ)≤W:=(Nat.cast_le.mpr (Nat.sub_le _ _)).trans hn
   have hY:= X (fun j=>P ((a+1)+j)) hw hx (fun j hj=> (hp _ (by omega)).1)
   have hZ:= X Q hw ((Nat.cast_le.mpr ha.le).trans hn) (fun i hi=>(hp i (hi.trans ha)).2.1)
   let V:=u*(t*C W*(W*δ));have hv:0≤V:=by unfold V;have hx:= hC.nn hw;have hw':0≤W:=zero_le_one.trans hw; positivity
   have hg:= toe_post k hv (toe_post k (hC.nn hw) hY hA.2.2) hZ e he i j
   change |tap e _| ≤ M;apply hg.trans_eq;unfold M u t;ring
 rw [sum_const,nsmul_eq_mul,card_range];apply (mul_le_mul_of_nonneg_right hn h).trans_eq; unfold M F; ring
end YM.RG08.Atrium
