import YM.RG08.Trill.Swift
import YM.RG08.Fete.Oboes
/-!
# Named mark algebra: coefficient actions at all orders. Scalar PowerSeries equality & flags.
 No rank activity alarms smuggled via `▸`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Atrium
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo Trill
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius PowerSeries
variable {I U:Type}{G:Gauge}{d n p l e D k a i r s:ℕ}
local notation "E₀"=>Ed G Cover
local notation "Y"=>Snap G d
local notation "A₀"=>Loc G 1
-- discrete clock utilities valid arbitrary additive monoids. NOTE not assuming identity estimates.
section
variable {V:Type}[AddCommMonoid V]
lemma overrange {e:ℕ}(f:ℕ→V){a:ℕ}(ha:a≤e): (∑ i∈range (a+1),f i) = ∑ i∈range (e+1),if i≤a then f i else 0:=by
 rw [←sum_filter];rw [show (range (e+1)).filter (fun i=>i≤a)=range (a+1) from ?_]; ext i; simp only [mem_filter,mem_range];omega
lemma tumble {e:ℕ}(f:ℕ→ℕ→V):(∑ i∈range (e+1),∑ a∈range (i+1),f i a)=∑ a∈range (e+1),∑ b∈range (e-a+1),f (b+a) a:=by
 calc
  _ =∑ i∈range (e+1),∑ a∈range (e+1),if a ≤ i then f i a else 0:=sum_congr rfl fun i hi=>overrange (f i) (by simp only [mem_range] at hi;omega)
  _ = _:=by
    rw [sum_comm];apply sum_congr rfl;intro a ha
    have ha:=mem_range.mp ha
    rw [show (∑ i∈range (e+1),if a ≤ i then f i a else (0:V))=∑ i∈range (a+(e-a+1)),if a ≤ i then f i a else (0:V) from by rw [show a+(e-a+1)=e+1 from by omega],sum_range_add, Finset.sum_eq_zero (fun i (hi:i∈range a)=>if_neg (not_le_of_gt (mem_range.mp hi))),zero_add]
    apply sum_congr rfl;intro i hi;rw [if_pos (show a≤a+i by omega), Nat.add_comm]
end
lemma tap_mul (p q:Dig)(e:ℕ):tap e (p*q)=∑ i∈range (e+1),tap i p*tap (e-i) q:=by rw [tap,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
lemma tap_one (e:ℕ):tap e (1:Dig)=if e=0 then 1 else 0:=PowerSeries.coeff_one _
lemma tap_zero (e:ℕ):tap e (0:Dig)=0:=map_zero _

def slip (t:Dig)(P:GrainS I):GrainS I:=fun e n=> ∑ i∈range (e+1),tap i t • P (e-i) n
lemma slip_one (P:GrainS I):slip 1 P=P:=by funext e n; unfold slip; rw [sum_eq_single 0];rw [tap_one,if_pos rfl,one_smul,Nat.sub_zero];intro i _ hi;rw [tap_one,if_neg hi,zero_smul];simp
lemma slip_zero (P:GrainS I):slip 0 P=0:=by ext; unfold slip; simp_rw [tap_zero,zero_smul,sum_const_zero];rfl
lemma slip_dry (v:Dig):slip v (0:GrainS I)=0:= by ext;unfold slip;simp only [Pi.zero_apply,smul_zero,sum_const_zero]
lemma slip_plus (P Q:GrainS I)(t:Dig):slip t (P+Q)=slip t P+slip t Q:=by funext e n;unfold slip;simp_rw [Pi.add_apply,smul_add,sum_add_distrib]
lemma slip_cast (P:GrainS I)(t u:Dig):slip (t+u) P=slip t P+slip u P:=by funext e n;unfold slip tap;simp_rw [Pi.add_apply,map_add,add_smul,sum_add_distrib]
lemma slip_family {s:Finset U}(t:U→Dig)(P:GrainS I):slip (s.sum t) P=∑ i∈s,slip (t i) P:=by induction s using Finset.induction_on with
| empty=>rw [sum_empty,sum_empty,slip_zero]
| @insert a s ha ih=>rw [sum_insert ha,sum_insert ha,slip_cast,ih]
lemma slip_family' {s:Finset U}(P:U→GrainS I)(t:Dig):slip t (s.sum P)=∑ i∈s,slip t (P i):=by induction s using Finset.induction_on with
| empty=>rw [sum_empty,sum_empty,slip_dry]
| @insert a s ha ih=>rw [sum_insert ha,sum_insert ha,slip_plus,ih]
lemma slip_stunt (P:GrainS I)(t u:Dig):slip t (slip u P) = slip (t*u) P := by
 funext e n
 unfold slip;simp_rw [Finset.smul_sum,smul_smul,tap_mul,Finset.sum_smul]
 symm
 rw [tumble (e:=e) (fun i j=> (tap j t*tap (i-j) u) • P (e-i) n)]
 apply sum_congr rfl;intro a ha;apply sum_congr rfl;intro b hb
 have ha:=mem_range.mp ha;have hb:=mem_range.mp hb
 rw [show b+a-a=b by omega,show e-(b+a)=e-a-b by omega]

/-- Rank k supplier read into column l with threshold. -/
def Paces (k l:ℕ)(t:Dig):Prop:=∀ i,l+i<k→tap i t=0
lemma Paces.church {k l:ℕ}(h:k≤l)(t:Dig):Paces k l t:=fun i hi=>False.elim (by omega)
lemma Paces.add {k l:ℕ}{t u:Dig}(h:Paces k l t)(hu:Paces k l u):Paces k l (t+u):=fun i hi=>by unfold tap; rw [map_add];change tap _ _+tap _ _=_;rw [h _ hi,hu _ hi,add_zero]
lemma Paces.mul {k l m:ℕ}{t u:Dig}(ht:Paces l k t)(hu:Paces m l u):Paces m k (t*u):=by
 intro i hi;rw [tap_mul];apply sum_eq_zero;intro j hj
 have hj:=mem_range.mp hj;by_cases h:k+j<l
 · rw [ht j h,zero_mul]
 rw [hu (i-j) (by omega),mul_zero]
lemma Paces.nothing {k l:ℕ}:Paces k l 0:=fun i _=> tap_zero i
lemma Paces.sum {k l:ℕ}(f:I→Dig)(s:Finset I)(hf:∀ i∈s,Paces k l (f i)):Paces k l (s.sum f):=by induction s using Finset.induction_on with
| empty=>rw [sum_empty];exact .nothing
| @insert a s ha ih=>rw [sum_insert ha];exact (hf a (by simp)).add (ih (fun i hi=>hf i (by simp [hi])))

structure Folk (d l:ℕ)(P:GrainS E₀):Prop where
 inlet : Permit d l P
 outlet : Calls l P

open Clef
lemma folk_nil (d l:ℕ):Folk (G:=G) d l 0:=⟨Permit_hush ..,Calls_hush⟩
lemma Folk.add {P Q:GrainS E₀}(hp:Folk D l P)(hq:Folk D l Q):Folk D l (P+Q):=⟨Permit_add hp.1 hq.1,by simpa using Calls_lin hp.2 hq.2 1⟩
lemma Folk.smul {P:GrainS E₀}(hp:Folk D l P)(a:ℝ):Folk D l (a • P):=⟨Permit_smul hp.1 _,Calls_smul hp.2 _⟩
lemma Folk.sub {P Q:GrainS E₀}(hp:Folk D l P)(hq:Folk D l Q):Folk D l (P-Q):=by rw [show P-Q=P+(-1:ℝ) • Q from by rw [neg_smul,one_smul,sub_eq_add_neg]];exact hp.add (hq.smul _)
lemma Folk.tots {s:Finset I}{P:I→GrainS E₀}(h:∀ i∈s,Folk D l (P i)):Folk D l (s.sum P):=by induction s using Finset.induction_on with
| empty=>rw [sum_empty];exact folk_nil ..
| @insert i s hi ih=>rw [sum_insert hi];exact (h i (by simp)).add (ih (fun j hj=>h j (by simp [hj])))
lemma flag_slip {P:GrainS I}{u:Dig}(h:Skiff.Lit k P)(hd:Paces k l u):Skiff.Lit l (slip u P):=by
 intro i n hi;contrapose! hi
 unfold slip; refine sum_eq_zero (fun j hj=>?_)
 have hj:=mem_range.mp hj;by_cases ht:l+j<k
 · rw [hd j ht,zero_smul]
 rw [show P (i-j) n=0 from Classical.not_not.mp (fun he=>?_ ),smul_zero];have he:=h _ _ he;omega
lemma permit_slip [Fintype I]{P:GrainS (Market I)}{u:Dig}(h:Permit D k P)(hd:Paces k l u):Permit D l (slip u P):=by
 refine ⟨flag_slip h.lit hd,?_,?_⟩
 · intro f e n;unfold Trickle.brook slip;rw [Trickle.during_sum]
   have hf(s:Finset ℕ)(F:ℕ→Flake n (Market I))(he:∀ i,Forms.Sym (F i)):Forms.Sym (s.sum F):=by
      induction s using Finset.induction_on with
      | empty=>exact Forms.Sym.zero
      | @insert i s hi ih=>rw [sum_insert hi];exact (he _).add ih
   exact hf (range (e+1)) _ (fun i=>(h.fine f _ _).smul _) -- during smul def
 intro i n;obtain ⟨σ,hσ,B,hB,K⟩:=h.price.license h.lit i
 let t(j):=tap j u
 refine ⟨Lyrics.sum (range _) (fun j _=> ((h.price (i-j) n).1).smul (t j)),σ,hσ, (∑ j∈range (i+1),|t j| * B),sum_nonneg fun j _=>mul_nonneg (abs_nonneg _) hB,Sings.sum (range _) (fun j hj=> (K (i-j) (by omega) n).smul _) fun _ _=> mul_nonneg (abs_nonneg _) hB⟩ -- syntax

-- Reading law; no Bore consumed for closed operations with scalars. use LinearMap.smt
private def hump (x:Tray I)(f:Pearl):Pack n I→ₗ[ℝ] Dig where
 toFun P:=Weald.summit P f x
 map_add' P Q:=by unfold summit Gallery.volume during; simp_rw [Pi.add_apply,add_smul,sum_add_distrib]
 map_smul' v P:=by unfold summit Gallery.volume during; simp_rw [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply,← smul_assoc]
lemma pin_tall (P:Pack n I)(i:ℕ)(x:Tray I)(f:Pearl)(c:ℝ): tap i (summit (c • P) f x)= c*tap i (summit P f x):=by
 change tap i (hump x f (c • P))= _;rw [_root_.map_smul,tap,PowerSeries.coeff_smul];rfl
private lemma rise_t (P:GrainS I)(hp:Skiff.Lit k P)(a l i:ℕ)(h:k≤l)(x:Tray I)(f:Pearl):
 (∑ n∈range (l+a+1), tap i (summit (P a n) f x))=∑ n∈range (k+a+1),tap i (summit (P a n) f x):=by
 symm;apply Finset.sum_subset (by intro j hj; apply mem_range.mpr;have ht:=mem_range.mp hj;omega);intro n _ hn; rw [show P a n=0 from ?_]
 · change tap i ((hump x f) 0)=0;rw [map_zero,tap_zero]
 exact Classical.not_not.mp fun hy=>hn (mem_range.mpr (by have he:=hp a n hy;omega))
lemma scripted (P:GrainS I)(x:Tray I)(f:Pearl)(q e:ℕ):tap e (Weald.mint q P f x)=∑ i∈range (e+1),∑ n∈range (q+i+1),tap (e-i) (summit (P i n) f x):=by
 rw [Weald.mint,tap,PowerSeries.coeff_mk]; unfold Weald.crown tap;simp_rw [map_sum]
lemma mint_weight (P:GrainS I)(hp:Skiff.Lit k P)(u:Dig)(hs:Paces k l u)(f:Pearl)(x:Tray I): Weald.mint l (slip u P) f x=u*Weald.mint k P f x:=by
 ext i:1;change tap _ _=tap _ _;rw [tap_mul,scripted];simp_rw [scripted P]
 have hh(z n j:ℕ): tap j (summit (slip u P z n) f x)=∑ a∈range (z+1),tap a u *tap j (summit (P (z-a) n) f x):=by
    unfold slip;change tap j (hump x f (_:Pack n I))=_
    rw [map_sum,tap,map_sum]; apply sum_congr rfl;intro a _; exact pin_tall _ j x f _
 simp_rw [hh]
 -- commute n & a then tumble
 trans ∑ z∈range (i+1),∑ a∈range (z+1),∑ n∈range (l+z+1),tap a u * tap (i-z) (summit (P (z-a) n) f x)
 · apply sum_congr rfl;intro j _;rw [sum_comm]
 rw [tumble (e:=i) (fun z a=>∑ n∈range (l+z+1),tap a u*tap (i-z) (summit (P (z-a) n) f x))];apply sum_congr rfl;intro a ha;rw [mul_sum];apply sum_congr rfl;intro b hb
 rw [←mul_sum,show i-(b+a)=i-a-b by omega,show b+a-a=b by omega]
 by_cases hz:l+a<k; · rw [hs a hz,zero_mul,zero_mul]
 congr 1; rw [show l+(b+a)+1=(l+a)+b+1 by omega,rise_t P hp _ _ _ (Nat.le_of_not_gt hz)]

theorem Folk.slip {u:Dig}(hw:Paces k l u){P:GrainS E₀}(h:Folk D k P):Folk D l (Atrium.slip u P):= ⟨permit_slip h.1 hw,fun f x b w=>by simp_rw [mint_weight P h.1.lit u hw,h.2 f x b w]⟩
end YM.RG08.Atrium
