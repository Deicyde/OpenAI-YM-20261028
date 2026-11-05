import YM.RG08.Halo.Tuners

/-! # Analytic polynomial projection tariff, with graded strict price. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I:Type}{n p d h w:ℕ}{B σ:ℝ}{hs:0<σ}{F:Pack n (Ed G Cover)}
local notation "A"=>Loc G 1
lemma vocal_pool [Fintype I](a:ℕ)(t:Pearl)(S:Pearl→ₗ[ℝ]ℝ)(q:(i:Fin a)→Cargo i.val→ℝ)(ht:t=∑ i:Fin a,∑ j,q i j • pal j): S t=∑ i:Fin a,∑ j,q i j * S (pal j):=by rw [ht,map_sum];simp_rw [map_sum,map_smul,smul_eq_mul]
/-- annihilation extends to arbitrary test pool polynomial where joint weight below w. weights
zero allowed for fields. -/
lemma vocals (he:Tuned G n h d w σ hs F B){x:Pearl}{q:ℕ}{V:Fin n→Masked G}{b:Fin n→ℕ}(hV:∀ i,V i∈Place.rangeLt _ (b i))(ht:x.val∈ Place.rangeLt ℝ (q+1))(hW:q+∑ i,b i < w):sonic F x (Yurt.inlet ∘ V)=0:=by
 obtain ⟨D,hD,H⟩:=glossary (q+1);obtain ⟨C,hw⟩:=poolQual _ x ht;obtain ⟨T,hT,hπ⟩:=H x (show (0:ℝ)<1 by norm_num) hw
 change sheet (permits_poly he hV) x=_
 rw [vocal_pool (I:=Unit) _ x (sheet (permits_poly (V:=V) he hV)) T hT] -- expression not match
 apply sum_eq_zero;intro i _; apply sum_eq_zero; intro k _; change T i k*sonic F (pal k) (Yurt.inlet ∘ V)=0; rw [show sonic F (pal k) (Yurt.inlet ∘ V)=0 from he.onway _ _ k _ (by omega) hV,mul_zero]
lemma pay_roll (G:Gauge)(R n:ℕ) :∃ M:ℝ,0≤M ∧ ∀{F:Pack n (Ed G Cover)}{d w:ℕ}{σ B:ℝ}(hs:0<σ),Tuned G n R d w σ hs F B→ ∀ (V:Fin n→Masked G){b:Fin n→ℕ}{D:Fin n→ℝ}{u E:ℝ}(t:Pearl)(q:ℕ),0<u→u≤1→(q+∑ i,b i)≤R→(∀ i,Pool u (b i) 1 (V i) (D i))→ Pool u (q+1) 0 t.val E →
 |sonic F t (Yurt.inlet ∘ V)|≤ M*B*(∏ i,D i)*E*u^w:=by
 let r:=Fin R; let z:=Fin (R+1); let m:=Tape n r
 obtain ⟨C,hC,H⟩:=relay_payout (n:=n) G R
 let A':ℝ:=∑ i:m,∑ j:z,∑ _x:Cargo j.val,C*C^n
 have hc:0≤C:=zero_le_one.trans hC
 refine ⟨A',sum_nonneg (fun _ _=> sum_nonneg fun _ _=>sum_nonneg fun _ _=>mul_nonneg hc (pow_nonneg hc _)),?_⟩
 intro F d w σ B hs he V b D u E t q hu hi hv hE hP
 have hz(i):b i≤R:=(single_le_sum (s:=univ) (f:=b) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans (by omega)
 obtain ⟨P,T,hV,Ht,ht,hK,hV',H'⟩:=H b q hz (by omega) hu hE hP
 let U(i:m)(y:Fin n):=P y (i y); let p(i:r):ℕ:=i.val+1
 let Q(S:Pearl)(i:m):= sonic F S (Yurt.inlet ∘ U i)
 have hf : sonic F t (Yurt.inlet ∘ V)=∑ i:m,∑ j:z,∑ l:Cargo j.val,T j l*Q (pal l) i:=by
    rw [_root_.funext hV]; change sonic _ t (fun i=>Yurt.inlet (∑ j,P i j))=_;rw [sonic_poly_all he (fun i j=>(ht i j).fit) t]
    apply sum_congr rfl; intro i _;exact vocal_pool (I:=Unit) (R+1) t (sheet (permits_poly (V:=U i) he (fun j=>(ht j (i j)).fit))) _ Ht
 rw [hf];unfold A';simp_rw [sum_mul]
 let c:= C*C^n*B*(∏ i,D i)*E*u^w
 have ha(i):0≤D i:=(hE i).nice
 have hb:0≤B:=he.nonneg
 have hp:=hP.nice
 have h':0≤c:=by have hx:=prod_nonneg (s:=univ) (f:=D) (fun i _=>ha i);unfold c;positivity
 apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=>?_))
 apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun j _=>?_)); apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun l _=>?_))
 change |T j l * Q (pal l) i| ≤ c
 let s:=p ∘ i
 have hj(y): Chit G (s y) (U i y) _:=ht y (i y)
 by_cases HH:(∀ y:Fin n,s y ≤ b y)∧ (j.val ≤ q)
 · have hh:(j.val + ∑ y:Fin n,s y) ≤ R := Nat.le_trans (Nat.add_le_add HH.2 (sum_le_sum (fun y (_:y∈(univ:Finset (Fin n)))=>HH.1 y))) hv
   by_cases hy:j.val+∑ y:Fin n,s y < w
   · rw [show Q (pal l) i=0 from he.onway s j.val l (U i) hy (fun y=>(hj y).fit),mul_zero,abs_zero];exact h'
   have ht':=he.sturdy s _ l (U i) (fun y=>C*D y*u^(s y)) hh (fun y=>Nat.succ_le_succ (Nat.zero_le _)) hj
   rw [abs_mul]; apply (mul_le_mul (hK j l) ht' (abs_nonneg _) (by positivity)).trans
   rw [prod_mul_distrib,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,prod_pow_eq_pow_sum]
   have hW:=pow_le_pow_of_le_one hu.le hi (Nat.le_of_not_gt hy : w ≤ j.val+∑ y,s y)
   rw [pow_add] at hW
   let k:= C*C^n*B*(∏ i,D i)*E
   refine (show _ ≤ k*(u^j.val*u^(∑ i,s i)) from le_of_eq (by unfold k;ring)).trans (mul_le_mul_of_nonneg_left hW ?_)
   unfold k; have hz:=prod_nonneg (s:=univ) (f:=D) (fun i _=>ha i);positivity
 simp only [not_and_or,not_forall,Nat.not_le] at HH
 rcases HH with ⟨y,hy⟩|hj
 · have hz':(Yurt.inlet ∘ U i) y=0:=by change Yurt.inlet (P y (i y))=_;rw [hV' y (i y) (by change b y<(i y).val+1 at hy;omega)];rfl
   rw [show Q (pal l) i=0 from sonic_zero (i:=y) hz' _,mul_zero,abs_zero];exact h'
 rw [H' _ hj,zero_mul,abs_zero];exact h'
end YM.RG08.Halo
