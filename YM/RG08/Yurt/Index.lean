import YM.RG08.Yurt.Cairns

/-!
# Ordered dual column accounting, joint cancellation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior Skiff
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{G:Gauge}{n h p d e i:ℕ}{D C T B τ σ δ:ℝ}{L L':Side}{hh:0<σ}
local notation "A" => Loc G 1

-- linearity of evaluation on test; all sums absolute.
def star {S:Jetty.Loom I}{F:Pack n I}(he:Lyrics F)(hf:Sings S d hh F C)(hC:0≤C){X:Fin n→I→ℝ}{a:Fin n→ℝ}{p:ℕ}{δ:ℝ}(hx:0≤δ)(hy:(n:ℝ)*δ≤σ/2)(hz:∀ i,Bearing S p δ (a i) (X i)):Pearl→ₗ[ℝ] ℝ where
 toFun f:= sonic F f X
 map_add' f g:=by
    unfold sonic tote
    simp_rw [(he _).plus,add_mul]
    exact (sonic_abs he hf hC f hx hy hz).of_norm.tsum_add (sonic_abs he hf hC g hx hy hz).of_norm
 map_smul' a f:=by
    unfold sonic tote;simp_rw [(he _).hum,mul_assoc,tsum_mul_left];rfl

-- joint test grade & fees: use Fin (h+2), last remainders. Fees positive. Pullback at ahead L α
def niche (h:ℕ)(a:ℝ)(v:E4)(f:Pearl)(r:Fin (h+2)):Pearl:=if r.val≤h then Lagoon.service a v r.val f else trail a v h f
lemma niche_gains (h:ℕ)(a:ℝ)(v:E4)(f:Pearl):aisle a v f=∑ i:Fin (h+2), niche h a v f i:=by
 rw [Fin.sum_univ_castSucc]; have he(i:Fin (h+1)):niche h a v f i.castSucc=Lagoon.service a v i.val f:=by unfold niche;rw [if_pos (by simp;omega)];rfl
 rw [sum_congr rfl (g:=fun i:Fin (h+1)=>Lagoon.service a v i.val f) (fun i _=>he i)];unfold niche at *
 rw [if_neg (by simp),Fin.sum_univ_eq_sum_range (fun i=> Lagoon.service a v i f)]; exact train ..
lemma niche_pays (_G:Gauge)(h d:ℕ)(τ σ:ℝ)(h0:0<τ)(h1:0<σ)(hz:h+1≤d):∃ C:ℝ,0≤C ∧∀(a:ℝ)(v:E4)(f:Pearl)(r:Fin (h+2)),‖v‖≤4→0≤a→a≤1→τ*a≤σ/2→
 beam d h1 (niche h a v f r) ≤ C*a^r.val*beam d h0 f:=by
 choose C hC hF using (fun i (hi:i≤d)=>spoken h1 h0 4 i d hi)
 obtain ⟨D,hD,H⟩:= withheld h0 h1 4 d h hz
 let s (i:Fin (d+1)):=C i.val (by omega)
 have hs(i):1≤ s i:= hC ..
 let S:=∑ i:Fin (d+1),s i
 have hS:0≤S:=sum_nonneg fun i _=>zero_le_one.trans (hs i)
 refine ⟨S+D,by linarith,fun a v f r hv ha ha' hp=>?_⟩
 have he: |a|=a:=abs_of_nonneg ha
 unfold niche;split
 · rename_i hx
   apply (hF r.val (by omega) f a v hv).trans
   let i:Fin (d+1):=⟨r.val,by omega⟩
   have hh:s i ≤ S:=single_le_sum (f:=s) (fun t _=>zero_le_one.trans (hs t)) (mem_univ _)
   rw [he]; gcongr
   · exact beam_nn ..
   exact hh.trans (le_add_of_nonneg_right (zero_le_one.trans hD))
 rename_i hx
 have hh:r.val=h+1:=by omega
 apply (H f a v (by rwa [he]) (by rwa [he]) hv).trans;rw [he,hh];gcongr
 · exact beam_nn ..
 exact le_add_of_nonneg_left hS

-- incoming rank tape n. weighted monomials. low joint. Tail `T`: actual rank receipt.
def ice (n _p _d t _h:ℕ)(Z _σ τ:ℝ):ℝ:= Fintype.card (Cargo t) * ((t.factorial:ℝ)⁻¹ * Real.exp (τ*4))*Z^n -- d etc prose
lemma bill_low {F:Pack n (Ed G Cover)}(hU:Minored G h n F B)(hB:0≤B)(X:Fin n→Masked G)(a:Fin n→ℕ)(t:ℕ)(u η:ℝ)(ht:0<η)(hF:Lyrics F)(hc:Sings (stance A) d hh F T)(hT:0≤T)
 (D:ℝ)(hD:0≤D)(hv:t+∑ i,a i ≤ h)(hz:h+1≤d)(he:∀ i,1≤a i)(hc':∀ i,Chit G (a i) (X i) (D*u^(a i)))(f:Pearl)(v:E4)(hu:0≤u)(hu':u≤1)(hw:‖v‖≤4):
 |sonic F (Lagoon.service u v t f) (Yurt.inlet ∘ X)| ≤ ice n h d t h D σ η * B * beam d ht f:=by
 let R:=star hF hc hT (show (0:ℝ)≤0 from le_rfl) (show (n:ℝ)*0≤σ/2 from by linarith) (X:=Yurt.inlet ∘ X) (a:=fun i=>D*u^(a i)) (p:=h) (fun i=>exhausted (hc' i) (by have := single_le_sum (f:=a) (fun i (_:i∈ (univ:Finset (Fin n)))=> Nat.zero_le (a i)) (mem_univ i); omega) le_rfl)
 change |R _| ≤ _
 unfold Lagoon.service Lagoon.spokes; rw [map_smul,smul_eq_mul,map_sum];simp_rw [_root_.map_smul,smul_eq_mul];rw [abs_mul,abs_pow]
 have Hc:0≤(t.factorial:ℝ)⁻¹:=by positivity
 have hY:= beam_nn d ht f
 let V:= (t.factorial:ℝ)⁻¹ * (beam d ht f * Real.exp (η*(4:ℝ))) * ((D^n)*B)
 have hV:0≤V:=by unfold V; positivity
 rw [abs_of_nonneg hu]
 refine (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hu hu')).trans ((abs_sum_le_sum_abs _ _).trans ?_)
 apply (sum_le_sum (g:=fun _=>V) (fun i _=>?_)).trans_eq
 · rw [sum_const,card_univ,nsmul_eq_mul]; unfold V ice;ring
 rw [abs_mul]
 apply mul_le_mul (borne i f v ht hw (by omega:t≤d)) ((hU a t i X _ hv he hc').trans ?_) (abs_nonneg _) (mul_nonneg Hc (mul_nonneg hY (Real.exp_pos _).le))
 apply mul_le_mul_of_nonneg_right _ hB
 rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin];apply mul_le_of_le_one_right (pow_nonneg hD _)
 exact Finset.prod_le_one (fun _ (_: _)=>pow_nonneg hu _) (fun _ (_: _)=> pow_le_one₀ hu hu')

lemma bill_high {F:Pack n I}(S:Jetty.Loom I)(X:Fin n→I→ℝ)(a:Fin n→ℕ)(t:ℕ)(D E u:ℝ)(f:Pearl)(hF:Lyrics F)(hc:Sings S d hh F T)(hT:0≤T)
 (hD:0≤D)(hu:0≤u)(hu':u≤1)(hE:0≤E)(he:0≤δ)(hz:(n:ℝ)*δ≤σ/2)(hf:∀ i,Bearing S p δ (D*u^(a i)) (X i))(hB:beam d hh f ≤ E*u^t)(H:t+∑ i,a i > h):
 |sonic F f X| ≤ blade 0 (p*n) (σ/2)*D^n*T*E*u^(h+1):=by
 have hc':0≤blade 0 (p*n) (σ/2):=blade_nn _ _ ((half_pos hh).le)
 have hi {k}:0 ≤ u^k:=pow_nonneg hu k
 have hj:0≤ D^n*T:=mul_nonneg (pow_nonneg hD n) hT
 have h₀:=sonic_le hF hc hT f he hz hf
 unfold Flint.tribute at h₀;rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,Finset.prod_pow_eq_pow_sum] at h₀
 apply h₀.trans; let N:=∑ i:Fin n,a i
 have hpow:u^N*u^t ≤ u^(h+1):=by rw [←pow_add];exact pow_le_pow_of_le_one hu hu' (by omega)
 change Jetty.blade _ _ _*(D^n*u^N)*_*_≤_
 nlinarith only [mul_le_mul_of_nonneg_left hB (show 0 ≤ blade 0 (p*n) (σ/2) * (D^n*u^N)*T by positivity),mul_le_mul_of_nonneg_left hpow (show 0 ≤ blade 0 (p*n) (σ/2)*D^n*T*E by positivity)]
end YM.RG08.Yurt
