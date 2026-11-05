import YM.RG08.Quarry.Qui
/-! # Sober demands reused at right grades before mark extraction. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Roost
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Mount Glyph Room Bloch Quarry Aggregate Steam
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c f :Side}{G:Gauge}{P:Patch}{K:KernelChoices}{A B:Bed}{C:Castle G}(hC:Mount.Stable C){Z:ChartRatio G}
-- do not require an incident step, even at chain entirely test periods. rank k≤e expression
private lemma converge (_k e j r:ℕ)(hj:j  ≤  e)(hr:r  ≤  j) (_hs:hC=hC):
    showV (fun i n=> if he:0 < n then pour (P:=c) (Mount.flight r j (C r j) i n) ⟨0,he⟩ else 0) e= tap e (PowerSeries.X^j*Camera.tax (Mount.rank r) (booked (C r j) (stick r) c)):=by -- duplicated concur for any side
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hj
 have he:= hC.hold r j; have hd:=hC.dial r j
 let p:=d+j;have hq:p-j=d:=by unfold p;omega
 let N:=d+Mount.rank r;have hn:0 < N:=Nat.zero_lt_succ _
 have hm :N∈range (p+3):=by simp only [mem_range,p,N,Mount.rank];omega
 rw [tap, add_comm j d, PowerSeries.coeff_X_pow_mul]
 unfold showV; change (∑ n∈range (p+3),parley (if hk:0 < n then pour (P:=c) (Mount.flight r j (C r j) p n) ⟨0,hk⟩ else 0))=tap d _
 rw [Finset.sum_eq_single_of_mem N hm ?_, dif_pos hn,Mount.flight,if_pos (by rw [hq];exact ⟨by dsimp [p]; omega,rfl⟩),Camera.audited,reserve (stick r) (n:=Mount.rank r) (k:=d+Mount.rank r) ⟨0,hn⟩ (hC.banner r j).path he (hC.weight r j) hd]
 intro b _ hh;split
 next h0=>rw [Mount.flight,hq,if_neg (by rintro ⟨_,H⟩;exact hh H.symm),blank _ _ rfl,parley_zero]
 exact parley_zero
-- taps for entire regulator
include hC in
lemma keeping (c:Side)(N e :ℕ)(h:e ≤ N):
 tap e (stock (unveil (demand C) c))= tap e (∑ i∈range (N+1),∑ r∈range (i+1),PowerSeries.X^i*Camera.tax (Mount.rank r) (booked (C r i) (stick r) c)):=by
 unfold tap Glyph.stock; rw [PowerSeries.coeff_mk]
 have hf(n:ℕ):parley (unveil (demand C) c e n)=∑ j∈range (e+1),∑ r∈range (j+1),parley (if hi:0 < n then pour (P:=c) (Mount.flight r j (C r j) e n) ⟨0,hi⟩ else 0):=by
    by_cases he:0 < n
    · simp only [unveil,dif_pos he,demand_sum C hC]
    simp [unveil,he,parley_zero]
 unfold showV; simp_rw [hf]; rw [Finset.sum_comm]
 rw [map_sum,←Finset.sum_subset (by intro i hi;simp only [mem_range] at *;omega : range (e+1)⊆range (N+1)) (f:=fun i=>PowerSeries.coeff e (∑ r∈range (i+1),PowerSeries.X^i*Camera.tax (Mount.rank r) (booked (C r i) (stick r) c))) ?_] -- g cannot infer
 · refine Finset.sum_congr rfl (fun i hi=>?_)
   rw [Finset.sum_comm,map_sum]; exact Finset.sum_congr rfl (fun r hr=>converge hC 0 e i r (by simpa using hi) (by simpa using hr) rfl)
 intro i _ hi;rw [map_sum]; apply Finset.sum_eq_zero; intro r _; rw [PowerSeries.coeff_X_pow_mul',if_neg (by simpa using hi)]
include hC
lemma update (c:Side)(N e:ℕ)(h:e ≤ N): tap e (stock (unveil (demand C) c))= tap e (∑ i∈range (N+1),∑ r∈range (i+1),PowerSeries.X^i*Camera.tax (Mount.rank r) (booked (C r i) (stick r) c)):=keeping hC c N e h
lemma overt (c:Side){I:Type}[Fintype I] (s:Signed) (f g:Camera.Strip (Lines G c 1) I)(hf:∀ i,Pace (f i))(hg:∀ i,Pace (g i))(hv: roll f 0=0)(ht:roll g 0=0)(hx:∀ᶠ x:Cellar I in 𝓝 0,∃ v:Site c→G.El, offers G (roll g x)=Lattice.gauge v (pull s 0 (offers G (roll f x)))):
 let V:=stock (unveil (demand C) c);belt (rescaleFields f) V=belt (rescaleFields g) V:=by
 intro V;ext e :1;change tap e _=tap e _
 let w:Port (Lines G c 1):= ∑ i∈range (e+1),∑ r∈range (i+1),PowerSeries.X^i*Camera.tax (Mount.rank r) (booked (C r i) (stick r) c)
 have hs (q):tap e (belt q V)=tap e (belt (fun i:Lines G c 1=> (q i:Port I)) w):=steady_belt _ e V w (fun k hk=>keeping hC c e k hk)
 rw [hs,hs]; apply congrArg
 unfold w;rw [map_sum,map_sum];simp_rw [map_sum,_root_.map_mul,_root_.map_pow,belt_g]
 apply sum_congr rfl;intro i _;apply sum_congr rfl; intro r _;congr 1
 exact switch_rep f g hf hg hv ht s 0 _ (hC.banner r i).path (hC.banner r i).hair (hC.dial r i) (hC.weight r i) (hC.hold r i) hx
lemma landing : Grafted (fun n=>unveil (demand C) (Isles.chain n)) (demand C):=by
 intro e n hn
 obtain ⟨u,V,hu,hV,hE⟩:=carpet_demand C hC e n
 exact fun t=> by simpa only [unveil,dif_pos hn,carpetRoad,Isles.port] using! ((bureau (demand_solid hC e n).1 hE hu hV ⟨0,hn⟩).light hn t)
end YM.RG08.Roost
