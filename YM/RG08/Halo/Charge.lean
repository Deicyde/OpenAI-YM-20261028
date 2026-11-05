import YM.RG08.Halo.Pillars

/-! # Leading exactness under dilation, reading polynomial map. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I:Type}{n p q d h w:ℕ}{B σ:ℝ}{hs:0<σ}{F:Pack n (Ed G Cover)}
local notation "A"=>Loc G 1
-- all leading maps, can discard strictly lowering Subspace of test.
lemma badge_turn (he:Tuned G n h d w σ hs F B) {V V':Fin n→Masked G}{b:Fin n→ℕ}
 (hq: (q+∑ i,b i)≤w)(hf:∀ i,1≤b i)(hV:∀ i,V i∈Place.rangeLt _ (b i))(hV':∀ i,V' i-V i∈Place.rangeLt _ (b i-1))
 (f f':Pearl)(h:f.val∈Place.rangeLt ℝ (q+1))(hk:((f'-f:Pearl).val)∈Place.rangeLt ℝ q):
 sonic F f' (Yurt.inlet ∘ V')=sonic F f (Yurt.inlet ∘ V):=by
 let z(i:Fin n)(c:Bool): Masked G := if c then V i else V' i - V i
 let a(i:Fin n)(c:Bool):ℕ:=if c then b i else b i-1
 have hx(i c):z i c∈Place.rangeLt _ (a i c):=by cases c;exact hV' _;exact hV i
 have hy(i):∑ c:Bool,z i c=V' i:=by rw [Fintype.sum_bool];unfold z;simp only [reduceCtorEq,if_false,if_true];abel
 have ht(i):V' i∈Place.rangeLt _ (b i):=by
    rw [←hy]; apply Submodule.sum_mem;intro c _;apply Place.grows _ (show a i c ≤ b i from ?_) (hx i c);cases c <;> simp [a]
 let R:=sheet (permits_poly he ht)
 have hF : sonic F f' (Yurt.inlet ∘ V')=sonic F f (Yurt.inlet ∘ V'):=by
    have hh : R (f'-f)=0:=by
       obtain rfl|hz:= Nat.eq_zero_or_pos q
       · rw [Place.rangeLt,Submodule.mem_bot] at hk; rw [show f'-f=0 from Subtype.ext hk,map_zero]
       apply vocals he ht (q:=q-1) (by convert hk using 2; omega) (by omega)
    rw [map_sub] at hh;exact sub_eq_zero.mp hh
 rw [hF,← _root_.funext hy,show Yurt.inlet ∘ (fun i=>∑ c:Bool,z i c)=(fun i=>Yurt.inlet (∑ c,z i c)) from rfl, sonic_poly_all he hx f,sum_eq_single_of_mem (fun _:Fin n=>true) (mem_univ _)];rfl
 intro y _ H
 obtain ⟨i,hi⟩:=Function.ne_iff.mp H
 let M(j:Fin n):= a j (y j)
 refine vocals he (fun i=>hx i _) h (q:=q) (by have hs:(∑ i,M i)<∑ i,b i:= sum_lt_sum (s:=univ) (fun i _=>by unfold M a;split<;>omega) ⟨i,mem_univ i,by have h0:=hf i; unfold M a; rw [if_neg hi];omega⟩;change q+(∑ i,M i)<_;omega)

/-- survivor below threshold ≥ all demanded terms, and principal exactly at threshold.
Orientation preservation, tends no assumed lemma. scales u^{total}, proof doesn't use positivity.
-/
lemma badges (he:Tuned G n h d w σ hs F B){u:ℝ} {V V':Fin n→Masked G}{b:Fin n→ℕ}
 (hq: (q+∑ i,b i)≤w)(hf:∀ i,1≤b i)(hV:∀ i,V i∈Place.rangeLt _ (b i))(hV':∀ i,V' i-u^b i • V i∈Place.rangeLt _ (b i-1))
 (f f':Pearl)(h:f.val∈Place.rangeLt ℝ (q+1))(hk:(f'-u^q • f:Pearl).val∈Place.rangeLt ℝ q):
 sonic F f' (Yurt.inlet ∘ V')=u^(q+∑ i,b i)*sonic F f (Yurt.inlet ∘ V):=by
 let v:Fin n→ Masked G:=fun i=> (u^b i) • V i
 have ht(i):v i∈Place.rangeLt _ (b i):=Submodule.smul_mem _ _ (hV i)
 let g:=u^q • f
 have hg:g.val∈Place.rangeLt _ (q+1):= Submodule.smul_mem _ _ h
 -- proof turn holds also w=0; generalize
 rw [badge_turn he hq hf ht hV' g f' hg hk]
 let Z:=sheet (permits_poly he ht)
 change Z (u^q • f)=_
 rw [map_smul];change u^q*sonic F f (Yurt.inlet ∘ v)= _
 rw [show Yurt.inlet ∘ v=(fun i=>u^(b i) • (Yurt.inlet ∘ V) i) from by ext i j;rfl,sonic_pull,prod_pow_eq_pow_sum,pow_add];exact (mul_assoc ..).symm
end YM.RG08.Halo
