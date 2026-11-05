import YM.RG08.Yurt.Index

/-! # Pointwise funded cell estimate. Null consumed. Joint all terms finite. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior Skiff
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I:Type}{G:Gauge}{n p d e i:ℕ}{D C T B τ η σ δ:ℝ}{L L':Side}
local notation "A" => Loc G 1
-- two beams σ input & η tested output (τ external slot rate). no assumption η≤σ only η/L≤σ/2 for remainder
/-- Constant-announced before L. Sym needed by Ward separately. T the same-order
sensor (allowed repeated); B fed by lower. -/
lemma lunch (G:Gauge)(h d n:ℕ)(s C σ η δ:ℝ)(ht:0≤ s)(hc:0≤C)(hs0:0<σ)(hη:0<η)(hd:h+1≤d)(hn:(n:ℝ)*δ≤σ/2):∃ D:ℝ,0 ≤ D ∧ ∀ {T B τ:ℝ}(L:Side)(o:Site L)(M:Carrier.Lines L)(F:Pack n (Ed G Cover))(f:Pearl)(y:Tape n (Ed G Cover)),Odd L.val→Tutor L s C M G h→0≤τ→τ≤ s →τ/(L.val:ℝ) ≤δ→ η*unitStep L ≤ σ/2→ Lyrics F→Sings (stance (Loc G 1)) d hs0 F T→0≤T→Minored G h n F B→0≤B→
 let u:=unitStep L
 ; |sonic F (aisle u (ahead L o) f) (fun i=>Yurt.full G o M τ (y i))| ≤ D*(B+T*u^(h+1))*beam d hη f:=by
 obtain ⟨Q,hQ,H⟩:=niche_pays G h d η σ hη hs0 hd
 obtain ⟨V,hV,h₁⟩:=Yurt.quarry G h s C ht hc
 let c:=Fin (h+2);let m:=Fin (h+1); let q:=Tape n m
 let W₁(t:c):= Yurt.ice n h d t.val h V σ η; have hz(t):0≤W₁ t:=by unfold W₁ ice;positivity
 let W₂:= Jetty.blade 0 (h*n) (σ/2) * V^n*Q;have hj:0≤W₂:=by unfold W₂; have hz:=blade_nn 0 (h*n) (σ:=σ/2) (by positivity); positivity -- signature
 let W(t:c):=W₁ t+W₂; have hw(t):0≤W t:=add_nonneg (hz _) hj
 let D:= ∑ t:c,∑ _j:q,W t
 have hD:0≤D:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>hw _
 refine ⟨D,hD,?_⟩
 intro T B τ L o M F f y hL hP hτ hτ' hδ hu' hF hT hT' hB hB' u
 have hu:0≤u:=(unitStep_pos L).le; have hu1:u≤1:=unitStep_le _
 have hη':0≤beam d hη f:=beam_nn d hη f
 have hδ':0≤δ:=(div_nonneg hτ (Nat.cast_nonneg _)).trans hδ
 let v:=ahead L o
 have hv:‖v‖≤4:=heading L o
 let S(i:Fin n)(j:m):=posed h o M τ (y i) j
 let a(i:m):=i.val+1
 have hx(i:Fin n)(j:m): Bearing (stance (Loc G 1)) h δ (V*u^(a j)) (S i j):= (h₁ L o M hL hτ hτ' hδ hP j (y i)).1
 let k(i:q)(j:Fin n):ℕ:=a (i j);let Y(i:q)(j:Fin n):=newton G τ o M (y j) (i j).val
 let P(i:q)(j:Fin n):=S j (i j)
 -- linearity F with low X via star/hx
 have he: sonic F (aisle u v f) (fun i=>Yurt.full G o M τ (y i))=∑ t:c,∑ i:q,sonic F (niche h u v f t) (P i):=by
    simp_rw [offer_read M h o];rw [sonic_bill hF hT hT' _ (X:=S) (a:=fun _ i=> V*u^a i) hδ' hn hx,sum_comm]
    apply sum_congr rfl;intro j _;rw [niche_gains h]
    exact map_sum (star hF hT hT' hδ' hn (fun i=>hx i (j i))) _ _
 change |sonic F (aisle u v f) _| ≤ _
 rw [he];refine (abs_sum_le_sum_abs ..).trans (le_trans (sum_le_sum (fun t _=>abs_sum_le_sum_abs ..)) ?_)
 unfold D;rw [sum_mul,sum_mul];apply sum_le_sum;intro t _;rw [sum_mul,sum_mul];apply sum_le_sum; intro i _
 by_cases hl:t.val + ∑ z,k i z ≤ h
 · have hY:Tape n m:=i
   have hh(j:Fin n):a (i j)≤h:=(single_le_sum (s:=Finset.univ) (f:=k i) (fun _ _=> Nat.zero_le _) (mem_univ j)).trans (by omega)
   have hI(j:Fin n):(i j).val<h:=hh j
   have ha:t.val≤h:=by omega
   rw [niche,if_pos ha,show P i=Yurt.inlet ∘ Y i from by funext j t;unfold P S Y posed;rw [if_pos (hI j)];rfl]
   refine (bill_low hB hB' (Y i) (k i) t.val u η hη hF hT hT' V hV hl hd (fun i=>Nat.succ_le_succ (Nat.zero_le _)) (fun j=>(h₁ L o M hL hτ hτ' hδ hP (i j) (y j)).2 (hI j)) f _ hu hu1 hv).trans ((mul_le_mul_of_nonneg_right (mul_le_mul (le_add_of_nonneg_right hj) ?_ hB' (hw t)) hη'))
   exact le_add_of_nonneg_right (mul_nonneg hT' (pow_nonneg hu _))
 push Not at hl
 have ht':beam d hs0 (niche h u v f t) ≤ (Q*beam d hη f)*u^t.val:=(H _ _ f t hv hu hu1 hu').trans_eq (by ring)
 refine (bill_high (stance (Loc G 1)) (P i) (k i) t.val V (Q*beam d hη f) u _ hF hT hT' hV hu hu1 (mul_nonneg hQ hη') hδ' hn (fun z=>hx z (i z)) ht' hl).trans ?_
 calc
 _ = W₂*(T*u^(h+1))*beam d hη f:=by unfold W₂;ring
 _ ≤ _:=by exact mul_le_mul_of_nonneg_right (mul_le_mul (le_add_of_nonneg_left (hz t)) (le_add_of_nonneg_left hB') (mul_nonneg hT' (pow_nonneg hu _)) (hw _)) hη'
end YM.RG08.Yurt
