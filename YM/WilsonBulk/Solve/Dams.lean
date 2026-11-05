import YM.WilsonBulk.Solve.Basin

/-!
# Pair-rate barrier; no unbounded cutoff pay. Includes proof of all-order Ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Shop
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {ℓ i k n N N' e E : ℕ} {x C θ δ : ℝ} {p q r v : ℝ→ℝ} {U : Shop H}
def spillBill (G : Gauge) (e n E : ℕ) (x : ℝ) := (1+x*x)*levyΔ G E e n x+hopDiff e n x
lemma spill_tag (G : Gauge) (e n E : ℕ) : Tariff (spillBill G e n E) := (((Tariff.const 1 zero_le_one).add (Tariff.one.prod Tariff.one)).prod (difference_formula ..)).add (hopsΔ_tag ..)
-- simplify algebraic for horizon
lemma ease_bound {M Y Z F : ℝ} {σ τ Q : ℝ} (h : M ≤ 1+Q*Q) (hv : 0≤Y) (hz : 0≤Z) (hf : 0≤F) (hp : 0≤ τ) (he : τ≤x) (hy : 0≤δ) (hs : M*σ≤ C) :
    M*(σ*(δ*Y)+τ*Z)+τ*F≤ C*(δ*Y)+x*((1+Q*Q)*Z+F) := by
  calc
   _ = (M*σ)*(δ*Y)+τ*(M*Z+F) := by ring
   _ ≤ C*(δ*Y)+τ*((1+Q*Q)*Z+F) := add_le_add (mul_le_mul_of_nonneg_right hs (by positivity)) (mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_right h hz) F) hp)
   _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right he (add_nonneg (mul_nonneg (add_nonneg zero_le_one (mul_self_nonneg Q)) hz) hf)) _
lemma pair_main (hG : G.Simple) (hp : Tariff p) (h : PriorGoods U p e (n+1)) (he : 0< e) (hE : e ≤ U.E) (hf : 1≤n) (hn : n ≤ e+1)
    (hM : Tariff q) (hh : U.Mono U.main 0 e (n+1) q) (hy : U.Mono U.raw 1 e (n+1) q) :
    ∃ (q' : ℝ→ℝ), Tariff q' ∧ U.Twin U.main 0 e (n+1) q' := by
  let Q x:= refill U p x+ refill U q x; have hQ : Tariff Q:= (refillCost U _ hp).add (refillCost U _ hM)
  have hhQ : Prizes (refill U p) Q:= prizes_right (refillCost _ _ hM); have hQ' : Prizes (refill U q) Q:= prizes_left (refillCost _ _ hp)
  let F x:= U.book x * spillBill G e n U.E (Q x)+2*q x; have hF: Tariff F:= (U.ticket.prod ((spill_tag ..).composed hQ)).add ((Tariff.const 2 (by norm_num)).prod hM)
  have harc (x : ℝ) (hx : 1≤x) : 2*q x ≤ F x:= by let k:= zero_le_one.trans hx; exact le_add_of_nonneg_left ((U.ticket.prod ((spill_tag ..).composed hQ)).1 x k) -- unicode var ⚬ ok?
  obtain ⟨B,hB⟩:= lullaby F hF (U.a-U.b) (sub_pos.mpr U.has)
  have hv : U.Mono U.main 0 e (n+1) B := Mono.more hh (fun x hx=> (le_mul_of_one_le_left (hM.1 x (zero_le_one.trans hx)) one_le_two).trans ((harc x hx).trans (hB.above x hx)))
  refine ⟨B,hB.bill, fun ℓ k x P i N N' hm hi ha=>?_⟩ -- syntax
  let Y := age A.S k x; change i≤N at hi; refine ⟨(damp_pos ..).le,hv ℓ k x P i N hm hi,hv ℓ k x P i N' hm (by omega),?_⟩; induction hi using Nat.decreasingInduction with
  | self=>
     have hX := (hh ℓ k x P N N hm le_rfl).sub (hh ℓ k x P N N' hm ha); refine hX.mono le_rfl ?_; rw [show U.fall N N=1 from damp_self ..,one_mul,← two_mul]; exact (harc _ (P.wisdom _)).trans (hB.above _ (P.wisdom _))
  | of_succ i hi ih=>
     let R:=Q (Y i); have hs: 0≤R:= P.conscious i hQ; have ht: refill U p (Y i) ≤ R:= hhQ _ (P.wisdom i)
     have ht' := hQ' _ (P.wisdom i)
     have hU : U.Mora U.raw i N' e (n+1) R := (hy ℓ k x P i N' hm (by omega)).mono le_rfl ((refill_orig hM _ (P.wisdom i)).trans ht')
     have hV : U.Mora U.main (i+1) N' e (n+1) R:= (hh ℓ k x P (i+1) N' (by omega) (by omega)).mono le_rfl ((P.refill_neighbor hM hm).trans ht')
     have hr := P.LeviedΔ hp h hm hi ha hG he hE hf hn ht hV (ih (by omega)); have hz:= P.WelledΔ hp h hm hi ha he ht hU hr; let δ' := U.fall (i+1) N; let δ:= U.fall i N; have hd : 0≤δ':= (damp_pos ..).le; have hx': 0 ≤ δ:= (damp_pos ..).le; have h' : δ' ≤δ * U.book (Y i):= (harvest A.S (U.has.trans U.aha).le).trans (mul_le_mul_of_nonneg_left (P.sizes _ hm) hx')
     have hp' := hB.replenish A.S k x i P.roof
     have hL:= P.large i hm n hf (by omega); have he' : U.rDeep i ≤ 1+R*R:= ((P.tarmac _ _ hm hi).more ((refilled hp _ (P.wisdom i)).trans ht)).reflectPrice
     have hpU : U.rise i (i+1) * (δ'*B (Y (i+1))) = δ*(damp A.S (U.a-U.b) i (i+1)* B (Y (i+1))) := by
       have hv := triangle_wall (a:=U.a-U.b) (b:=U.b) (x:= B (Y (i+1))) (i:=i) (j:=i+1) (k:=N) A.S; rw [sub_add_cancel] at hv; exact hv
     refine hz.mono le_rfl ?_
     calc _ ≤ U.rise i (i+1)*(δ'*B (Y (i+1))) + (δ*U.book (Y i))*spillBill G e n U.E R := ease_bound he' (P.conscious (i+1) hB.bill) ((difference_formula ..).1 R hs) ((hopsΔ_tag ..).1 R hs) hd h' hd hL
          _ = δ*(damp A.S (U.a-U.b) i (i+1)*B (Y (i+1))+U.book (Y i)*spillBill G e n U.E R) := by rw [hpU]; ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ hx'; apply le_trans ?_ hp' -- fix
            exact add_le_add_right (le_add_of_nonneg_right (mul_nonneg (by norm_num) (P.conscious i hM))) _
end YM.WilsonBulk.Parapet.Shop
