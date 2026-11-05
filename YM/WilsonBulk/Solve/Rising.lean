import YM.WilsonBulk.Solve.Dams

/-!
# Ledger issued, conditional on admissible finite kbulk Land

Proof supports any number of steps beyond ℓ. Exponential widths before k changes; moments infinite
via finite arithmetic. Constants not a hidden selection after N; polynomial on post-L choices. See `Land`.
Need footprint limits instantiated via complete horizon above geometric demands (`StepAgenda`). This
file does NOT yet discharge on such joint smoothing data. It computes pairwise overlaps given geometric
and FLAT/Toll contracts on only such data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Shop
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {ℓ i k n N N' e E : ℕ} {x C θ δ : ℝ} {p q r v : ℝ→ℝ} {U : Shop H}
lemma pair_press (hG : G.Simple) (hp : Tariff p) (h : PriorGoods U p e (n+1)) (he : 0< e) (hE : e ≤ U.E) (hf : 1≤n) (hn : n ≤ e+1)
    (hM : Tariff q) (hh : U.Twin U.main 0 e (n+1) q) (hy : U.Mono U.raw 1 e (n+1) q) :
    ∃ (q' : ℝ→ℝ), Tariff q' ∧ U.Twin U.raw 1 e (n+1) q' := by
  let Q x:=refill U (fun x=>p x+q x) x; have hQ: Tariff Q:= refillCost _ _ (hp.add hM)
  have hhQ : Prizes (refill U p) Q:= refill_more (prizes_right hM); have hQ' : Prizes (refill U q) Q:= refill_more (prizes_left hp)
  let F x:= U.book x*(Q x+ levyΔ G U.E e n (Q x)); have hF : Tariff F:= U.ticket.prod (hQ.add ((difference_formula G U.E e n).composed hQ))
  let u:=Mono.more hy (prizes_right hF); refine ⟨_,hM.add hF, fun ℓ k x P i N N' hi he' ht =>?_⟩ -- syntax
  have hN : i<N:= he'; let Y:= age A.S k x; let p':=Q (Y i); obtain hB:= hh _ _ _ P (i+1) N N' (by omega) hN ht; have hz:= hB.more le_rfl ((P.refill_neighbor hM hi).trans (hQ' _ (P.wisdom i))) le_rfl; have hP : 0 ≤ levyΔ G U.E e n p':= (difference_formula G U.E e n).1 p' (P.conscious i hQ); let δ:= U.fall i N; let δ':=U.fall (i+1) N; have hx' : 0≤δ:= (damp_pos ..).le
  have hl : δ' ≤ δ*U.book (Y i):= (harvest A.S (U.has.trans U.aha).le).trans (mul_le_mul_of_nonneg_left (P.sizes i hi) hx'); have hb := P.LeviedΔ hp h hi hN ht hG he hE hf hn (show refill U p (Y i) ≤ p' from hhQ _ (P.wisdom i)) hz.minus hz.variation; refine ⟨hx',u ℓ k x P i N hi he',u _ _ _ P i N' hi (by omega), hb.mono le_rfl ?_⟩
  calc _ ≤ δ'*(p'+levyΔ G U.E e n p') := by rw [mul_add]; exact add_le_add_left (mul_le_of_le_one_left hz.variation.1 (P.cDeep_small hi hf (by omega))) _
       _ ≤ (δ*U.book (Y i))*(p'+levyΔ G U.E e n p'):= mul_le_mul_of_nonneg_right hl (add_nonneg (P.conscious i hQ) hP)
       _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (prizes_left hM (q:=F) _ (P.wisdom i)) hx'

lemma yearPositive (hG : G.Simple) (hp : ∀ i k,Prior e (n+1) i k → ∃ p,Tariff p ∧ U.Ledger p i k) (he : 0<e) (hE : e ≤ U.E) (hf : 1≤n) (hn : n ≤ e+1) : ∃ p,Tariff p ∧ U.Ledger p e (n+1) := by
  obtain ⟨p,hp,h⟩:= precedent hp; obtain ⟨q,hq,v⟩:= uniform_main hG hp h he hE hf hn; obtain ⟨r,hr,w⟩:= uniform_raw hG hp h he hE hf hn v hq; let t x:=q x+r x; have ht: Tariff t:=hq.add hr; have hv: U.Mono U.main 0 e (n+1) t:= Mono.more v (prizes_right hr); have hw: U.Mono U.raw 1 e (n+1) t:= Mono.more w (prizes_left hq)
  obtain ⟨s,hs,hi⟩:= pair_main hG hp h he hE hf hn ht hv hw; have hs':=hs.add ht; obtain ⟨y,hy,hh⟩:= pair_press hG hp h he hE hf hn hs' (Twin.high hi (prizes_right ht)) (Mono.more hw (prizes_left hs)); exact ⟨_,hs.add hy,Twin.high hi (prizes_right hy),Twin.high hh (prizes_left hs)⟩

lemma tail_clime (U : Shop H) (h : G.Simple) (e n : ℕ) (he : e≤U.E) : ∃ p,Tariff p ∧ U.Ledger p e n := by
  induction e using Nat.strong_induction_on generalizing n with
  | h e ih=>
    by_cases he': n≤e+2; swap; · exact ⟨_, Tariff.one,rankHuge U Tariff.one (by omega)⟩
    suffices H: ∀ x : ℕ,x≤e+2 → ∃ p,Tariff p ∧ U.Ledger p e (e+2-x) from (show e+2-(e+2-n)=n by omega) ▸ H (e+2-n) (by omega)
    intro x hx; induction x using Nat.strong_induction_on with
    | h x hh=>
       let y := e+2-x; by_cases hy : y ≤ 1; · exact ⟨_,Tariff.one, rankLow U h Tariff.one hy⟩
       obtain ⟨r,hr⟩: ∃ r:ℕ,e+2-x=r+1:= ⟨y-1,by unfold y at *; omega⟩
       rw [hr]; unfold y at hy
       by_cases hE : e=0; · subst hE; rw [show r+1=2 by omega]; exact ⟨_,U.ticket,U.Leading_rank⟩
       refine yearPositive h (fun i j hij=> ?_) (by omega) he (by omega) (by omega)
       rcases eq_or_ne i e with rfl|Hj
       · have hk : j>r+1:=hij.2.2 rfl; have ht:=hij.1; exact (show i+2-(i+2-j)=j by omega) ▸ hh (i+2-j) (by omega) (by omega)
       exact ih i (lt_of_le_of_ne hij.2.1 Hj) j (hij.2.1.trans he)

/-- Concurrent height issuer (source consumers may request previous e or any moment, given `Land`). DOESN'T assume uniform lower order expenses; even Ω rank-two resets included. Still requires FLAT+width/completion feasibility, delivered in separate calibration files. Statement phase0.
-/
theorem budgetAll (U : Shop H) (h : G.Simple) : ∃ p,Tariff p ∧ ∀ e ≤ U.E, ∀ n,U.Ledger p e n := by
  let S := (range (U.E+1)) ×ˢ (range (U.E+3)); obtain ⟨p,hp,hv,hP⟩:= prize_all (fun x:ℝ=>x) (fun p (i:ℕ×ℕ)=> U.Ledger p i.1 i.2) (fun h _ _ _ v=> v.more h) S (fun i hi=> tail_clime U h i.1 i.2 (by have he:= mem_range.mp (mem_product.mp hi).1; omega)) Tariff.one
  refine ⟨p,hp,fun i hi n=>?_⟩; by_cases H: n ≤ i+2; · exact hP (i,n) (mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩)
  exact rankHuge _ hp (by omega)
end YM.WilsonBulk.Parapet.Shop
