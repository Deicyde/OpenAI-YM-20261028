import YM.RemainderComparison.Flues.Stoker
import YM.RemainderComparison.Flues.Receipt

/-!
# Exact Mayer at every configuration/probe

Preserves the old compulsory admissibility and conditions. Square-zero or
empty mark footprints handled differently only in exponent, not analytically
on flag surfaces. Polynomials not normed as Banach algebras; use Census
budgets for summability only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums Finset Merge Work.H03
open Mosaic Mosaic.Verse Marker GridRenewal.Rain
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι θ : Type}[DecidableEq θ] {α:Type*} {J : Census θ}
variable (H:Yard ι α G n) (L:Scone ι α G n) (P:BudgetPoint) (root:ι→Support n)(Z:Set ι)
local notation "C" => fireplace H L
variable (F:ℕ ≃ (fireplace H L).Pellet) (a:α) (U:Config G n) (z:ι→Poly J)
variable {k:ℕ} {gV:θ→ℝ} (hZ:Serif.Chorus J gV Z z k)
local notation "D" => flash H L P Z F
local notation "R" => L.plume Z z a U

def cinders (i:ℕ): Poly J:= (Complex.ofReal (L.tinct Z a i U)) • controls Z z (L.glyph i)
local notation "E" => cinders L Z a U z

def ember : Ovens.Label → Poly J := Sum.elim (H.song Z z a U) (cinders L Z a U z)
lemma evaporate {p : Poly J} (hp:p*p=0): cyclone p=1+p:=by
   unfold cyclone; rw [tsum_eq_sum (s:=range 2)]; · simp [Finset.sum_range_succ,term]
   intro i hi; have he:2 ≤ i:=by simp at hi; exact hi
   obtain ⟨i,rfl⟩:=Nat.exists_eq_add_of_le he; rw [term,pow_add,pow_two,hp,zero_mul,smul_zero]
lemma cold (p:Multiset ι) (he:load Z p=0) : controls Z z p=1:=by
   induction p using Multiset.induction_on with
   | empty =>simp [controls]
   | cons i p hi=> unfold controls; rw [Multiset.map_cons,Multiset.prod_cons]; unfold load at he; split
                   next h => simp only [Multiset.filter_cons_of_pos _ h,Multiset.card_cons] at he; omega
                   next h =>rw [one_mul]; rw [Multiset.filter_cons_of_neg _ h] at he; exact hi he
include hZ
lemma burns (p:Multiset ι) (h:load Z p ≠0) : controls Z z p* controls Z z p=0:=by
   induction p using Multiset.induction_on with
   | empty => simp [load] at h
   | cons i p hi=> unfold controls; rw [Multiset.map_cons,Multiset.prod_cons]; split
                   next hv => rw [mul_mul_mul_comm,hZ.square,zero_mul]
                   next hv => unfold load at h; rw [Multiset.filter_cons_of_neg _ hv] at h; rw [one_mul]; exact hi h
lemma ignition i : cyclone (R i)= 1 + E i:=by
   unfold Scone.plume cinders Scone.tinct; split
   next hh=>
      rw [cold Z z _ hh,← beacon,← beacon,clear]; simp only [Complex.ofReal_sub,Complex.ofReal_exp,Complex.ofReal_one]; unfold bead; rw [map_sub,map_one]; ring
   next hh => exact evaporate (by rw [smul_mul_smul_comm,burns Z z hZ (L.glyph i) hh,smul_zero])
local notation "S" => H.gala P Z z a U

def casket (p:Finset ℕ): Poly J := ∏ i∈p,cinders L Z a U z i
local notation "C₁" => casket L Z a U z
local notation "H₀" => H.song Z z a U
variable {r v d b B σ w t y γ σ' : ℝ} {K : ℕ}
-- May activate these even without merging prerequisites
variable (hp:H.Pays Z k K σ b) (he:L.Treasures Z k K σ v d) (hσ:0 ≤ σ)
-- global finite-V summable envelope. no geom costs assigned by these
omit hZ in
lemma registered {f:ℕ→Support n}{q:ℕ→ℝ}(hq:∀ i,0≤ q i)(ht: Ac.Hit f K q σ b)(hN:∀ i,(f i).Nonempty)(hσ:0≤ σ) : Summable q:=by
   have he:= Product.everyone_ne f K hq (fun i _=>hN i) ht
   exact he.2.1.of_nonneg_of_le hq (fun i=> le_mul_of_one_le_right (hq _) (Real.one_le_exp (mul_nonneg hσ (by positivity))))
lemma product_p (f:ℕ→Poly J)(hf: Summable f): Summable (fun i:Finset ℕ=>∏ j∈i,f j):=by
   let q i:=Poly.price gV (f i); have h : Summable q := GridRenewal.Rain.price_sums gV hf
   have hz : Summable (fun i:Finset ℕ=> ∏ j∈i,q j):= summable_finsetProd_of_summable_nonneg (fun _=>Poly.nonnegative hZ.votes _) h
   exact (Poly.budgeted hZ.votes hz (fun i=> Poly.multiple hZ.votes ..)).1
include hp hσ
lemma yard_paid : Summable (H.song Z z a U)∧Summable (H.gala P Z z a U):=by
   obtain ⟨q,hq,hh,h⟩:= hp.wages
   have hv := registered hq hh (fun i=> (H.more i).inventory_ne.mono (H.more i).inventory_sup) hσ
   have ht i:Poly.price gV (H₀ i)≤ q i:= by
     by_cases hz:load Z (H.score i)≤ k
     · unfold Yard.song; refine le_trans ?_ (h i hz a U); rw [Poly.adapted,Complex.norm_real]
       exact mul_le_of_le_one_right (norm_nonneg _) (Serif.bought hZ _)
     unfold Yard.song; rw [hZ.capacity _ (lt_of_not_ge hz),smul_zero,Poly.zero_price]; exact hq i
   have hs := Poly.budgeted hZ.votes hv ht
   refine ⟨hs.1,?_⟩
   let f:= fun i: Finset ℕ=>∏ j∈i,H₀ j; have hi : Summable (fun i=> ‖f i‖):= (product_p Z z hZ _ hs.1).norm
   exact (hi.of_nonneg_of_le (fun i=> norm_nonneg (S i)) (fun i=> by unfold Yard.gala Photo.fronts; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _)).of_norm
omit hp
include he
lemma scone_budget (h: v ≤ 1): Summable (L.plume Z z a U)∧ Summable E∧Summable C₁:=by
   obtain ⟨q,g,hq,hg,hW,hF,hR⟩:= he.wages
   have hv := registered hq hW L.rest hσ; have hz := registered hg hF L.rest hσ
   have hh (i) (x:ℝ) : Poly.price gV ((↑x:ℂ) • controls Z z (L.glyph i))≤ ‖x‖:=by rw [Poly.adapted,Complex.norm_real]; exact mul_le_of_le_one_right (norm_nonneg _) (Serif.bought hZ _)
   let d i:=2*q i+g i; have hr i : 0≤ d i:= add_nonneg (mul_nonneg zero_le_two (hq i)) (hg i); have hd : Summable d:= (hv.mul_left 2).add hz
   have hk i : Poly.price gV (R i) ≤ d i∧ Poly.price gV (E i)≤ d i:=by
      by_cases ht: load Z (L.glyph i) ≤k
      swap; · simp only [Scone.plume,cinders, hZ.capacity _ (lt_of_not_ge ht), smul_zero,Poly.zero_price,and_self]; exact hr i
      have hM:= hR i ht a U; refine ⟨(hh i _).trans (hM.trans ?_),(hh i _).trans ?_⟩
      · split; next=> exact le_trans (b:=2*q i) (le_mul_of_one_le_left (hq _) one_le_two) (le_add_of_nonneg_right (hg _))
        next=> exact le_add_of_nonneg_left (mul_nonneg zero_le_two (hq _))
      unfold Scone.tinct; split
      next h0=> rw [if_pos h0] at hM; rw [Real.norm_eq_abs] at hM ⊢
                exact le_trans (Real.abs_exp_sub_one_le (hM.trans ((PhysicalNext.RecursiveSecants079.BothSides.hit_one hW hσ hq i (L.rest i)).trans h))) ((mul_le_mul_of_nonneg_left hM zero_le_two).trans (le_add_of_nonneg_right (hg _)))
      next h0=> rw [if_neg h0] at hM; exact hM.trans (le_add_of_nonneg_left (mul_nonneg zero_le_two (hq _)))
   have hs:= (Poly.budgeted hZ.votes hd (fun i=> (hk i).2)).1
   exact ⟨(Poly.budgeted hZ.votes hd fun i=> (hk i).1).1,hs,product_p Z z hZ _ hs⟩
variable [Fintype θ]
lemma watch (h:v ≤ 1): HasSum C₁ (cyclone (∑' i,L.plume Z z a U i)):=by
   obtain ⟨hv,hz,hV⟩:=scone_budget L Z a U z hZ he hσ h
   suffices hh : HasProd (fun i=> 1 + E i) (cyclone (∑' i,L.plume Z z a U i)) by
      rw [← hh.tprod_eq, tprod_one_add hV]; exact hV.hasSum
   simp_rw [← ignition L Z a U z hZ]; unfold HasProd; simp_rw [← roaring]; exact breath.continuousAt.tendsto.comp hv.hasSum

def fly (p:Finset Ovens.Label):Poly J := S p.toLeft * C₁ p.toRight
local notation "Y"=> fly H L P Z a U z
include hp
local instance : IsTopologicalSemiring (Poly J) where
lemma circles (h:v≤1): HasSum Y ((∑' i,H.gala P Z z a U i) * cyclone (∑' i,L.plume Z z a U i)):= by
   have hx:=(yard_paid H P Z a U z hZ hp hσ)
   have hy:=watch L Z a U z hZ he hσ h
   let f:=fun i:Finset ℕ × Finset ℕ=> S i.1*C₁ i.2; have hf : HasSum f _ := hx.2.hasSum.mul hy (hybrid hx.2 hy.summable)
   exact (Finset.sumEquiv.toEquiv.hasSum_iff (f:=f)).mpr hf
end YM.RemainderComparison.Flues
