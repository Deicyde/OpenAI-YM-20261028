import YM.MergeProof.West.Flight
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Station
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {p n i k j q d:ℕ} {S : Schedule}
variable (R:Lead G S p)(P:Fin n → poly (Chamber G S k p)) (h : j ≤ k)

section
variable (H:∀ i, j ≤ i→ i<k→ Tapes.Voice R i)(hp:∀ i,Poetic (P i))
include H hp

end

variable {X:Levels G}(R:Lead G X.S p)(P:Fin n→poly (Chamber G X.S k p))
variable {x:Points n}{s:ℝ}

variable (hv:middleSky X s k ≤ j) (hx:roomTestSky X s k p d q)
    (hf:∀ i,middleSky X s k ≤ i → i < k → Mote (A:=X) R i)
    (hp:∀ i,∀ f∈(P i).vars,fog X x s p 8 (walls (clim X k)) le_rfl i f)
include hv hx hf hp
lemma travelsSky (T:modes (Fin n)): (heads R P h T).vars ⊆ flock X s x T.val (8*walls (clim X j)) h:=by
   unfold heads
   induction h using Nat.decreasingInduction with
   | self=>
     rw [center_shelf]; generalize  T.val=S
     induction S using Finset.induction_on with
     | empty=>simp
     | insert i v hv IH=>
       rw [prod_insert hv]; refine Subset.trans (vars_mul ..) (union_subset ?_ ?_)
       · intro f h; exact mem_filter.mpr ⟨mem_univ _,i,mem_insert_self ..,hp i f h⟩
       intro f h; obtain ⟨-,a,ha,hh⟩:= mem_filter.mp (IH h); exact mem_filter.mpr ⟨mem_univ _,a,mem_insert_of_mem ha,hh⟩
   | of_succ j H IH=>
     rw [shelving _ H]; apply pipe_vars; intro i hi f hF
     obtain ⟨-,a,hA,hB⟩:= mem_filter.mp (IH (hv.trans (Nat.le_succ _)) hi); refine mem_filter.mpr ⟨mem_univ _,a,hA,?_⟩
     rw [itinerary _ _ _ _ H]; have hh:= spends_aloftSky X hx H hv _ _ (hB.trans (Nat.mul_le_mul_right _ (show 8≤ q by have he:=hx.radius; omega)))
     apply (separation_triangle ..).trans ((add_le_add hh ((hf j hv H).pole _ _ hF)).trans ?_); omega
lemma emigratesSky (w:modes (Fin n)): (vista R P h w).vars⊆flock X s x w.val (8*walls (clim X j)) h:=by
   let A:=flock X (p:=p) s x w.val (8*walls (clim X j)) h
   let L:=heads R P h; let Z:=yolk (Fin n) w
   have he (i : ℝ × List (modes (Fin n))) (m:modes (Fin n)) (ht:i∈Z) (hM:m∈i.2): (L m).vars⊆A:=by
     intro f hf'; obtain ⟨hB,a,ha,hq⟩:= mem_filter.mp (travelsSky h R P hv hx hf hp m hf')
     exact mem_filter.mpr ⟨mem_univ _,a,yolk_club w _ ht _ hM ha,hq⟩
   have hp' (l : List (modes (Fin n))) (H:∀ i∈l,(L i).vars⊆A): (l.map L).prod.vars⊆A:=by
     induction l with
     | nil=>simp
     | cons i l IH=> simp only [List.map_cons,List.prod_cons]; exact Subset.trans (vars_mul ..) (union_subset (H i (List.mem_cons_self ..)) (IH (fun k hk=> H k (List.mem_cons_of_mem _ hk))))
   have hh (V:Clump (modes (Fin n))) (hv:V⊆Z) : (honors V L).vars⊆A:=by
      induction V with
      | nil=>simp [honors]
      | cons i l IH=>
        rw [show honors (i::l) L=C (↑i.1)*(i.2.map L).prod+honors l L from rfl]
        exact Subset.trans (vars_add_subset ..) (union_subset (Subset.trans (vars_mul ..) (union_subset (by simp) (hp' _ (fun j=> he _ _ (hv (List.mem_cons_self ..)))))) (IH fun i hi=>hv (List.mem_cons_of_mem _ hi)))
   exact hh Z (List.Subset.refl _)
end YM.Next.Rank.Tapes.West
