import YM.MergeProof.West.Seal
import YM.Next.RANK.CircleSense
import YM.Next.RANK.Currents

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {p n i k j q d:ℕ} {S : Schedule}
variable (R:Lead G S p)(P:Fin n → poly (Chamber G S k p)) (h : j ≤ k)
def heads (T : modes (Fin n)) := shelve R h (∏ i ∈ T.val, P i)
lemma oneView : heads R P h (quiet _) = 1:= by
  unfold heads; rw [show (quiet _).val=∅ from rfl,prod_empty]; induction h using Nat.decreasingInduction with
  | self=> rw [center_shelf]
  | of_succ j h H=> rw [shelving R h,H]; simp [Valve.read,pipes]
def vista (T : modes (Fin n)) := honors (yolk (Fin n) T) (heads R P h)
def spunW (x : Chamber G S j p→ℝ) :veil (Fin n) := Poly.inject fun i=> text x (heads R P h i)
def t_cum (x : Chamber G S j p→ℝ) :veil (Fin n) := Poly.inject fun i=> text x (vista R P h i)
lemma vista_eq (x: Chamber G S j p→ℝ) : t_cum R P h x=medicine (yolk _) (spunW R P h x) := by
  ext i; exact g_honors (A:=poly _) (aeval (R:=ℂ) (fun i=> (x i:ℂ))) _ _
lemma expanders (x: Chamber G S j p→ℝ) : Expands (t_cum R P h x) (spunW R P h x):=by
   rw [vista_eq]; apply belly; change text x (heads _ _ _ _)= _; rw [oneView]; exact map_one _
lemma forgotten : vista R P h (quiet _)=0:= audible _ _ (fun x=>by rw [show text x _=0 from (expanders R P h x).1];exact (map_zero _).symm)
section
variable (H:∀ i, j ≤ i→ i<k→ Tapes.Voice R i)(hp:∀ i,Poetic (P i))
include H hp
lemma woven (T : modes (Fin n)) : Poetic (vista R P h T):= by
   let V:=heads R P h; intro u
   rw [vista,g_honors, show exchange (coloration (S.side j p) u) ∘ heads R P h=V from ?_]
   funext i; exact sung R _ h H (fun u=> by rw [_root_.map_prod];exact prod_congr rfl fun i _=> hp i _) u
end

variable {X:Levels G}(R:Lead G X.S p)(P:Fin n→poly (Chamber G X.S k p))
variable {x:Points n}{s:ℝ}
def flock (A:Levels G) {k i n p:ℕ}(s:ℝ)(x:Points n)(T:Finset (Fin n)) (B:ℕ) (h:i≤k) := univ.filter (fun f:Chamber G A.S i p => ∃ a∈T, separation (core A x s p h a) f.1≤ B)
variable (hv:middle X s k ≤ j) (hx:roomTest X s k p d q)
    (hf:∀ i,middle X s k ≤ i → i < k → Mote (A:=X) R i)
    (hp:∀ i,∀ f∈(P i).vars,fog X x s p 8 (walls (clim X k)) le_rfl i f)
include hv hx hf hp
lemma travels (T:modes (Fin n)): (heads R P h T).vars ⊆ flock X s x T.val (8*walls (clim X j)) h:=by
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
     rw [itinerary _ _ _ _ H]; have hh:= spends_aloft X hx H hv _ _ (hB.trans (Nat.mul_le_mul_right _ (show 8≤ q by have he:=hx.radius; omega)))
     apply (separation_triangle ..).trans ((add_le_add hh ((hf j hv H).pole _ _ hF)).trans ?_); omega
lemma emigrates (w:modes (Fin n)): (vista R P h w).vars⊆flock X s x w.val (8*walls (clim X j)) h:=by
   let A:=flock X (p:=p) s x w.val (8*walls (clim X j)) h
   let L:=heads R P h; let Z:=yolk (Fin n) w
   have he (i : ℝ × List (modes (Fin n))) (m:modes (Fin n)) (ht:i∈Z) (hM:m∈i.2): (L m).vars⊆A:=by
     intro f hf'; obtain ⟨hB,a,ha,hq⟩:= mem_filter.mp (travels h R P hv hx hf hp m hf')
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
