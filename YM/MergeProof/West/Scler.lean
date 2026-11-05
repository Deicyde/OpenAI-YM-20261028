import YM.MergeProof.West.Flight
import YM.MergeProof.West.Mileage
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {p n i k j q d:ℕ} {X:Levels G}(R:Lead G X.S p)(P:Fin n→poly (Chamber G X.S k p))
variable {x:Points n}{s:ℝ}
variable (h:j≤k) (hv:middle X s k ≤ j) (hx:roomTest X s k p d q)
    (hf:∀ i,middle X s k ≤ i → i < k → Mote (A:=X) R i)
    (hp:∀ i,∀ f∈(P i).vars,fog X x s p 8 (walls (clim X k)) le_rfl i f)
include hv hx hf hp
lemma parts_flee (A B : Finset (Fin n))(hD : Disjoint A B) (ht:∀ i∈A,∀ j'∈B, 3*walls (clim X j)<separation (core X x s p h i) (core X x s p h j')) : heads R P h (scene (A∪B))=heads R P h (scene A)*heads R P h (scene B):=by
  induction h using Nat.decreasingInduction with
  | self=> unfold heads; simp only [center_shelf]; exact prod_union hD
  | of_succ j hr H=>
    let Q:= X.clock.op j p; let b:= walls (clim X j); let W:=walls (clim X (j+1)); let T:= travels hr R P (hv.trans (Nat.le_succ _)) hx hf hp; let L:=heads R P hr
    let d₁:=core X x s p hr; let d₀:=core X x s p hr.le
    have hb : 10≤q:=by have hh:=hx.radius; omega
    have ha : L (scene (A∪B))=L (scene A)*L (scene B):=by
      apply H (hv.trans (Nat.le_succ j)); intro i hi i' hi'; by_contra! he
      have hh:=spends_aloft X hx hr hv (d₁ i) (d₁ i') (he.trans (Nat.mul_le_mul_right _ (show 3≤q by omega)))
      have H:= ht i hi i' hi'; simp only [itinerary _ _ _ _ hr] at H; exact (Nat.not_lt_of_ge (hh.trans (Nat.le_mul_of_pos_left b (by norm_num)))) H
    rw [show heads R P hr.le _= (R j).read (L (scene (A∪B))) from shelving R hr _, ha,show heads R P hr.le (scene A)=_ from shelving R hr _, show heads R P hr.le (scene B)=_ from shelving R hr _]
    apply bridge; intro i hi u hu; obtain ⟨-,a,ha,hp⟩:=mem_filter.mp (T (scene A) hi); obtain ⟨-,e,he,hq⟩:= mem_filter.mp (T (scene B) hu)
    have h₁:= spends_aloft X hx hr hv _ _ (hp.trans (Nat.mul_le_mul_right _ (show 8≤q by omega)))
    have h₂:= spends_aloft X hx hr hv _ _ (hq.trans (Nat.mul_le_mul_right _ (show 8≤q by omega)))
    specialize ht a ha e he; rw [itinerary _ _ _ _ hr,itinerary _ _ _ _ hr] at ht; contrapose! ht
    exact le_trans (separation_triangle ..) (le_trans (add_le_add h₁ ((separation_triangle ..).trans (add_le_add ((hf _ hv hr).foley i u ht) ((separation_comm ..).trans_le h₂)))) (by omega))

abbrev Manner (n : ℕ):= flame (Fin n)
def cosy (A:Levels G)(x:Points n)(s:ℝ)(p d B:ℕ)(h:j≤k)(u:Manner n):Prop := ∀ i∈u.val.val,∀ j ∈ u.val.val,separation (core A x s p h i) (core A x s p h j) ≤ d*B

theorem a_schism (hn : 3*n ≤ d) (Y:Manner n) (hy:¬cosy X x s p d (walls (clim X j)) h Y): vista R P h Y.val=0 := by
  unfold cosy at hy; push_neg at hy; obtain ⟨u,hu,v,hV,hpY⟩:= hy
  let F:=core X x s p h; let B:= walls (clim X j); let W:= Y.val.val; let R':=glows F W (3*B)
  let U:= W.filter (ReflTransGen R' u); let V:=W \ U
  have ht: v ∈ V := mem_sdiff.mpr ⟨hV,fun h=> by
    have hx:= trek (c:=F) (S:=W) (d:=3*B) (mem_filter.mp h).2
    have he : W.card ≤ n:= (card_le_univ ..).trans (by simp)
    exact hpY.not_ge (hx.trans (by
      calc
        _ ≤ n*(3*B):=Nat.mul_le_mul_right _ he
        _ = (3*n)*B:=by ring
        _ ≤ d*B:= Nat.mul_le_mul_right _ hn))⟩
  have hU:u∈U:= mem_filter.mpr ⟨hu,.refl⟩
  have hs (a)(ha:a∈U)(b)(hb:b∈V): 3*B < separation (F a) (F b):= by
    obtain ⟨ha,h₁⟩:=mem_filter.mp ha; obtain ⟨hb,h₂⟩:=mem_sdiff.mp hb
    by_contra! h
    exact h₂ (mem_filter.mpr ⟨hb,h₁.tail ⟨ha,hb,h⟩⟩)
  have hK : Disjoint U V:= disjoint_sdiff; have hh: U∪V=W:= union_sdiff_of_subset (filter_subset ..)
  apply audible; intro a; let M:= spunW R P h a
  have he : (medicine (yolk _) M).part Y.val=0:= by
    refine splits_apart M (by change text a (heads _ _ _ _)=_; rw [oneView]; exact map_one _) U V hK ⟨u,hU⟩ ⟨v,ht⟩ Y.val hh.symm ?_
    intro l hl
    let A':=l.val∩U; let B':=l.val∩V
    change text a (heads _ _ _ l)= text a _ * text a _
    let T:= parts_flee R P h hv hx hf hp A' B' (hK.mono inter_subset_right inter_subset_right) (fun i hi j hj=> hs i (mem_inter.mp hi).2 j (mem_inter.mp hj).2)
    have hF: scene (A'∪B')=l:= Subtype.ext (show (l.val∩U)∪(l.val∩V)= l.val by rw [← inter_union_distrib_left,hh]; exact inter_eq_left.mpr hl)
    rw [hF] at T; rw [T]; exact map_mul ..
  rw [show text _ _=(t_cum R P h a).part Y.val from rfl, vista_eq,he]; exact (map_zero _).symm
end YM.Next.Rank.Tapes.West
