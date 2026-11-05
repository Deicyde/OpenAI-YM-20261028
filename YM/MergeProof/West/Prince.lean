import YM.MergeProof.West.Flag
import YM.Next.RANK.Canal



/-!
# Full realignment one paid tick
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V I ι κ β : Type} [Fintype ι] [Fintype κ]
variable {C : Family G} {i k l j m p q d D a N : ℕ}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i≤k} {h : middle C.path.levels b k ≤ i}

section
variable {P : BudgetPoint} {S : Era}
variable (W : Bale C k b p a x hk→ SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN)))
variable (hp : princFt C P hN x b hk q a p W)
include hp in
lemma perFt {Z : ℝ} (hZ : 0 ≤ Z) (c e y : ℝ) (h : ∀ i,(W i).pays P (fun _=>c) e Z) (he : (↑(2^m:ℕ):ℝ)*Z ≤ y) : Shine W P (fun _=>c) e y:= by
  refine ⟨fun _=>Z,h,fun i=>?_⟩
  rcases i with ⟨u,t⟩
  have hE (j : Bale C k b p a x hk) (h:(u,t)∈(W j).fires.val) : u=j.1:= by rw [(hp j).2] at h; exact mem_singleton.mp (mem_product.mp h).1
  let J:= PatchPt x b C.path.levels p a hk
  have ht:Fintype.card J ≤ 2^m:= (Fintype.card_subtype_le _).trans (fire_size.trans (by rw [Fintype.card_fin]))
  apply le_trans _ he
  change (∑ x:CellP C k b p × J, _) ≤ _
  rw [Fintype.sum_prod_type]; rw [sum_eq_single (show CellP C k b p from u)]
  · calc
      _ ≤ ∑ _ : J, Z:= sum_le_sum fun x hx=>by split_ifs; exact le_rfl;exact hZ
      _ ≤ (↑(2^m:ℕ):ℝ)*Z := by rw [sum_const, card_univ, nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hZ
  · intro j _ hb; apply sum_eq_zero; intro k _; exact if_neg fun h=> hb (hE _ h).symm
  simp

variable (he : P.B=walls (clim C.path.levels i))
variable (F : ι→SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN)))
include he hp hN in
private lemma constFt (H : middle C.path.levels b k ≤ i) (hv : Fit C.path.levels b k x) (hz : Allowed C.path.levels b k)
    (hK : roomTest C.path.levels b k p a q) (v : ι → Bale C k b p a x hk) (ha : ∀ i,(F i).fires=(W (v i)).fires) {s N : ℝ} {p' : ι → ℝ} (hB : 0 ≤ s) (hC : 0 ≤ N) (hh : ∀ i,0≤p' i)
    (hg : ∀ u : (Ship.yard C b hN p).Cell× Fin m,∑ j, (if u∈(F j).fires.val then p' j else 0) ≤ N) (t : Site (C.side i p)) :
    ∑ i,(if t∈(W (v i)).extent then p' i*Value.charge P s (W (v i)).extent else 0) ≤ (m:ℝ)*N* rentQ q s:= by
  let r:= rentQ q s; let X i:=(W i).extent; let f i:= if t∈ X (v i) then p' i* Value.charge P s (X (v i)) else 0
  change ∑ i,f i ≤ _
  have hx i: Value.charge P s (X (v i)) ≤ r:= by unfold X; rw [(hp _).1]; exact hall q P hB
  have hr:0≤r:= (Real.exp_pos _).le
  by_cases hQ : ∃ i:ι,t ∈ X (v i)
  · obtain ⟨j,hj⟩:=hQ
    let Z:=(v j).1; let g (i) (t : Fin m):= if (Z,t) ∈ (F i).fires.val then p' i else 0
    have he' i: f i≤ (∑ x:Fin m,g i x)*r:= by
      have h (u):0≤g i u:= by unfold g;split;exact hh i;exact le_rfl
      unfold f;split
      · rename_i hQ
        have H' : (v i).1=Z:= t_ightFt C b x q a H hK hz hv P.B he (v j) (v i) hN ((hp _).1 ▸ (show t∈(W (v j)).extent from hj)) ((hp _).1 ▸ (show t∈(W (v i)).extent from hQ))
        obtain ⟨⟨u,T⟩,hU⟩:= (F i).chosen
        have hv': u=Z:= ((mem_singleton.mp (mem_product.mp (show (u,T)∈(litFt p hN b C (v i).1 (v i).2.val).val from ((ha i).trans (hp _).2) ▸ hU)).1)).trans H'
        refine (mul_le_mul_of_nonneg_left (hx _) (hh _)).trans (mul_le_mul_of_nonneg_right ?_ hr); refine le_trans (b:=g i T) ?_ (single_le_sum (fun t _=>h t) (mem_univ T))
        exact (if_pos (hv' ▸ hU)).symm.le
      exact mul_nonneg (sum_nonneg fun j _=> h j) hr
    refine (sum_le_sum fun i _=> he' i).trans ?_; rw [← sum_mul, sum_comm]
    apply mul_le_mul_of_nonneg_right _ hr
    apply (le_trans (sum_le_sum (g:=fun _=>N) (fun i _=>hg (Z,i))))
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (le_rfl) hC
  rw [show ∑ i, f i=0 from sum_eq_zero fun i _=> if_neg fun h=> hQ ⟨i,h⟩]; exact mul_nonneg (mul_nonneg (by norm_num) hC) hr
end

-- keep hit and Bg. charge at P and all raw outputs, pre-step geometry & costs.
section
variable (P : Rep G (C.side i p))
variable (F : Bale C k b p a x hk → SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN)))
variable {z r c Z δ D y g s u : ℝ} {d : ℕ}
variable [Fintype I] (H : ι → SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN)))
variable (S : κ → SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN))) (K : I→Lifted G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN)) P.p.threshold)

lemma resFt (h : princFt C P.p hN x b hk q a p F) (he : Fit C.path.levels b k x)
    (hp : Allowed C.path.levels b k) (hi : middle C.path.levels b k ≤ i) (hx : roomTest C.path.levels b k p a q) (hP : P.p.B=walls (clim C.path.levels i)) (hW : ∀ i,Carport (a*P.p.B) (S i) (q*P.p.B))
    (h₀ : Background P K) (h₂ : Shine S P.p (fun _=> r) c Z) (hw : 0 ≤ Z) (hb : 0<r) (hB : r≤1) (hc : 0 ≤ c)
    (h₁ : Shine H P.p (fun _=> r) c z) (hK : Stripes P.p K (fun _=>r) (c+1) s) (hJ : 0 ≤ δ) (hg : 0≤ g)
    (hM : Real.exp g * s + (m:ℝ)*Z*rentQ q (c+1) ≤ δ) (ht : (↑((P.p.B+P.p.B+1):ℕ):ℝ)^4*δ ≤ 1)
    (hu : ∀ j U, Healthy P.p.threshold (d_olm x b q P.p.B hN hk j.1 j.2.val) U →
      ‖((∑ t, if (S t).fires = (F j).fires then (S t).value U else 0)-(F j).value U)‖ ≤ y) (hy : 0≤ y) :
      ∃ (β α : Type), ∃ (_ : Fintype β) (_ : Fintype α), ∃ (H' : β→SourceAt G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN)))
        (K' : α→ Lifted G (readers (C:=C) (b:=b) (p:=p) x hN (hk.trans hN)) P.p.threshold),
        Value.dust P (Sum.elim H S) K= Value.dust P (Sum.elim H' F) K' ∧ Background P K' ∧ Light P H' K' (fun _=>r) c (z+(↑(2^m:ℕ):ℝ)*(rentQ q c*y))
          (Real.exp (-g)*(Real.exp δ-1)) := by
  choose v he' ht' using fun i=> f_pair (hk:=hk) hi hx he hp (S i) P.p.B hP (hW i)
  have hf i : (S i).extent ⊆ (F (v i)).extent:=(h _).1.symm ▸ ht' i
  have hF i:(S i).fires=(F (v i)).fires := (he' i).trans (h _|>.2).symm
  let L:= partnerW S F v hf; let Φ:=fun i=> messages S F v hf i P.p.threshold; let X:=merged K Φ
  refine ⟨_,_,inferInstance,inferInstance,Sum.elim H L,X,funext (enact S F v hF hf P K H),fun i U=> (monogous K Φ i U).trans (h₀ ..),Shine.plus H L h₁ ?_,?_⟩
  · have hq: princFt C P.p hN x b hk q a p L:= fun i=> h i
    let u:=rentQ q c*y; have hp: 0≤ u:= mul_nonneg (Real.exp_pos _).le hy
    apply perFt L hq hp r c _ _ le_rfl
    intro i; refine ⟨hp,fun U hh=>?_⟩
    have heS: Value.charge P.p c (L i).extent ≤ rentQ q c:= by rw [(hq i).1];exact hall q P.p hc
    have hi:Poly.toll (fun _:(Ship.yard C b hN p).Cell × Fin m=>r) (L i).fires ≤ 1:= by unfold Poly.toll; rw [prod_const];exact pow_le_one₀ hb.le hB
    have hI: Injective (fun i=> (F i).fires):= fun t v he=> by
      have hz := torches hN b p (C:=C) (a₁:=(t.1,t.2.val)) (a₂:=(v.1,v.2.val)) (((h t).2).symm.trans (he.trans (h v).2)); have hF:= congr_arg Prod.fst hz; have hB:= congr_arg Prod.snd hz; exact Prod.ext hF (Subtype.ext hB)
    have ht: ‖(L i).value U‖≤y:= by
      have hv:= hu i U ((hq i).1 ▸ hh); rw [show (L i).value U= (∑ j, if (S j).fires=(F i).fires then (S j).value U else 0)-(F i).value U from ?_]; exact hv
      refine congr_arg (· -(F i).value U) (sum_congr rfl (fun j h=>?_))
      rw [hF]; split_ifs with hy hu hu; exacts [rfl, False.elim (hu (congr_arg SourceAt.fires (congr_arg F hy))), False.elim (hy (hI hu)), rfl]
    exact mul_le_mul ((mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le).trans (by rw [mul_one]; exact heS)) ht (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨b,hH,hb'⟩:=h₂
  exact landed S F v hf P K (fun _=> hb) _ hJ hc hH hK (fun i=>rfl) (constFt F h hP S hi he hp hx v hF (add_nonneg hc zero_le_one) hw (fun i=> (hH i).1) hb') hM ht hg
end
end YM.Next.Rank.Tapes.West
