import YM.Push.GRID_APPROXIMATION.Draw
import YM.Push.GRID_APPROXIMATION.Joint

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Hearth
open Filter Set Function Finset Lattice RG Wilson Push GridApprox Cells
open MeasureTheory
open scoped Topology BigOperators Classical
variable {ι:Type*} {S: Schedule} {m N p J:ℕ} {G:Gauge} (H: History G)
lemma backTo_t (q:m≤N) (hk:J≤m)(r:Site (H.S.side J p)){F: Config G (H.S.side m p)→ℂ}(h:Envelope F): backTo H N p q (F ∘ translate (anchor H.S p hk r))= (backTo H N p q F) ∘ translate (anchor H.S p (hk.trans q) r) := by
   have ht:= backTo_orient H N p hk q r 1 h; simp only [Function.comp_def,pull_one] at ht; exact ht
lemma behind (q:m≤J)(f:Config G (H.S.side m p)→ℂ)(v: ℂ) : backTo H N p q (v • f)=v • backTo H N p q f:=by
    induction J,q using Nat.le_induction with
    | base=> simp
    | succ J q ih=>
       rw [backTo_next H N p q,backTo_next H N p q,ih]; let W:=backTo H N p q f; funext U; simp only [back,Pi.smul_apply,smul_eq_mul,mul_left_comm _ v,integral_const_mul]
lemma backTo_sum (q:m≤N)(g:ι→ Config G (H.S.side m p)→ℂ)(L:Finset ι)(h:∀ i∈L,Envelope (g i)): backTo H N p q (∑ i∈L,g i)=∑ i∈L, backTo H N p q (g i):=by
   induction L using Finset.induction with
   | empty=> exact (by simp only [Finset.sum_empty]; exact backTo_const H N p q 0)
   | insert i L hi ih=>
     rw [Finset.sum_insert hi, Finset.sum_insert hi]; have hx j (hh:j ∈ L):=h j (mem_insert_of_mem hh)
     rw [backTo_add H N p q (h i (mem_insert_self ..)),ih hx]; let K:=fun U: Config G (H.S.side m p)=> ∑ i∈L,g i U
     rw [show (∑ i∈L,g i)=K from funext fun U=> by unfold K; rw [Finset.sum_apply]]; exact Envelope.sumC _ _ hx
lemma whereBack (q:m ≤ N) (hk:J ≤ m) (r:ℕ) {F: Config G (H.S.side m p) → ℂ}(h:Interior (window 0 r) F)(hh:GridApprox.room H.levels J m r): Interior ((tilesAt H.S p (hk.trans q)).chamber 0) (backTo H N p q F):=by
    let i:Site (H.S.side J p):=0; rw [← show anchor H.S p hk i=0 from (H.S.toDepth hk p).root.map_zero] at h
    exact (backTo_local H N p hk q i r h).enlarges (room_fits p H.levels _ hk q hh i)
lemma inSum {X:Side}(A:Set (Site X))(f:ι→ Config G X→ℂ)(L:Finset ι)(h:∀ i∈L, Interior A (f i)): Interior A (∑ i∈L,f i):=by
    induction L using Finset.induction with
    | empty=> simp only [Finset.sum_empty]; exact Interior.constant ..
    | insert i L hi ih=> rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hh=> h j (mem_insert_of_mem hh))
lemma room_small (S:Levels G) {r k:ℕ}(hx:r ≤ k)(h:GridApprox.room S J m k): GridApprox.room S J m r:=by
    unfold GridApprox.room at *; refine lt_of_le_of_lt ?_ h; apply mul_le_mul_of_nonneg_left _ zero_le_two; gcongr; exact (S.S.a_pos _).le
lemma window_large {s:Side}{o:Site s}{r k:ℕ}(h:r≤k): window o r⊆window o k:=by rintro _ ⟨x,hx,rfl⟩; exact ⟨x, box_larger hx h,rfl⟩
def lifting [Fintype ι] (H: Schedule)(n:ℕ)(q:J≤m)(o:ι→ Site (H.side J n))(f:ι→ Config G (H.side m n)→ℂ) (U: Config G (H.side m n)): ℂ:= ∏ i,f i (translate (anchor H n q (o i)) U)
lemma aggregation [Fintype ι] (q:m≤N)(hk:J≤m)(r:ℕ) (o:ι→ Site (H.S.side J p))(ho:Injective o)(F:ι→ Config G (H.S.side m p)→ℂ)(h:∀ i,Interior (window 0 r) (F i))(hx:GridApprox.room H.levels J m r): backTo H N p q (lifting H.S p hk o F) = lifting H.S p (hk.trans q) o (fun i=> backTo H N p q (F i)):=by
   let f i:= F i ∘ translate (anchor H.S p hk (o i))
   let A (j: Site (H.S.side J p)) : Config G (H.S.side m p)→ℂ:= if h:∃ i,o i=j then f (Classical.choose h) else 0
   have hm(i): A (o i)= f i:=by unfold A; rw [dif_pos (show ∃ j,o j=o i from ⟨i,rfl⟩)]; exact congr_arg f (ho (Classical.choose_spec (show ∃ j,o j=o i from ⟨i,rfl⟩)))
   let L:= Finset.univ.image o; have he: lifting H.S p hk o F= fun U=> ∏ j∈L,A j U:=funext fun i=> by unfold L; rw [Finset.prod_image ho.injOn]; simp_rw [hm]; rfl
   have hF j (hh:j∈L) : Interior (window (anchor H.S p hk j) r) (A j):=by
       obtain ⟨i,hi,rfl⟩:= Finset.mem_image.mp hh; rw [hm]; have he:=translated_window (anchor H.S p hk (o i)) (h i); rw [zero_add] at he; exact he
   rw [he,backTo_cells H N p hk q L A r hF hx]; funext u; unfold L; rw [Finset.prod_image ho.injOn]; apply Finset.prod_congr rfl; intro i _; rw [hm]; exact congr_fun (backTo_t H q hk _ (cylinder_env (h i))) u
lemma lifts_env [Fintype ι](H:Schedule)(n:ℕ)(q:J≤m)(o:ι→ Site (H.side J n)) (F:ι→ Config G (H.side m n)→ℂ)(h:∀ i,Envelope (F i)): Envelope (lifting H n q o F):=Envelope.prodC _ _ fun i _=> (h i).comp_env (show Measurable _ from (law_translate 0 _).measurable)
end YM.UVExtension.Hearth
