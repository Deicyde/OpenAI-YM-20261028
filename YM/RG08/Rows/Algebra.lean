import YM.RG08.Packets.Pushed

/-!
# True translation operators in native cells

All arrays unwrapped. For different levels, can pack all quantities first in single (coarse)
cell units, paying residue counts. Reuse `Pert.Bulk` anchored absolute API, all type-independent
except the explicitly counted intermediate type sizes and polynomial demand. No seminorm on
physical densities.
-/
noncomputable section
namespace YM.RG08.Rows
open Filter Finset Pert.Bulk Lattice Laurent Bloch RG08.Packets Function Matrix
open scoped Topology ENNReal
set_option autoImplicit false
variable {α β γ : Type} {p q σ τ : ℝ}
    {K T U: Kernel α β} {D W : Kernel β γ}
    {n : Side}

structure Priced (σ p: ℝ) (K : Kernel α β) : Prop where
  pos : 0 ≤ p
  city : Packets.city 1 K
  row : RowCost σ 1 K p
  col : ColCost σ 1 K p

namespace Priced
lemma mono (h : Priced σ p K) (hs:τ≤σ)(hp:p≤q): Priced τ q K := ⟨h.pos.trans hp,h.city,fun x y=> ((h.row.mono hs) x y).trans (ENNReal.ofReal_le_ofReal hp),fun x y=> ((h.col.mono hs) x y).trans (ENNReal.ofReal_le_ofReal hp)⟩
lemma row_t (h : Priced σ p K) (_hs:0≤σ): RowCost σ 1 (Function.swap K) p := by
  intro x y; simpa only [swap,delta_one,sep_comm x.1] using h.col y x
lemma rear (h : Priced σ p K) (hs:0≤σ): Priced σ p (Function.swap K) := by
  refine ⟨h.pos,fun x y u=> ?_, row_t h hs,fun i x=> ?_⟩
  · have he:=h.city y x u
    dsimp only [swap]; simpa only [show (1:Side).val=1 from rfl,one_smul] using he
  simpa only [swap,delta_one,sep_comm x.1] using h.row x i
lemma add (h : Priced σ p K)(hk: Priced σ q T) : Priced σ (p+q) (K+T):= by
  have ht (x y : ℝ)(a : ℝ): bill (x+y) a≤bill x a+bill y a:= by simpa only [← stamp_real] using stamp_add x y a
  refine ⟨add_nonneg h.pos hk.pos,fun x y u=> ?_,fun x i=>?_,fun i x=>?_⟩
  · exact congr_arg₂ (·+·) (h.city x y u) (hk.city x y u)
  · rw [ENNReal.ofReal_add h.pos hk.pos]
    exact (ENNReal.tsum_le_tsum fun y=> ht (K x (y,i)) (T x (y,i)) (σ*delta 1 x.1 y)).trans (by rw [ENNReal.tsum_add]; exact add_le_add (h.row x i) (hk.row x i))
  rw [ENNReal.ofReal_add h.pos hk.pos]
  exact (ENNReal.tsum_le_tsum fun y=> ht (K (y,i) x) (T (y,i) x) (σ*delta 1 y x.1)).trans (by rw [ENNReal.tsum_add]; exact add_le_add (h.col i x) (hk.col i x))
lemma smul (h : Priced σ p K) (s : ℝ) : Priced σ (|s| *p) (s • K) := by
  have ht {x t} : bill (s*x) t= ENNReal.ofReal |s| * bill x t := by rw [bill_eq,bill_eq,abs_mul,ENNReal.ofReal_mul (abs_nonneg _),mul_assoc]
  refine ⟨mul_nonneg (abs_nonneg _) h.pos,fun x y u=> ?_,fun x i=> ?_,fun i x=> ?_⟩
  · exact congr_arg (s • ·) (h.city x y u)
  · simp_rw [Pi.smul_apply,smul_eq_mul, ht,ENNReal.ofReal_mul (abs_nonneg s),ENNReal.tsum_mul_left]; exact mul_le_mul_right (h.row x i) _
  simp_rw [Pi.smul_apply,smul_eq_mul, ht,ENNReal.ofReal_mul (abs_nonneg s),ENNReal.tsum_mul_left]; exact mul_le_mul_right (h.col i x) _
lemma neg (h: Priced σ p K): Priced σ p (-K):= by simpa using h.smul (-1)
lemma sub (h: Priced σ p K)(hk : Priced σ q T): Priced σ (p+q) (K-T):=by rw [sub_eq_add_neg]; exact h.add hk.neg
lemma zero (σ : ℝ) : Priced σ 0 (0: Kernel α β):= ⟨le_rfl,fun _ _ _=>rfl,fun _ _=>by simp [bill],fun _ _=>by simp [bill]⟩

lemma mul [Fintype β] (h : Priced σ p K)(ht : Priced σ q D)(hs:0≤σ): Priced σ (Fintype.card β*(p*q)) (Pert.Bulk.bind K D):= by
  have he (x y z : Cover) : σ*delta (1:Side) x z≤σ*delta 1 x y+σ*delta 1 y z:=by simp only [delta_one,← mul_add]; exact mul_le_mul_of_nonneg_left (sep_triangle ..) hs
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (mul_nonneg h.pos ht.pos), by simpa only [one_mul] using pass_bind h.city ht.city, row_block h.pos ht.pos h.row ht.row he, col_block h.pos ht.pos h.col ht.col he⟩
end Priced

/-- A kernel and its every-period finite presentation are tracked together. -/
structure Tagged (σ p:ℝ)(K:Kernel α β)(A:∀ n:Side, Matrix (Co n α) (Co n β) ℝ) : Prop extends Priced σ p K where
 seen (n:Side) : Matches K (A n)

variable {A B Z : ∀ n:Side, Matrix (Co n α) (Co n β) ℝ} {C : ∀ n : Side,Matrix (Co n β) (Co n γ) ℝ}
namespace Tagged
lemma rear (h : Tagged σ p K A)(hs:0≤σ): Tagged σ p (Function.swap K) (fun n=> (A n).transpose) := ⟨h.toPriced.rear hs,fun n=> matches_back (L:=1) (by simp) h.city (h.seen n)⟩
lemma mul [Fintype β] (h : Tagged σ p K A)(ht : Tagged σ q D C)(hs:0≤σ): Tagged σ (Fintype.card β*(p*q)) (Pert.Bulk.bind K D) (fun n=> A n * C n):= ⟨h.toPriced.mul ht.toPriced hs,fun n=> applies_bind h.row ht.row hs hs (h.seen n) (ht.seen n)⟩
lemma smul (h: Tagged σ p K A) (t : ℝ): Tagged σ (|t| *p) (t • K) (fun n=>t • A n):= by
  refine ⟨h.toPriced.smul _,fun n x y=>?_⟩
  rw [Matrix.smul_apply, ← h.seen n x y]
  unfold display
  rw [ smul_eq_mul, ← tsum_mul_left]
  apply tsum_congr
  intro z
  split <;> simp
lemma add [Fintype β] (h : Tagged σ p K A)(ht : Tagged σ q T B)(hs:0≤σ): Tagged σ (p+q) (K+T) (A+B):= by
  refine ⟨h.toPriced.add ht.toPriced,fun n x y=>?_⟩
  classical
  have he {K:Kernel α β}(p:ℝ)(h:Priced σ p K):Summable fun z=> if wrap n z=y.1 then K x (z,y.2) else 0 := by
    have H : Summable fun z:Cover=> K x (z,y.2) := summable_from_receipt (fun z=> mul_nonneg hs (delta_nonneg (1:Side) x.1 z)) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.row x y.2))
    exact (H.indicator {z | wrap n z = y.1}).congr fun v=>Set.indicator_apply ..
  change _ = A n _ y+B n _ y
  rw [← h.seen n x y, ← ht.seen n x y,display,display,display,← (he _ h.toPriced).tsum_add (he _ ht.toPriced)]
  apply tsum_congr; intro b; split <;> simp
lemma neg (h : Tagged σ p K A): Tagged σ p (-K) (-A):= by
  convert h.smul (-1:ℝ) using 1 <;> simp; rfl
lemma sub [Fintype β](h : Tagged σ p K A)(ht:Tagged σ q T B)(hs:0≤σ): Tagged σ (p+q) (K-T) (A-B):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.add ht.neg hs
lemma mono (h : Tagged σ p K A) (hs:τ≤σ)(hp:p≤q): Tagged τ q K A := ⟨h.toPriced.mono hs hp,h.seen⟩
lemma ticket [Fintype β] (H:Row α β)(h:H.strip σ p)(hp:0≤p): Tagged σ p (plain H) (fun n=> H.acts n):= ⟨⟨hp,pass_one _,(plain0 h le_rfl).1,(plain0 h le_rfl).2⟩,fun _=>matches_plain _⟩ -- matches_plain needs Fintype β
end Tagged
end YM.RG08.Rows
