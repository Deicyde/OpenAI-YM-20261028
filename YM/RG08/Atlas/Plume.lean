import YM.RG08.Isles.Fruit
import YM.RG08.Atlas.Church

/-! # Truncation and transposing to cofinal piston period (chain n). !-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Mount
open Lattice Stationary Exterior Pert.Bulk Laurent RG Forms Camera Room Glyph Steam Isles Filter Function Finset Topology
open scoped Classical Topology PowerSeries BigOperators
variable {I J G M:Type}{e n:ℕ}{σ p:ℝ}

def hedge (n:ℕ)(A:Grain I):Grain I:= fun i=>if i ≤ n then A i else 0
lemma hedge_hit (A:Grain I) (e i:ℕ)(he:i ≤ e):hedge e A i=A i:=if_pos he

variable (g: Forms.Line I) {A:Grain I}
lemma spark_hedge (l:ℕ)(i:ℕ) : ∀ k ≤ e,burn g (hedge e A) l k i=burn g A l k i:=by
 induction l using Nat.strong_induction_on generalizing i with
 | h l ih=>cases l with
   | zero=>simp [spark,hedge]; grind
   | succ l=>intro k hk;simp_rw [blaze,wheels,unilateral];rw [ih l (by omega) _ _ hk];congr 2; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b hb;apply sum_congr rfl; intro c hc;rw [ih b ?_ _ c ?_,ih (l-b) ?_ _ (k-c) ?_]<;> simp [mem_range] at * <;> omega
lemma all_hedge (m:I→J→ℝ)(l:ℕ)(k:ℕ)(hk:k ≤ e):allG g (hedge e A) m k l=allG g A m k l:=by
 unfold allG Steam.strict Steam.cinder;rw [hedge_hit _ _ _ hk];congr 2;apply sum_congr rfl;intro i _;rw [spark_hedge g (i+1) l k hk]
lemma hedge_unveil (c:Side)(H:Grain (Market I))(e): hedge e (unveil H c)=unveil (hedge e H) c:=by
 ext n m z;unfold unveil hedge;split <;> rename_i hn
 · rfl
 split; next h=> change (0:ℝ)=pour (P:=c) (0:Flake m (Market I)) _ z;rw [blank _ _ rfl];rfl
 rfl

private lemma Study.monoS {F:ViewDeck n I}{G}(h:Study σ p F G){z q}(hz:0<z)(hZ:z ≤ σ)(hq:p ≤ q):Study z q F G:= ⟨hz,h.cost.trans hq,h.palm.mono hZ hq (fun _=>le_rfl),fun i=> (h.calm i).mono hZ hq (fun _=>le_rfl),h.light⟩

lemma hedgeline (T:Grain (Market I))(e:ℕ)(ht:Steam.Eligible T)(hh:legal T)(hs:∀ i,slaw T i): ∃ θ:ℝ,0 < θ∧Isles.seats θ (fun j=> unveil (hedge e T) (chain j)) (hedge e T):=by
 choose a b ha hb h using fun x:ℕ×ℕ=>hs x.1 x.2
 let W:Finset (ℕ×ℕ):= range (e+1) ×ˢ range (e+3)
 obtain ⟨c,B,hc,hB,H⟩:= docket W a b (fun x _=>ha x) (fun x _=> hb x)
 refine ⟨c,hc,fun i n=>?_⟩
 by_cases hz:0<n
 · let z:Fin n:=⟨0,hz⟩
   by_cases he: i ≤ e ∧ n ≤ i+2
   · refine ⟨B,?_⟩
     obtain ⟨hx,hy⟩:=H (i,n) (show _ from Finset.mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩)
     have hU:Held (carpet _) c B (T i n):=(h (i,n)).mono hx hy (fun _=>le_rfl)
     simp only [hedge,unveil,he.1,dif_pos hz,if_pos];exact Isles.bureau (hh i n).1 hU hc hB z -- hh .. invalid
   · have hV:hedge e T i n=0:=by
       unfold hedge;split
       next hp=> exact Classical.byContradiction fun hg=> he ⟨hp,ht.head _ _ hg⟩
       rfl
     simp only [unveil,hV,dif_pos hz,blank _ _ rfl]; exact ⟨0,show _ from Isles.Study.zero (I:=I) n hc le_rfl⟩
 rcases n with _|n
 · obtain ⟨t,u,hT,hU,hp⟩:=hs i 0
   refine ⟨0,?_⟩ 
   refine ⟨hc,le_rfl,Forms.ensign.mpr fun j=>Fin.elim0 j,fun i=>Forms.ensign.mpr fun j=>Fin.elim0 j, fun h=>False.elim (Nat.lt_irrefl _ h)⟩
 exact False.elim (hz (Nat.succ_pos n))
end YM.RG08.Mount
