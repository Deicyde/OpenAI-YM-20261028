import YM.RG08.Isles.Cask

noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter Bloch
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I:Type}{n:ℕ}{P:Side}{F:Flake n (Market I)} {σ C:ℝ}

lemma plaza (x:Tape n (Market I)): (shore P I).radius (port P ∘ x)≤(carpet I).radius x:= (shore P I).radius_le _ (Ground.radius_nn ..) fun i j=> (walk_wrap ..).trans ((carpet I).le_radius x i j)
lemma cell_sum (h:Held (carpet I) σ C F)(he:0≤σ)(i:Fin n)(z:Market I): Summable fun w:Tape n (Market I)=> if w i=z then |F w| else 0:=by
 refine (Ticket.unweighted h (fun _ x=>mul_nonneg he ((carpet I).radius_nn x)) (i,z)).congr ?_;intro x; unfold hung;split_ifs <;> simp
lemma pour_view (h:Held (carpet I) σ C F)(he:0≤σ)(i:Fin n)(x:Tape n (Market I)):
  Tendsto (fun k=> pour F i (port (chain k) ∘ x)) atTop (𝓝 (F x)) :=by
 let U(w:Tape n (Market I)):= if w=x then F w else 0
 have ht(w):Tendsto (fun k=> (lantern i (port (chain k) ∘ x)).indicator F w) atTop (𝓝 (U w)):=by
    apply Filter.EventuallyEq.tendsto
    filter_upwards [(carpetRoad I).cards n|>.growing w,(carpetRoad I).cards n|>.growing x] with k hw hx
    change reach ∘ port (chain k) ∘ w=w at hw
    change reach ∘ port (chain k) ∘ x=x at hx
    have hf:w∈lantern i (port (chain k) ∘ x) ↔ w=x:=by
      constructor
      · intro H;exact hw ▸ hx ▸ congr_arg (fun v=> reach (I:=I) (P:=chain k) ∘ v) ((Set.mem_setOf.mp H).2)
      rintro rfl; exact ⟨(congrFun hx i).symm,rfl⟩
    rw [Set.indicator_apply];dsimp only [U];simp_rw [hf]
 let B (w:Tape n (Market I)):= if w i=x i then |F w| else 0
 have hh :∀ᶠ k:ℕ in atTop, ∀ w, ‖(lantern i (port (chain k) ∘ x)).indicator F w‖ ≤ B w:=by
    filter_upwards [contacts (x i)] with k hk
    intro w
    by_cases hy:w i=x i
    · dsimp only [B];rw [if_pos hy]; unfold Set.indicator;split_ifs<;>simp
    · have he:w∉lantern i (port (chain k) ∘ x):=fun hz=>hy (((Set.mem_setOf.mp hz).1).trans hk)
      dsimp only [B];rw [Set.indicator_of_notMem he,if_neg hy,norm_zero]
 have hu:=tendsto_tsum_of_dominated_convergence (cell_sum h he i (x i)) ht hh
 simpa only [pour,U,tsum_ite_eq] using hu -- tuple orientation

lemma pour_hold (hc:Cohort F)(h:Held (carpet I) σ C F)(he:0≤σ)(i:Fin n):Held (shore P I) σ C (pour F i):=by
 rw [ensign]
 intro a z
 unfold Forms.row mark
 simp_rw [congrFun (funext (common (P:=P) hc i a))]
 calc
  _ ≤ ∑' w:Tape n (Cove P I),∑' x:Tape n (Market I), if w=port P ∘ x then Forms.row (mark (carpet I) σ F) a (reach z) x else 0:= ENNReal.tsum_le_tsum fun w=> ?_
  _ ≤ _:=by rw [ENNReal.tsum_comm];simpa only [tsum_ite_eq] using (ensign.mp h) a (reach z) -- ?
 unfold Forms.row
 by_cases hf:w a=z
 · rw [if_pos hf];apply (bill_tsum (fun x=>(lantern a w).indicator F x) _).trans
   apply ENNReal.tsum_le_tsum;intro x
   by_cases hp:x∈lantern a w
   · obtain ⟨hr,rfl⟩:=Set.mem_setOf.mp hp
     rw [if_pos rfl,if_pos (hr.trans (congr_arg reach hf)),Set.indicator_of_mem hp]
     exact bill_mono le_rfl (mul_le_mul_of_nonneg_left (plaza ..) he)
   rw [Set.indicator_of_notMem hp];simp [bill]
 simp [hf]

lemma bureau (hc:Cohort F)(h:Held (carpet I) σ C F)(he:0<σ)(hC:0≤C)(i:Fin n):Study σ C (I:=I) (fun j=>pour (P:=chain j) F i) F:=⟨he,hC,h,fun _=>pour_hold hc h he.le i,fun _=>pour_view h he.le i⟩

end YM.RG08.Isles
