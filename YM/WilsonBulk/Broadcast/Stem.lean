import YM.WilsonBulk.Broadcast.Pins
import YM.WilsonBulk.Series.Picture

/-!
# Read planted finite period onto formal tape. Handles reindexing around finite
physical step. No addressing outside cover; caller supplies correct manifold tape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators ContDiff
open Function Filter Equiv Finset Lattice Laurent Bloch Pert.Bulk
open MvPolynomial (X C)
variable {α β γ : Type} {n : ℕ} {Λ : Side} {p σ : ℝ}
lemma curls_fin (u : Legs (Co Λ α) n) (r) (v : Legs (Co Λ α) n) (i : Fin n) : curlies u r v= ∑ x:Site Λ,if v=rolls x α ∘ u then r else 0:= by
  let x := (v i).1-(u i).1; rw [sum_eq_single x,curls_pinned u r v i]
  · intro y _ hy; split
    next h=>
      exfalso; apply hy; unfold x; rw [h]; simp only [Function.comp_apply,rolls_apply,add_sub_cancel_left]
    exact rfl
  exact fun h=> False.elim (h (mem_univ _))
variable (T : β→Market α)
abbrev ladder (z : Site Λ) : β → Co Λ α := (rolls z α) ∘ (small Λ α ∘ T)
variable [Fintype α]
lemma curls_script (u : Legs (Co Λ α) n) (r) (hn : n≠0) : script (curlies u r)=∑ x : Site Λ,C r*field (rolls x α ∘ u) := by
  simp only [script,curls_fin u r _ (⟨0,by omega⟩ : Fin n),map_sum, sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro i _; simp [apply_ite,ite_mul] -- Mv powers
variable [Fintype β]
lemma stalk_script (U : Page β n) (c : Side) (hn : n≠0) : script (stalk (Λ:=c) T U) = ∑ x : Site c, MvPolynomial.rename (ladder T x) (script U) := by
  rw [stalk,script_polish,script_sum]; simp only [curls_script _ _ hn]; rw [sum_comm]; apply sum_congr rfl; intro i _; simp only [script,map_mul,map_sum,field,map_prod,MvPolynomial.rename_X,MvPolynomial.rename_C]; rfl

omit [Fintype α] [Fintype β] in
lemma submit_name (u : α→β) (p : Tape α) : submit (named ∘ u) p = parallel (MvPolynomial.rename u).toLinearMap p := by
  rw [show (named ∘ u)=(fun i=> PowerSeries.C ((MvPolynomial.rename u) (X (R:=ℝ) i))) by simp; rfl]; exact submit_by .. -- maybe typeclasses

def socket (u : α→β) : Tabletop β →L[ℝ]Tabletop α := ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:β=>ℝ) (u i))
omit [Fintype α] [Fintype β] in
lemma socket_apply (u : α→β) (x : Tabletop β) : socket u x=x∘u:= rfl
omit [Fintype α] in
lemma expose_socket (u : α→β) : exposure (socket u)=named ∘ u := funext (fun i=> flash_named (u i))
lemma ink_rename (u : α→β) (f : Tabletop α→ℝ) (h : ContDiffAt ℝ ω f 0) : ink (f ∘ socket u) = submit (named ∘ u) (ink f) := by rw [ink_comp h (socket u).contDiff.contDiffAt (map_zero _),expose_socket]
-- for path sectors, repeated FIELD terms at power m all prior in τ costs local
variable (f : Tabletop β→ℝ) (h : ContDiffAt ℝ ω f 0)
def plantSector (Λ : Side) : Tabletop (Co Λ α) → ℝ := ∑ z : Site Λ,f ∘ socket (ladder T z)
include h
lemma plant_stalk (c : Side) (n : ℕ) : PowerSeries.coeff (n+1) (ink (plantSector T f c)) = script (print c (stem T (photo f (n+1)))) := by
    have hn:=Nat.succ_ne_zero n; rw [(reads (stem_style T _)).uniq (stem_due T c _) (small_onto _ _) hn,stalk_script T _ c hn,plantSector,ink_sum] -- order
    · simp_rw [ink_rename _ _ h, submit_name, map_sum, coeff_parallel]; simp [ink_power]
    intro i _; exact (show ContDiffAt ℝ ω f (socket (ladder T i) 0) by rw [map_zero]; exact h).comp 0 (socket (ladder T i)).contDiff.contDiffAt
end YM.WilsonBulk.Sheet
