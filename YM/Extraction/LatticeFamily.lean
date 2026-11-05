import YM.Source.Construction
import YM.Euclid.Table

/-!
# Adapter from Wilson Family to finite moments

Multilinearity, reality, orientation use *only* this cylinder calibration.
No limit used. Literal cutoff coordinates, origin and cover.
-/

set_option autoImplicit false
noncomputable section
namespace YM
open Lattice Wilson Function Set MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius

namespace Family
variable {G : Gauge} (C : Family G)

abbrev book : Register G := ⟨C.labels, fun d => C.S.a (C.ref d),fun d => C.S.a_pos (C.ref d)⟩

@[simp] theorem unit_ref (d : ℕ) : C.book.scalar d = C.refUnit d := rfl

variable {N p n : ℕ}

def seen (t : C.book.Token) (y : Site (C.side N p)) := C.O N p (d := t.1) t.2 y

theorem integrableR {n : ℕ} (v : Fin n → C.book.Token) (r : Fin n → Site (C.side N p)) :
    Integrable (fun U => ∏ i, C.seen (v i) (r i) U) (law G _ (C.beta N p)) :=
  continuous_integrable (C.beta N p) (continuous_finsetProd _ fun i _ => C.continuousO N p (v i).1 (v i).2 (r i))

def ensemble (d : Caps n) (x : Fin n → Site (C.side N p)) : Moment C.book n d where
  toFun v := C.omega N p fun U => ∏ i, C.O N p (d := d i) (v i) (x i) U
  map_update_add' v i u w := by
    let f (a : C.book.Vector d) (U : Config G (C.side N p)) : ℂ := ∏ i, C.O N p (d := d i) (a i) (x i) U
    have He (a : C.book.Ref (d i)) (U) : f (update v i a) U = C.O N p (d := d i) a (x i) U *
        ∏ j ∈ Finset.univ.erase i, C.O N p (d := d j) (v j) (x j) U := by
      dsimp only [f]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => congr_arg
        (fun y : C.book.Ref _ => C.O N p (d := d j) y (x j) U)
        (Function.update_of_ne (Finset.mem_erase.mp hj).1 ..)
    change (∫ U, f _ U ∂_) = _
    have H (a) : Integrable (f a) (law G (C.side N p) (C.beta N p)) :=
      C.integrableR (fun j => ⟨d j,a j⟩) x
    change (∫ U, f (update v i (u+w)) U ∂_) = (∫ U, f (update v i u) U ∂_)+(∫ U, f (update v i w) U ∂_)
    rw [← integral_add (H _) (H _)]
    apply integral_congr_ae; refine Filter.Eventually.of_forall fun U => ?_
    dsimp only
    rw [He,He,He, ← add_mul]
    exact congr_arg (fun y : ℂ => y * _) (congr_fun ((C.linearO N p (d i) (x i)).map_add u w) U)
  map_update_smul' v i c u := by
    let f (a : C.book.Vector d) (U : Config G (C.side N p)) : ℂ := ∏ j, C.O N p (d := d j) (a j) (x j) U
    have He (a : C.book.Ref (d i)) (U) : f (update v i a) U = C.O N p (d := d i) a (x i) U *
        ∏ j ∈ Finset.univ.erase i, C.O N p (d := d j) (v j) (x j) U := by
      dsimp only [f]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => congr_arg
        (fun y : C.book.Ref _ => C.O N p (d := d j) y (x j) U)
        (Function.update_of_ne (Finset.mem_erase.mp hj).1 ..)
    change (∫ U, f (update v i (c • u)) U ∂_) = c * ∫ U, f (update v i u) U ∂_
    rw [← integral_const_mul]; apply integral_congr_ae
    refine Filter.Eventually.of_forall fun U => ?_; dsimp only; rw [He,He, ← mul_assoc]
    exact congr_arg (fun y : ℂ => y * _) (congr_fun ((C.linearO _ _ _ _).map_smul c u) U)

def numeric (N p : ℕ) (v : Fin n → C.book.Token) (r : Fin n → Site (C.side N p)) : ℂ :=
  C.ensemble (fun i => (v i).1) r fun i => (v i).2

theorem num (v : Fin n → C.book.Token) (r : Fin n → Site (C.side N p)) :
    C.numeric N p v r = ∫ U, (∏ i, C.seen (v i) (r i) U) ∂law G _ (C.beta N p) := rfl

theorem oriented (H : C.Makes) (v : Fin n → C.book.Token) (H' : ∀ i, C.ref (v i).1 ≤ N)
    (s : Signed) (t : Site (C.side N p)) (x : Fin n → Site (C.side N p)) :
    C.numeric N p (C.book.move s ∘ v) (affine s t ∘ x) = C.numeric N p v x := by
  let F := fun U : Config G _ => ∏ i, C.seen (C.book.move s (v i)) (affine s t (x i)) U
  -- F equals original product on pulled links
  rw [num,num]
  have he : F = (fun U => ∏ i, C.seen (v i) (x i) U) ∘ pull s t := funext fun U =>
    Finset.prod_congr rfl fun i _ => C.rotated H (H' i) (v i).2 s (x i) t U
  change moment (C.beta N p) F = _; rw [he]
  exact moment_pull _ _ _ _ (C.integrableR v x)

abbrev sufficient (N) (v : Fin n → C.book.Token) := ∀ i, C.ref (v i).1 ≤ N

theorem anchored (H : C.Makes) (v : Fin n → C.book.Token) (H' : C.sufficient N v) (t : Site (C.side N p)) (x) :
    C.numeric N p v (fun i => x i + t) = C.numeric N p v x := by
  have he1 : C.book.move 1 ∘ v = v := funext fun i => by unfold Function.comp Register.move; simp
  have he2 : affine 1 t ∘ x = fun i => x i + t := funext fun i => by simp [affine,add_comm]
  simpa only [he1,he2] using C.oriented H v H' 1 t x

theorem real_eval (H : C.Makes) (v : Fin n → C.book.Token) (H' : C.sufficient N v)
    (x : Fin n → Site (C.side N p)) :
    C.numeric N p (C.book.conjugate ∘ v) x = star (C.numeric N p v x) := by
  rw [num,num,Complex.star_def,← integral_conj]
  apply integral_congr_ae; refine Filter.Eventually.of_forall fun U => ?_
  simp only [map_prod]
  exact Finset.prod_congr rfl fun i _ => C.reality H (H' i) (v i).2 _ _
end Family
end YM
