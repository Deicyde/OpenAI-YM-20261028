import YM.Next.UV_STRESS.Invert
import YM.Next.UV_STRESS.Tensor
import YM.UVNext.FREE_STRESS_CERTIFICATE.Couplings
import YM.UVNext.FREE_STRESS_CERTIFICATE.DoubleWick



/-!
# Degree four classes in `Bel` on separated positions

Explicit samples with the same Green and Wilson-family color normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Labels Tensor Maxwell Wick Climb Function Filter Set Table Work.A01 Next.UVStress
variable {G : Gauge} (F : Frames G) {j l n d : ℕ}

def embed (d : ℕ) : Label G d →ₗ[ℂ] (freeTable F).Field d :=
  ((freeTable F).project d).comp ((F.level d).coords.toLinearMap)

theorem covers : Surjective (embed F d) := ((freeTable F).onto d).comp (F.level d).coords.surjective

@[simp] theorem pin_unit (d : ℕ) : embed F d (Labels.unit G d) = (freeTable F).unit d := by
  change (freeTable F).project d _ = (freeTable F).project d _
  congr 1
  change (F.level d).coords _ = _
  rw [show _ = (F.level d).e0 from (F.level d).coords_unit]
  simp [Register.scalar, Register.coord, standard]; exact (one_smul ℂ _).symm

def token (d : ℕ) (p : Label G d) : (standard F).Token := ⟨d,(F.level d).coords p⟩
def tag (d : ℕ) (p : Label G d) : (freeTable F).Tag := ⟨d,embed F d p⟩

@[simp] theorem tag_decode (d : ℕ) (p : Label G d) : (freeTable F).classTokens (token F d p) = tag F d p := rfl

-- Transfer of label-level maps. These are the actual conj & mirror, not imposed
-- on an auxiliary symmetric tensor space. And the inclusion is also forced.
@[simp] theorem conjugate_embed (H : (freeTable F).RealSpin) (p : Label G d) :
    (freeTable F).conj H d (embed F d p) = embed F d (realBar p) := by
  change (freeTable F).conj H _ ((freeTable F).project d _) = (freeTable F).project _ _
  rw [Table.conj_project]; congr 1
  apply (F.level d).coords.symm.injective
  change (F.level d).coords.symm (star ((F.level d).coords p)) = (F.level d).coords.symm ((F.level d).coords (realBar p))
  rw [LinearEquiv.symm_apply_apply]
  exact ((standard F).geom_conj d _).symm.trans (congr_arg realBar ((F.level d).coords.symm_apply_apply p))

@[simp] theorem mirror_embed (H : (freeTable F).RealSpin) (s : Signed) (p : Label G d) :
    (freeTable F).mirror H d s (embed F d p) = embed F d (Labels.tensor s.ortho p) := by
  change (freeTable F).mirror H _ _ ((freeTable F).project d _) = (freeTable F).project _ _
  rw [Table.mirror_project]; congr 1
  exact (F.level d).act_coords ..

theorem first_label (p : Label G d) (w : Fin n → (standard F).Token) (x : Points (n+1)) :
    (freeTable F).read x (Fin.cons (token F d p) w) =
    moment G x (Fin.cons (observable G d p) (fun i => observable G _ ((F.level _).coords.symm (w i).2))) := by
  rw [decodes]
  congr 1; funext i; refine Fin.cases ?_ (fun j => ?_) i
  · change observable G d ((F.level d).coords.symm ((F.level d).coords p)) = observable G d p
    rw [(F.level d).coords.symm_apply_apply]
  · rfl

theorem rise_embed (W : DiffPlan (freeTable F)) (hW : W.Inclusions (freeTable F)) {e} (h : d ≤ e)
    (p : Label G d) : W.rise h (embed F d p) = embed F e (raiseLabel G h p) := by
  apply (freeTable F).faithfully; rw [W.through_limit (table_sym F) hW]
  funext x
  change (freeTable F).read x.point (Fin.cons (token F d p) x.letter) =
      (freeTable F).read x.point (Fin.cons (token F e _) x.letter)
  rw [first_label, first_label]; rfl

theorem mean_bond (p q : Place 0) : expectation (freeTable F) 4 (embed F 4 (bond p q le_rfl)) = 0 := by
  rw [expectation,front_eval]
  let B : Fin 0 → (standard F).Token := Fin.elim0
  change (freeTable F).useAt _ _ (Fin.cons (tag F 4 _) _) = _
  rw [show (Fin.cons (α:=fun _ : Fin (0+1) => (freeTable F).Tag) (tag F 4 (bond p q le_rfl)) (blank (freeTable F))) =
      (freeTable F).classTokens ∘ Fin.cons (α:=fun _ => (standard F).Token) (token F 4 (bond p q le_rfl)) B from
      funext fun i => by rw [@Subsingleton.elim (Fin 1) _ i 0]; rfl,
    (freeTable F).at_project (freeTable F) (table_sym F) (fun _ => le_rfl) conf1,first_label, shell_bond]
  -- linearity
  let M := moment G (0:Points 1)
  let w := fun i : Fin 0 => observable G (B i).1 ((F.level (B i).1).coords.symm (B i).2)
  change M.curryLeft (∑ c, _) w = _
  rw [map_sum,sum_apply]
  exact Finset.sum_eq_zero fun c _ => (show M (Fin.cons _ w) = _ from by
    rw [show Fin.cons (symbol _ (curlProbe p c) * symbol _ (curlProbe q c)) w =
        (fun _ => symbol _ (curlProbe p c) * symbol _ (curlProbe q c)) from
      funext fun i => by rw [@Subsingleton.elim (Fin 1) _ i 0]; rfl, mean_symbol])

def negs (F : Frames G) (c e f m : Axis) : Fin 1 → (freeTable F).Tag := fun _ => tag F 4 (ff G 4 le_rfl c e f m)

def hearing (x : Points 2) (c e f m : Axis) (d : ℕ) : (freeTable F).Field d →ₗ[ℂ] ℂ :=
  frontRead (negs F c e f m) x d

theorem listens (x : Points 2) (c e f m) (g : (freeTable F).Field d) :
    hearing F x c e f m d g = (freeTable F).useAt (freeTable F) x (Fin.cons ⟨d,g⟩ (negs F c e f m)) :=
  front_eval ..

set_option maxHeartbeats 50000 in
theorem samples {x : Points 2} (hx : x∈conf 2) (P : Label G d) (c e f m) :
    hearing F x c e f m d (embed F d P) =
      wickTwo G x (observable G d P) (observable G 4 (ff G 4 le_rfl c e f m)) := by
  let Q : Label G 4 := ff G 4 le_rfl c e f m
  let w : Fin 1 → (standard F).Token := fun _ => token F 4 Q
  rw [listens, show Fin.cons (α:=fun _ : Fin (1+1) => (freeTable F).Tag) ⟨d,embed F d P⟩ (negs F c e f m) =
      (freeTable F).classTokens ∘ Fin.cons (α:=fun _ => (standard F).Token) (token F d P) w from by
    funext i; refine Fin.cases ?_ (fun _ => ?_) i <;> rfl, (freeTable F).at_project (freeTable F) (table_sym F) (fun _ => le_rfl) hx,first_label]
  refine congr_arg (fun u : Fin 1 → WickPol G => moment G x (Fin.cons (observable G d P) u))
    (show (fun i : Fin 1 => observable G (w i).1 ((F.level _).coords.symm (w i).2)) =
      (fun _ => observable G 4 Q) from ?_)
  funext i
  change observable G 4 ((F.level 4).coords.symm ((F.level 4).coords Q)) = observable G 4 Q
  rw [(F.level 4).coords.symm_apply_apply]

theorem shellLink {x y : E4} (h : x ≠ y) (a b c d : Axis) (i k : G.ColorIndex) :
    actualEntry h (curlProbe (initialPlace a b) i) (curlProbe (initialPlace c d) k) =
    if i=k then (bareCurl a b c d (x-y) : ℂ) else 0 := by
  unfold actualEntry curlProbe
  rw [Maxwell.raw_mixed _ _ a b c d i k]
  · simp [Tensor.coeff_apply_zero]; split <;> simp_all
  exact sub_ne_zero.mpr h

def flash (a b i k c e f m : Axis) (z : E4) :=
    bareCurl a b c e z * bareCurl i k f m z + bareCurl a b f m z * bareCurl i k c e z

theorem hears {x : Points 2} (hx : x∈conf 2) (a b i k c e f m) :
    hearing F x c e f m 4 (embed F 4 (ff G 4 le_rfl a b i k)) =
    ((G.lieDim:ℂ) * (flash a b i k c e f m (x 0-x 1) : ℂ)) := by
  classical
  have h : x 0 ≠ x 1 := (show Injective x.ofLp from hx).ne (by decide)
  rw [samples F hx]; simp only [ff,shell_bond, map_sum, LinearMap.sum_apply,double_symbol x h 0 0 0 0]
  simp_rw [shellLink h]
  push_cast [flash]
  simp [ite_mul,mul_ite,Finset.sum_add_distrib,mul_add]

end YM.UVNext.FreeStress
