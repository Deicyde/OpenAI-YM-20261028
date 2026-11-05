import YM.Push.CUTOFF_PROJECTORS.Signed

/-!
# Use with extraction on *the same* fitted equation coordinates

Not necessary to assume map convergence in order to apply this. Use
`include_projections` with our bounds (or `common` if supplied the
other finite estimates). Not claiming the finite projection results cost any particular *number*
of scales to converge. No rank conclusion about Maxwell *detectors*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors
open Filter Extraction Function Labels Next.Extract Dash
open scoped Topology BigOperators InnerProductSpace

variable {G : Gauge} {C : Family G} {d N p : ℕ} {F : Labels.Frame G d} {A : Campaign C} {f : Order}

abbrev lost (F : Labels.Frame G d) (L : F.Coeff →L[ℂ] F.Coeff) := LinearMap.ker L.toLinearMap

/-- Orthogonal in the chosen common metric, not assumed for all of
EXTRACTION's abstract presentations. -/
structure Shadow (F : Labels.Frame G d) (L : F.Coeff →L[ℂ] F.Coeff) : Prop where
  stays (x : F.Coeff) : L (L x) = L x
  hermitian (x y) : pair F (L x) y = pair F x (L y)

variable {P Q : F.Coeff →L[ℂ] F.Coeff}







variable {S T : Table C.book} {R : Bin S} {z : (d : ℕ) → ℕ → CoordMap C d}





/-! ## If dimension and orientation estimates come through

Act on the very same H subspaces of the very same coefficient labels.
A helpful way of passing the real and signed type along with rank:
project from a nearby member of equal type. No limit left-inverse for
possibly growing columns. Applies both at a single p and on period tails.
-/

structure Commuting (F : Labels.Frame G d) (L : F.Coeff →L[ℂ] F.Coeff) : Prop where
  signed (s : Signed) (x) : L (turn F s x) = turn F s (L x)
  real (x) : L (star x) = star (L x)

def Aligned (F : Labels.Frame G d) (K : Submodule ℂ F.Coeff) := ∃ e : equationSpace F ≃ₗ[ℂ] K,
    (∀ (s : Signed) (w : equationSpace F),
      (e ⟨turn F s w, equation_oriented F s w w.2⟩).val = turn F s (e w)) ∧
    ∀ w : equationSpace F,
      (e ⟨star w.val, equation_realForm F w w.2⟩).val = star (e w).val







/-- Move the null-coordinate type between nearby orthogonal projections. -/
def changeKer (P : F.Coeff →L[ℂ] F.Coeff) {Q : F.Coeff →L[ℂ] F.Coeff} (h : Shadow F Q) :
    lost F P →ₗ[ℂ] lost F Q :=
  let g := (LinearMap.id - Q.toLinearMap).comp (lost F P).subtype
  g.codRestrict _ fun x => by
    apply LinearMap.mem_ker.mpr
    change Q (x.val-Q x.val) = 0
    rw [map_sub, h.stays, sub_self]

theorem changeKer_injective (h : Shadow F Q) (he : ‖P-Q‖ < 1) : Injective (changeKer P h) := by
  have ht (v : lost F P) (hx : changeKer P h v = 0) : v = 0 := by
    have hm : v.val - Q v.val = 0 := congr_arg Subtype.val hx
    have hv : P v.val = 0 := LinearMap.mem_ker.mp v.property
    apply Subtype.ext
    change v.val = 0
    by_contra hw
    have hq := (P-Q).le_opNorm v.val
    change ‖P v.val - Q v.val‖ ≤ _ at hq
    rw [hv,← sub_eq_zero.mp hm,zero_sub,norm_neg] at hq
    have hb := mul_lt_mul_of_pos_right he (norm_pos_iff.mpr hw)
    linarith
  intro x y hz
  exact sub_eq_zero.mp (ht (x-y) (by simp only [map_sub,hz,sub_self]))

theorem Aligned.near (ht : Shadow F P) (hw : Shadow F Q) (h : Aligned F (lost F P))
    (hs : Commuting F Q) (he : ‖P-Q‖ < 1) : Aligned F (lost F Q) := by
  let c := changeKer P hw
  have h1 : Injective c := changeKer_injective hw he
  have h2 := changeKer_injective ht (show ‖Q-P‖ < 1 by rwa [norm_sub_rev])
  have hk := le_antisymm (LinearMap.finrank_le_finrank_of_injective h1) (LinearMap.finrank_le_finrank_of_injective h2)
  let b := LinearEquiv.ofBijective c ⟨h1,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hk).mp h1⟩
  obtain ⟨L,hL,hp⟩ := h
  have hc (v : equationSpace F) : ((L.trans b) v).val = (L v).val - Q (L v).val := rfl
  refine ⟨L.trans b,fun s w => ?_,fun w => ?_⟩
  · rw [hc,hc,hL,hs.signed,map_sub]
  rw [hc,hc,hp,hs.real,star_sub]












end YM.Push.CutoffProjectors
