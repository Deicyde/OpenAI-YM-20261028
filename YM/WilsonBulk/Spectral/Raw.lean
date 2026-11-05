import YM.WilsonBulk.Spectral.Joint
import YM.Next.STATIONARY.Films.Contact

/-! Post-L expense converting slab-relative weights to actual row strip norms.
Use finite type compact bounds keeping the declared width, NEVER call a pre-length
quantity with these costs. Uniform in finer cutoff & period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Work.F08 Precision Exterior Stationary Audience Matrix Set
open scoped Topology BigOperators ContDiff

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {σ η V : ℝ} {L : Side}

open scoped Matrix.Norms.L2Operator in
lemma level_cont (F : Momentum→CompM α α) (h : Continuous F) : Continuous (fun i=>vflux (F i)) := by
  unfold vflux; exact h.norm

lemma continuous_slug {k : Type} [Fintype k] : Continuous (slug (α:=k)) := by
  unfold slug; fun_prop
lemma continuous_shade : Continuous shadeK := by
  exact continuous_slug.comp (show Continuous (fun x : Momentum => Exterior.q (ground x)) from by unfold Exterior.q ground axes; fun_prop)
omit [Fintype α] [DecidableEq α] in
lemma continuous_spice (i : Co L α) : Continuous (fun x=> spice L α x i) := by
  unfold spice; apply Continuous.inv₀
  · have ht := continuous_shade
    unfold hill pebWeight aliasAt; fun_prop
  exact fun x=> Complex.ofReal_ne_zero.mpr (hill_pos _ _).ne'
lemma continuous_plankTile : Continuous (plankTile L α) := by
  apply continuous_matrix fun i j=> ?_
  rw [continuous_iff_continuousAt]; intro p; exact (tile_lit p i j).continuousAt
lemma continuous_altar : Continuous (altarTile L α).tile := by
  unfold altarTile contour; dsimp only [id_eq]
  have hg : Continuous (fun x : Momentum=>Matrix.diagonal (spice L α x)) := by
    apply continuous_matrix; intro i j; unfold Matrix.diagonal; simp only [Matrix.of_apply]; split <;> first | exact continuous_spice _ | exact continuous_const
  exact (continuous_plankTile.mul hg).mul continuous_const
lemma continuous_spade {X : Slab α} {Y : Slab β} (h : Continuous X.tile) (g : Continuous Y.tile) :
    Continuous (X.spade Y).tile := by
  apply continuous_matrix; intro i j; cases i <;> cases j <;> first | exact h.matrix_elem _ _ | exact g.matrix_elem _ _ | exact continuous_const
lemma continuous_slabW (G : Gauge) (L : Side) : Continuous (slabW G L).tile :=
  continuous_spade continuous_altar continuous_const
lemma continuous_retreat {X : Slab α} (h : Continuous X.tile) : Continuous (fun x => (X.tile x)⁻¹) := by
  apply continuous_iff_continuousAt.mpr; intro p
  apply (continuousAt_matrix_inv _ ?_).comp h.continuousAt
  rw [show Ring.inverse= (Inv.inv : ℂ → ℂ) from funext Ring.inverse_eq_inv]; exact continuousAt_inv₀ (X.whole p).ne_zero
lemma continuous_dual {X : Slab α} (h : Continuous X.tile) : Continuous X.dual.tile := by
  have he := (continuous_retreat h).matrix_transpose.comp continuous_neg
  convert he using 1
  ext x i j; rw [Slab.dual]; dsimp only [Function.comp_apply]; rw [transpose_nonsing_inv]

variable {X : Slab α}
lemma tile_max {F : Momentum→ CompM α α} (h : Continuous F) (σ : ℝ) :
    ∃ M : ℝ, 0≤ M ∧ ∀ p ∈ strip σ, Nave p → vflux (F p) ≤ M := by
  obtain ⟨M,hm⟩:= ((isCompact_closedBall (0:Momentum) (Real.pi+|σ|)).image (level_cont F h)).bddAbove
  refine ⟨max M 0,le_max_right .., fun p hp hN=> le_max_of_le_left ?_⟩
  refine hm ⟨p, Metric.mem_closedBall.mpr ?_,rfl⟩
  rw [dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
  exact fun i=> (Complex.norm_le_abs_re_add_abs_im _).trans
    (add_le_add (hN i) (((hp i).le).trans (le_abs_self _)))

lemma postCost (σ : ℝ) (X : Slab α) (hX : Continuous X.tile) :
    ∃ W, 0 ≤ W ∧ ∀ M : Momentum → CompM α α,
      ∀ A, Poster σ M → Freezer X.dual X M σ A →
        ∀ p∈ strip σ, vflux (M p)⁻¹ ≤ A * W := by
  obtain ⟨U,hU,u⟩:= tile_max hX σ; obtain ⟨W,hW,w⟩:= tile_max (continuous_retreat (continuous_dual hX)) σ
  refine ⟨U*W,mul_nonneg hU hW, fun M A hp h p hP=>?_⟩
  obtain ⟨q,hq,hQ⟩ := Nave.roll p
  have hv := skyPeriod hP hQ.symm
  rw [← hp.shifts hQ hv]
  let Y := (M q)⁻¹; let Z:=carryM X X.dual q q Y
  have hz : vflux Z≤ A := h.price q hv
  have ha := (flux_nonneg Z).trans hz
  have hx : Y=X.tile q*Z*(X.dual.tile q)⁻¹ := by
    unfold Z carryM; rw [← mul_assoc (X.tile q),← mul_assoc (X.tile q),
      mul_nonsing_inv _ (X.whole q), Matrix.one_mul, mul_assoc,mul_nonsing_inv _ (X.dual.whole q),Matrix.mul_one]
  change vflux Y≤_; rw [hx]
  calc _ ≤ _ := (flux_power ..).trans
            (mul_le_mul ((flux_power ..).trans (mul_le_mul (u q hv hq) hz (flux_nonneg _) hU))
              (w q hv hq) (flux_nonneg _) (mul_nonneg hU ha))
       _ = _ := by ring

end YM.WilsonBulk
