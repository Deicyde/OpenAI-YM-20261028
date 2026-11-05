import YM.Lattice.Route
import YM.Branch.Synchronize
import YM.RG.Patch

/-!
# Tube cutoffs in Wilson kernel
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG

open Branch Lattice Wilson
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable (G : Gauge)

theorem frame_unique : ∃ δ : ℝ, 0 < δ ∧ ∀ C : KernelChoices, C.frame_cut ≤ δ → ∀ P : Patch,
    ∀ U : CoverConfig G, P.usesMin C U → ∃! h, P.minimizing U h := by
  obtain ⟨d,hd,H⟩ := align G
  refine ⟨d/G.colorScale, div_pos hd G.colorScale_pos, fun C hc P U ht => ?_⟩
  let a := P.axial U (P.center,1)
  let A : Pairs P.Points Lattice.Order G :=
    { W := P.via a U
      mirror := backOrder
      same := fun i k => by simp [Patch.via,travel]
      reflect := fun i j k => by
        unfold Patch.via; rw [back_route]
        have h : travel U j.val (reverse (route i.val j.val k)) = (travel U i.val (route i.val j.val k))⁻¹ := by
          convert (travel_reverse (route i.val j.val k) U i.val) using 1
          simp only [route_end]
        rw [h]; group }
  have hw (x y k) : ‖G.mat (A.W x y k) - 1‖ ≤ d := by
    have hh : G.chord (A.W x y k) ≤ d/G.colorScale := le_trans (ht 1 k x y).le hc
    exact (div_le_div_iff_of_pos_right G.colorScale_pos).mp hh
  let toA (b : P.Frame G) : P.Frame G := fun x => b x*(a x)⁻¹
  have he (b) : P.score U b = A.cost (toA b) := by
    have hh (i j k) : A.term (toA b) i j k = G.price (P.via b U i j k) := by
      unfold Pairs.term toA
      simp only [A,Patch.via]; congr 1; group
    unfold Pairs.cost; simp_rw [hh]
    rfl
  have hs (b : P.Frame G) (h : P.minimizing U b) : A.Solves (toA b) := by
    intro f
    let p : P.Frame G := fun i => f i*a i
    let q : P.Frame G := fun i => (p P.center)⁻¹*p i
    have hx := h.2 q (by simp [q]); rw [he,he] at hx
    rw [show toA q = (fun i => (p P.center)⁻¹ * f i) by ext i; simp only [p,q,toA, mul_assoc, mul_inv_cancel,mul_one],A.moves] at hx
    exact hx
  obtain ⟨b,hb⟩ := P.min_exists U
  refine ⟨b,hb,fun f hf => ?_⟩
  obtain ⟨c,hc'⟩ := H _ _ A hw (toA b) (toA f) (hs _ hb) (hs _ hf)
  have hx := hc' P.center
  simp only [toA,hb.1,hf.1, one_mul,mul_eq_right] at hx
  funext i
  exact mul_right_cancel (by simpa only [hx,toA,one_mul] using (hc' i).symm)

theorem predictor_unique : ∃ δ : ℝ, 0 < δ ∧ ∀ C : KernelChoices, C.predictor_cut ≤ δ → ∀ P : Patch,
    ∀ Y : P.Connector G, P.usesBest C Y → ∃! u, ∀ v, P.bondCost Y u ≤ P.bondCost Y v := by
  obtain ⟨δ,hn,H⟩ := weighted_unique G
  refine ⟨δ,hn,fun C hc P Y h => ?_⟩
  obtain ⟨u,hu,hy⟩ := H P.Points P.weight P.weight_nonneg P.weight_sum Y ⟨P.best Y, lt_of_lt_of_le h hc⟩
  exact ⟨u, (min_iff P.weight P.weight_sum Y u).1 hu, fun j hj => hy j ((min_iff _ P.weight_sum Y _).2 (show ∀ _, _ from hj))⟩
end YM.RG
