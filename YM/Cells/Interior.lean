import YM.Cells.Cut

/-!
# Copying does not lose locality/invariance/boundedness/integrability
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} {F P : Config G n → ℂ}

namespace Interior
variable {K M : Set (Site n)}

lemma integrable (h : Interior K F) (β : ℝ) : Integrable F (law G n β) := by
  obtain ⟨c,hc⟩ := h.cost
  exact bounded_integrable _ h.borel hc

lemma constant (K : Set (Site n)) (z : ℂ) : Interior (G := G) K fun _ => z :=
  ⟨fun _ _ => rfl, measurable_const, fun _ _ _ => rfl, _, fun _ => le_refl ‖z‖⟩

lemma real (h : Interior K F) : Interior K fun x => star (F x) := by
  refine ⟨fun t U => ?_,?_,fun s r H => ?_,?_⟩
  · rw [h.gauge t U]
  · exact (continuous_star (R := ℂ)).measurable.comp h.borel
  · rw [h.localSites s r H]
  obtain ⟨c,hc⟩ := h.cost; exact ⟨c,fun U => by rw [norm_star]; exact hc _⟩

lemma times (h : Interior K F) (e : Interior K P) : Interior K (fun x => F x * P x) := by
  obtain ⟨c,hc⟩ := h.cost; obtain ⟨d,hd⟩ := e.cost
  exact ⟨fun t U => congr_arg₂ _ (h.gauge ..) (e.gauge ..), h.borel.mul e.borel, fun u v H =>
    congr_arg₂ _ (h.localSites u v H) (e.localSites u v H), c*d,fun U => (norm_mul_le ..).trans
    (mul_le_mul (hc _) (hd _) (norm_nonneg _) ((norm_nonneg _).trans (hc U)))⟩

lemma scale (c : ℂ) (h : Interior K F) : Interior K (fun x => c * F x) := (constant K c).times h

lemma plus (h : Interior K F) (hp : Interior K P) : Interior K (fun x => F x + P x) := by
  obtain ⟨c,hc⟩ := h.cost; obtain ⟨d,hd⟩ := hp.cost
  exact ⟨fun t U => congr_arg₂ _ (h.gauge ..) (hp.gauge ..), h.borel.add hp.borel, fun u v H =>
    congr_arg₂ _ (h.localSites u v H) (hp.localSites u v H), c+d,fun U => (norm_add_le ..).trans
    (add_le_add (hc _) (hd _))⟩

lemma enlarges (h : Interior K F) (hm : K ⊆ M) : Interior M F :=
  ⟨h.gauge,h.borel,fun u v H => h.localSites u v (agrees_mono H hm), h.cost⟩

lemma unchanged (h : Interior K F) (s : Signed) (b : Site n) (hs : MapsTo (affine s b) K M) :
    Interior M (F ∘ pull s b) := by
  refine ⟨fun t U => ?_,h.borel.comp (continuous_pull s b).measurable, fun u v H => ?_,?_⟩
  · change F (pull s b (Lattice.gauge t U))= _
    rw [show pull s b (Lattice.gauge t U) = Lattice.gauge (t ∘ affine s b) (pull s b U) by
      funext e
      unfold pull Lattice.gauge
      have he (x i) : affine s b (x+step i) = affine s b x + ((posDir i).rotate s).vec := by
        rw [Step.vec_rotate]; simp [affine]; abel
      simp only [Function.comp_apply,he]
      exact Step.gauge_read ((posDir e.2).rotate s) t U (affine s b e.1)]
    exact h.gauge ..
  · apply h.localSites
    intro p hz hz'
    let d := (posDir p.2).rotate s
    let x := affine s b p.1
    change d.read u x = d.read v x
    have hh := hs hz
    have hw : x + d.vec ∈ M := by
      simp only [x,d, Step.vec_rotate, Step.vec_pos]; rw [show _ + s.act (step p.2) = affine s b (p.1 + step p.2) by
        rw [affine, affine,Signed.act_add]; abel]; exact hs hz'
    generalize d = D at *
    rcases D with ⟨i,t|t⟩
    · exact H (x,i) hh hw
    change (u (x-step i,i))⁻¹ = (v (x-step i,i))⁻¹
    rw [H]; exacts [by simpa [Step.vec,sub_eq_add_neg] using hw,by simpa [x] using hh]
  obtain ⟨c,hc⟩ := h.cost; exact ⟨c,fun _ => hc _⟩

lemma combines {ι : Type*} (F : ι → Config G n → ℂ) (s : Finset ι) (hs : ∀ i ∈ s, Interior K (F i)) :
    Interior K (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact constant _ _
  | @insert i s h ih =>
    simp_rw [Finset.prod_insert h]
    exact (hs i (Finset.mem_insert_self ..)).times <| ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
end Interior
end YM.Cells
