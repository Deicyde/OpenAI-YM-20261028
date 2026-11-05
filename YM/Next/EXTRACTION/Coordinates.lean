import YM.Next.EXTRACTION.Relay

/-!
# Coordinates at the common normalized base

Some exact consequences useful when the projection data were extracted. Give that passage even for the `Added` receipt of D04 on the
**same** extraction. No assumptions about already having bounded coefficient
rows; this gives convergence of the *projected parts*, along `f.fuse`. One
must still check each-period estimates to pick two-stage limits when needed;
fused-filter convergence alone does not license that. Also give the 
kernel dimension persistence for `Projected`, for both stages as stated
there (no assertion of the proposed value of that dimension).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Extract
open Filter Set MeasureTheory Extraction Dash Function
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Order} {d : ℕ} {R : Bin S}





private lemma near_null {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (p q : V →L[ℂ] V) (hq : ∀ v, q (q v) = q v) (H : ‖p - q‖ < 1) :
    Module.finrank ℂ (LinearMap.ker p.toLinearMap) ≤ Module.finrank ℂ (LinearMap.ker q.toLinearMap) := by
  let s := LinearMap.ker p.toLinearMap
  let t := LinearMap.ker q.toLinearMap
  let W : s →ₗ[ℂ] V := (LinearMap.id-q.toLinearMap).comp s.subtype
  let B : s →ₗ[ℂ] t := W.codRestrict _ fun v => by
    apply LinearMap.mem_ker.mpr
    change q ((v:V)-q v)=0
    rw [map_sub,hq,sub_self]
  have ht v : B v = 0 → v = 0 := fun h => by
    have hp : (v:V)-q v=0 := congr_arg Subtype.val h
    apply Subtype.ext
    change (v:V)=0
    by_contra hc
    have hh : p v = 0 := LinearMap.mem_ker.mp v.property
    have hw := (p-q).le_opNorm (v:V)
    rw [sub_apply,hh,← sub_eq_zero.mp hp,zero_sub,norm_neg] at hw
    have hl := mul_lt_mul_of_pos_right H (norm_pos_iff.mpr hc)
    rw [one_mul] at hl
    exact hl.not_ge hw
  apply LinearMap.finrank_le_finrank_of_injective (f := B)
  intro x y hxy
  exact sub_eq_zero.mp (ht (x-y) (by rw [map_sub,hxy,sub_self]))

/-- Ranks of kernels persist in the *two* separate limits, including at
arbitrary fixed periods. -/
lemma Projected.ranks {b : Presentation C} {z} (h : Projected b f R z) (d : ℕ) :
    let k := fun u : CoordMap C d => Module.finrank ℂ (LinearMap.ker u.toLinearMap)
    (∀ p : ℕ, ∀ᶠ j : ℕ in atTop, k (b.step d (f.mesh j,p)) = k (z d p)) ∧
    ∀ᶠ i : ℕ in atTop, k (z d (f.per i)) = k (R d).trueP := by
  dsimp only
  have ht (p : ℕ → CoordMap C d) (q : CoordMap C d) (hp : ∀ i v, p i (p i v) = p i v)
      (hq : ∀ v, q (q v) = q v) (he : Tendsto p atTop (𝓝 q)) :
      ∀ᶠ j : ℕ in atTop, Module.finrank ℂ (LinearMap.ker (p j).toLinearMap) = Module.finrank ℂ (LinearMap.ker q.toLinearMap) := by
    filter_upwards [Metric.tendsto_nhds.mp he 1 one_pos] with i hi
    rw [dist_eq_norm] at hi
    exact le_antisymm (near_null _ _ hq hi) (near_null _ _ (hp i) (by rwa [norm_sub_rev]))
  exact ⟨fun p => ht (fun j => b.step d (f.mesh j,p)) (z d p) (fun j => b.projected d _) (h.inner_projection d p)
      (h.keeps.rows d p trivial),
    ht (fun i => z d (f.per i)) (R d).trueP (fun i => h.inner_projection d _) (R d).final (h.keeps.outer d)⟩
end YM.Next.Extract
