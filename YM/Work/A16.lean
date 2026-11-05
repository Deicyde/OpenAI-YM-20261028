import YM.Bid.Angular

/-!
# Proper orthochronous Lorentz group via the future unit time direction

The stabilizer of the time basis vector consists of spatial turns. Successive
coordinate boosts suffice to put a future unit timelike vector at rest (so no
limiting products/topological closure are needed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A16
open Set Mink Real
open scoped InnerProductSpace

/-- An element fixing the future unit time basis vector preserves also the
Euclidean norm, hence is one of the spatial turns, with determinant unchanged. -/
theorem exists_room_of_fix (g : Lorentz) (hg : g.act (basis timeAxis) = basis timeAxis) :
    ∃ (K : Ortho) (h : Lorentz.spatialTurn K), Lorentz.room K h = g := by
  have hr : General.walk Lorentz.reverseL (basis timeAxis) = basis timeAxis := by
    simp only [Lorentz.reversing, roll_space, neg_zero]
    rw [← roll_space, position_eta]
  have hd : g.dual.act (basis timeAxis) = basis timeAxis := by
    change General.walk (Lorentz.reverseL * g.val * Lorentz.reverseL) _ = _
    rw [General.walk_mul, General.walk_mul, hr, hg, hr]
  have ht (v : E4) : time (g.act v) = time v := by
    have hp := g.dual_sent (basis timeAxis) v
    rw [hd, real_inner_comm (basis timeAxis), basis_inner, real_inner_comm _ v, basis_inner] at hp
    exact hp
  have hn (v : E4) : ‖g.act v‖ = ‖v‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), squares, squares, ht]
    have hp := g.keeps v
    simp only [m, ht] at hp
    linarith
  let C : E4 ≃ₗᵢ[ℝ] E4 := { g.sends.toLinearEquiv with norm_map' := hn }
  obtain ⟨K,hK⟩ := OS.Ground.columns C
  have hmap : K.motion.toLinearEquiv.toLinearMap = g.act.toLinearMap := LinearMap.ext hK
  have h : Lorentz.spatialTurn K := ⟨by rw [Lorentz.properTurn,hmap,g.det],by
    intro x; rw [hK x]; exact ht x⟩
  exact ⟨K,h,Lorentz.ext _ _ hK⟩

/-- A coordinate boost killing one spatial component on the strict future cone. -/
theorem exists_boost_zero (i : SpaceAxis) (x : E4) (hx : x ∈ inside) :
    ∃ t : ℝ, spatial ((Ray.fromAxis i).shift t x) i = 0 := by
  let e := Ray.fromAxis i
  have hT := ((strict_self x).1 hx).1
  let y := e.along x
  have hy := abs_lt.mp (show |y| < time x from lt_of_le_of_lt (e.along_le x) hx)
  have hyt : y / time x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ hT).mpr (by linarith), (div_lt_iff₀ hT).mpr (by linarith)⟩
  let r := artanh (y / time x)
  have hr : sinh r / cosh r = y / time x := by
    rw [← tanh_eq_sinh_div_cosh]; exact tanh_artanh hyt
  have hr' := (div_eq_div_iff (cosh_pos _).ne' hT.ne').mp hr
  refine ⟨-r, ?_⟩
  change ((e.shift (-r) x) i.castSucc) = 0
  rw [← Ray.onAxis, Ray.newProjection, sinh_neg, cosh_neg]
  change -sinh r * time x + cosh r * y = 0
  linarith

lemma boost_keeps_other (i j : SpaceAxis) (hj : j ≠ i) (t : ℝ) (x : E4) :
    spatial ((Ray.fromAxis i).shift t x) j = spatial x j := by
  rw [Ray.newSpace]
  simp [Ray.fromAxis, Ne.symm hj]

lemma exists_rest_finset (x : E4) (hx : x ∈ inside) (s : Finset SpaceAxis) :
    ∃ k ∈ Bid.beamGens, ∀ i ∈ s, spatial (Lorentz.act k x) i = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, Bid.beamGens.one_mem, by simp⟩
  | insert i s _ ih =>
    obtain ⟨k,hk,h⟩ := ih
    obtain ⟨t,ht⟩ := exists_boost_zero i _ ((k.stays x).mpr hx)
    have hb : (Ray.fromAxis i).boost t ∈ Bid.beamGens :=
      Subgroup.subset_closure (Or.inr ⟨i,t,rfl⟩)
    refine ⟨(Ray.fromAxis i).boost t * k, Bid.beamGens.mul_mem hb hk,fun j hj => ?_⟩
    rw [Lorentz.act_mul, Ray.boost_at]
    by_cases hij : j=i
    · subst j; exact ht
    rw [boost_keeps_other _ _ hij]; exact h j ((Finset.mem_insert.mp hj).resolve_left hij)

/-- Transitivity up to the rest vector on the future unit hyperboloid. -/
theorem exists_rest (x : E4) (hx : x ∈ inside) (hm : m x = 1) :
    ∃ k ∈ Bid.beamGens, Lorentz.act k x = basis timeAxis := by
  obtain ⟨k,hk,h⟩ := exists_rest_finset x hx Finset.univ
  have hs : spatial (k.act x) = 0 := PiLp.ext (fun i => h i (Finset.mem_univ _))
  have hm' : m (k.act x) = 1 := (k.keeps x).trans hm
  simp only [m, hs, norm_zero] at hm'
  have hT := ((strict_self _).1 ((k.stays x).mpr hx)).1
  exact ⟨k,hk, ext_by (by rw [hs, roll_space]) (by rw [roll_clock]; nlinarith)⟩

theorem answer : YM.Bid.A16 := by
  apply Bid.beamGens.eq_top_iff'.2
  intro g
  have hx : basis timeAxis ∈ inside := by
    change ‖spatial (basis timeAxis)‖ < time (basis timeAxis)
    simp
  have hm : m (basis timeAxis) = 1 := by simp [m]
  obtain ⟨k,hk,h⟩ := exists_rest _ ((g.stays _).mpr hx) ((g.keeps _).trans hm)
  obtain ⟨K,hK,he⟩ := exists_room_of_fix (k*g) h
  have hb : k * g ∈ Bid.beamGens := Subgroup.subset_closure (Or.inl ⟨K,hK,he⟩)
  simpa using Bid.beamGens.mul_mem (Bid.beamGens.inv_mem hk) hb

end YM.Work.A16
