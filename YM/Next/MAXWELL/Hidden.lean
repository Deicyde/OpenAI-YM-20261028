import YM.Next.MAXWELL.Batch
import YM.Next.MAXWELL.Born
import YM.Next.MAXWELL.Rumbles



/-!
# Hidden colors at a cluster

Mixed-leg replacement operators with unrestricted highest direction.
The low jet values need only *generically* separate colors -- prove this
over the polynomial domain using det.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder Matrix
variable {G : Gauge} {j k l n r d : ℕ}

lemma probe_radius_span (G : Gauge) (j k : ℕ) : Submodule.span ℝ
    {p : Module.Dual ℝ (Probe G j)| ∃ (x:E4) (h:x∈away) (c:G.ColorIndex) (q:Flavor k),p=pairing h (flavor k c q)} = ⊤ := by
  classical
  let W := Submodule.span ℝ {p : Module.Dual ℝ (Probe G j)|∃ (x:E4) (h:x∈away) (c:G.ColorIndex) (q:Flavor k), p=pairing h (flavor k c q)}
  change W=⊤
  have hp : W.dualCoannihilator=⊥ := by
    apply le_antisymm _ bot_le; intro i hi
    have ht : i=∑ c, flavor j c (flavor_pick i c) := by
      ext u; rw [LinearMap.sum_apply]; conv_lhs => rw [← half_sum u, map_sum]
      rfl
    have hm (c) : flavor_pick i c=0 := by
      apply ranging c _ k; intro z hz q
      have H (z) (h : z∈away) : pairing (l:=j) h (flavor k c q) i=0 :=
        (Submodule.mem_dualCoannihilator _).mp hi _ (show _∈ W from Submodule.subset_span ⟨z,h,c,q,rfl⟩)
      have he : K i (flavor k c q) z 0=0 := (K_symmetric _ _ hz).trans (H _ (sub_ne_zero.mpr hz.symm))
      rw [ht,K_pairing _ _ hz,map_sum,LinearMap.sum_apply,Finset.sum_eq_single_of_mem c (Finset.mem_univ _)] at he
      · change fare c (flavor_pick i c) q (z-0)=_ at he
        rwa [sub_zero] at he
      intro a _ ha; change legKernel _ _ _=_
      rw [any_ink c (flavor_pick i a) q a c (sub_ne_zero.mpr hz),if_neg ha,zero_mul]
    simp_rw [hm,map_zero, Finset.sum_const_zero] at ht
    rw [ht]; exact Submodule.zero_mem _
  apply Submodule.eq_top_of_finrank_eq
  have he := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hp,finrank_bot,add_zero] at he
  rw [he]; exact (Subspace.dual_finrank_eq ..).symm

lemma group_meal {p : WickPol G} (h : ∀ (x:E4), x∈away → ∀ (q : Flavor k) (c : G.ColorIndex), singleBite j (flavor k c q) x p=0)
    (i : Fin (legDim G j)) : MvPolynomial.pderiv (keyAt j i) p=0 := by
  let f (a : Fin (legDim G j)) := coordinateLeg (keyAt j a)
  let P (a : Fin (legDim G j)) := MvPolynomial.pderiv (keyAt j a) p
  let Q : Module.Dual ℝ (Probe G j) →ₗ[ℝ] WickPol G :=
    { toFun x := ∑ i, x (f i) • P i
      map_add' x y := by simp only [LinearMap.add_apply,add_smul, Finset.sum_add_distrib]
      map_smul' t x := by simp [Finset.smul_sum,smul_smul] }
  have hh : Q=0 := by
    apply LinearMap.ext_on (probe_radius_span G j k); rintro w ⟨x,hx,c,q,rfl⟩
    have he := h x hx q c
    rw [bite_eval] at he; simp_rw [volumes] at he; exact he
  have ht := LinearMap.congr_fun hh ((Module.Dual.eval ℝ (Shell G j)) (frame G j i))
  change ∑ a : Fin (legDim G j), (f a (frame G j i)) • P a=0 at ht
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)] at ht
  · rw [show f i _=1 from (Module.Basis.repr_self_apply (frame G j) i i).trans (if_pos rfl),one_smul] at ht; exact ht
  intro a _ ha; rw [show f a _=0 from (Module.Basis.repr_self_apply (frame G j) i a).trans (if_neg ha.symm),zero_smul]

lemma matrix_meal (h : G.Simple) : ∃ q : (c : G.ColorIndex) → Flavor c.val, (Matrix.of (fun (c i : G.ColorIndex) => bit (q c) i)).det≠0 := by
  classical
  have he (c : G.ColorIndex) : ∃ (q : Flavor c.val) (v : Sheet c.val), q v = 1 := by
    let B := Module.finBasis ℝ (Sheet c.val)
    letI := has_sheet h c.val
    let i := (⟨0,Module.finrank_pos⟩ : Fin (Module.finrank ℝ (Sheet c.val)))
    exact ⟨B.coord i, B i, (Module.Basis.repr_self_apply B i i).trans (if_pos rfl)⟩
  choose q w hw using he
  let A := Matrix.of fun c i : G.ColorIndex => bit (q c) i
  refine ⟨q,fun H => ?_⟩
  let y : TaylorTower G := fun j => if h:j<G.lieDim then fill j (unitColor G ⟨j,h⟩) (w ⟨j,h⟩) else 0
  let P := probe y
  have hh : A.map P=1 := by
    ext a b; change probe y (bit (q a) b)=_; rw [bit,symbol_test]
    rw [show y a.val=fill _ (unitColor G a) (w a) from dif_pos a.isLt, Matrix.one_apply]
    by_cases h:a=b
    · subst b; rw [tasted,hw,if_pos rfl]; rfl
    rw [if_neg h];
    change (↑(q a (faceMap _ _ (fill _ _ _))):ℂ)= _
    rw [which,unitPaint a b,if_neg (Ne.symm h),zero_smul,map_zero]; rfl
  have hk : P A.det=1 := by rw [AlgHom.map_det,show P.mapMatrix A=1 from hh, Matrix.det_one]
  rw [H,map_zero] at hk; exact zero_ne_one hk

lemma reduces_top (A : WickPol G) (h : G.Simple) (hp : A ∈ shelf G (j+1)) 
    (H : ∀ (l : ℕ), l < G.lieDim → ∀ (p : Flavor k) (q : Flavor l) x,x≠0 → circulate (j+1) p q x A=0) : A∈ shelf G j := by
  classical
  obtain ⟨q,hq⟩ := matrix_meal h
  have he (p : Flavor k) (i : G.ColorIndex) {x : E4} (hx : x∈away) : singleBite (j+1) (flavor k i p) x A=0 := by
    let M := Matrix.of fun i b : G.ColorIndex => bit (q i) b
    let D i := singleBite (j+1) (flavor k (G:=G) i p) x A
    have hi : M *ᵥ D=0 := funext fun i => (circulate_eval (j+1) p (q i) x A).symm.trans (H _ i.isLt p (q i) x hx)
    have hv : M.det * D i=0 := congr_fun (show M.det • D=0 by rw [← Matrix.one_mulVec D, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, hi]; simp) i
    exact (mul_eq_zero.mp hv).resolve_left hq
  apply MvPolynomial.mem_supported.mpr; intro i hi
  have hb : i.1 ≤ j+1 := MvPolynomial.mem_supported.mp (show A∈Rack G _ from hp) hi
  rcases i with ⟨i,z⟩; change i ≤ j+1 at hb; change i ≤ j
  by_contra! ha
  obtain rfl : i=j+1 := by omega
  exact erase_var _ A (group_meal (k:=k) (fun _ hx p c => he p c hx) z) hi
end YM.Maxwell.Free

namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped Topology BigOperators
variable {G : Gauge}

/-- One fixed exterior weight bound (all arities allowed) detects all caps. -/
theorem exposed (h : G.Simple) : ∃ d,∀ w,∀ p∈shellSector G w,p∈ghost G d → p=0 := by
  let j := G.lieDim
  let L := j+1
  obtain ⟨r,hr⟩ := hosting G j
  let d := max r (4+j+L)
  refine ⟨d,fun w => ?_⟩
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro p hp H
    cases w with
    | zero => exact ghosts_out (chain (Nat.zero_le _) hp) H
    | succ w =>
      have hx (i : ℕ) (hK : p∈shelf G (j+i)) : p∈shelf G j := by
        induction i with
        | zero => exact hK
        | succ m he =>
          rw [← Nat.add_assoc] at hK
          apply he (reduces_top p h hK (k:=L) ?_)
          intro l hl q t x hu
          have hh : l < j := hl
          have hw : L+l+4 ≤ d := le_trans (by omega : L+l+4 ≤ 4+j+L) (le_max_right ..)
          apply ih w (by omega) _ (circulates_lower (j+m+1) q t hu (by omega) _ hp) (cluster_clear hK H q t (by unfold L; omega) hw hu)
      have he : p∈shelf G j := hx (w+1) ((MvPolynomial.supported_mono
        (show {k : Slot G| k.1 ≤ w + 1} ⊆ {k : Slot G| k.1 ≤ j+(w+1)} from fun _ hv => le_trans hv (Nat.le_add_left ..))) (cap_shelf p (sector.mp hp).1))
      exact hosted_out p (ghost_le (le_max_left ..) H) (fun i {_} => hr i _) he hp
end YM.Maxwell.Free
