import YM.Push.LOOP_COEFFICIENT.LoopSymbol

/-!
# Alias jets modulo longitudinal transfers

Avoid charging hypothetical valuations to the longitudinal piece of an
arbitrary stationary RBC lift. Need a regular section only up to first order
at the origin and only for the independent fine Ward-invariant terms in the
coarse projection, not a column acting on-shell away from the origin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Lattice Laurent Bloch Exterior Matrix Complex RG
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {L : Side} {V : Profiles L (Axes G) (Axes G)} {U : Momentum → Matrix (Axes G) (Axes G) ℂ}

structure GaugeAlias (V : Profiles L (Axes G) (Axes G)) : Prop where
  lift : ∃ W : Profiles L (Axes G) (Axes G), AliasJet W ∧ (∀ k : Site L, ContDiffAt ℂ ω (fun p => W p k) 0) ∧
    ∀ p, star p=p → ∀ k : Site L, ∃ M, V p k = W p k + longitudinal G (aliasAt p k) * M

lemma q_period (p : Momentum) (z : Cover) (i : Axis) : q (p+reciprocal z) i = q p i := by rw [q, ← factor,mode_phase,mode_periodic,mul_one,factor,q]
lemma long_period (p : Momentum) (z : Cover) : longitudinal G (p+reciprocal z) = longitudinal G p := by simp only [longitudinal,q_period]

def TwoWard (U : Momentum → Matrix (Axes G) (Axes G) ℂ) := ∀ p, star p=p → U p * longitudinal G p = 0 ∧ (longitudinal G (-p)).transpose * U p = 0
lemma Signature.twoWard {b} (h : Signature G b U) : TwoWard U := fun p hp => ⟨h.ward p hp,by
  rw [show U p = (U (-p)).transpose by rw [← h.symmetric p hp,transpose_transpose],← Matrix.transpose_mul,h.ward (-p) (by rw [star_neg,hp]), transpose_zero]⟩

lemma GaugeAlias.probe (a : G.ColorIndex) (h : GaugeAlias V) (hv : ∀ k : Site L,ContDiffAt ℂ ω (fun p => V p k) 0) (hu : ∀ k : Site L, ContDiffAt ℂ ω U (aliasAt 0 k))
    (he : TwoWard U) (hU : Signature.Short U 2) : probe₂ (collectPair V U) a = probe₂ U a := by
  obtain ⟨W,h,hW,hQ⟩ := h.lift
  have hh {V : Profiles L (Axes G) (Axes G)} (hv : ∀ k : Site L, ContDiffAt ℂ ω (fun p => V p k) 0) : ContDiffAt ℂ ω (collectPair V U) 0 := collect_analytic hu (fun k => ⟨(show ContDiffAt ℂ ω (fun p => V p k) (-0) by simpa using hv k).comp (f:=(-·)) 0 (by fun_prop),hv k⟩)
  have hz : collectPair V U =ᶠ[𝓝 0] collectPair W U := germ_real (hh hv).analyticAt (hh hW).analyticAt (Eventually.of_forall fun p hp => by
    unfold collectPair; congr 1; refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨M,hM⟩ := hQ p hp k; obtain ⟨L,hL⟩ := hQ _ (show star (-p)=-p by rw [star_neg,hp]) (-k)
    have hw := he _ (show star (aliasAt p k) = aliasAt p k by rw [← alias_conj,hp])
    obtain ⟨z,hz⟩ := alias_opposite k p
    rw [Matrix.mul_assoc,hM,Matrix.mul_add,← Matrix.mul_assoc _ _ M,hw.1,Matrix.zero_mul,add_zero,hL, hz,long_period,Matrix.transpose_add,Matrix.transpose_mul,Matrix.add_mul, Matrix.mul_assoc (Matrix.transpose L), ← Matrix.mul_assoc (longitudinal _ _).transpose,hw.2,Matrix.zero_mul,Matrix.mul_zero, add_zero,Matrix.mul_assoc]
  )
  rw [probe₂,mark,of_apply,line_congr (hz.mono (fun p h => congr_fun (congr_fun h (1,a)) (1,a)))]
  exact congr_arg (·/2) (congr_fun (congr_fun (collect_mark hW hu h hU (unitAxis 0)) (1,a)) (1,a))

lemma orbit_long (p : Momentum) (s : Signed) : orbitSymbol G s p * longitudinal G p = longitudinal G (s⁻¹.act p) := by
  ext ⟨i,a⟩ b; simp only [Matrix.mul_apply,Fintype.sum_prod_type,orbitSymbol,Matrix.of_apply,Prod.mk.injEq,ite_and,ite_mul,zero_mul,
    longitudinal,mul_ite,mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,Finset.mem_univ,if_true]; split; swap
  · simp_all
  simp only [corner, Signed.act, Signed.inv_perm, Signed.inv_flip,Equiv.symm_symm,Equiv.symm_apply_apply,q]; split <;> simp [*, mul_neg, exp_neg, Complex.exp_ne_zero,mul_sub]; ring
lemma long_curl (p : Momentum) : curlSymbol G p * longitudinal G p = 0 := by
  ext i j; rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp [curlSymbol,longitudinal,mul_ite,ite_mul]; intro h
  have he := congr_fun (congr_fun (d_d 0 (q p)) (plaquette i.1)) vac
  rw [Matrix.mul_apply, ← Equiv.sum_comp axisEquiv] at he
  have hz (i : Axis) : wedge 0 (q p) (coord i) vac = q p i := by
    unfold wedge; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]; rw [Fintype.sum_eq_single i]
    · rw [left,of_apply,dif_pos (show i∈(coord i).val by simp [coord]),if_pos (vac_only _)]; simp [coord,parity,pre,Finset.filter_singleton]
    intro j hj; simp [coord,left,hj]
  simpa only [symbol,coord_map,hz,Matrix.zero_apply, Nat.zero_add] using he
lemma loop_twoWard (W : PathData G) : TwoWard (loopSymbol W) := by
  have he (p : Momentum) (s : Signed) : orient G (rawSymbol G (loopRow W)) s p * longitudinal G p = 0 := by
    simp only [orient,rawSymbol,Matrix.mul_assoc,orbit_long,long_curl,Matrix.mul_zero]
  intro p hp; constructor
  · simp only [loopSymbol,Matrix.smul_mul,Matrix.sum_mul,he,Finset.sum_const_zero, smul_zero]
  have hh : (loopSymbol W (-p)).transpose = loopSymbol W p := by
    simp only [loopSymbol,orient,transpose_sum, rawSymbol,Signed.act_neg, Matrix.transpose_smul, Matrix.transpose_add,transpose_mul,transpose_transpose, neg_neg, Matrix.mul_assoc]
    refine congr_arg (((Fintype.card Signed : ℂ)⁻¹) • ·) ?_; apply Finset.sum_congr rfl; intro i _; rw [add_comm]
  rw [← hh,← Matrix.transpose_mul]; simp only [loopSymbol,Matrix.smul_mul,Matrix.sum_mul,he,Finset.sum_const_zero,smul_zero, transpose_zero]
end YM.Push.Loops
