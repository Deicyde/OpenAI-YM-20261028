import YM.Push.LOOP_COEFFICIENT.Divide

/-! # Order control in divisions and analytic cancellation -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Filter Function Set Lattice Laurent Bloch Exterior Complex Metric
open scoped Topology ContDiff BigOperators
variable {f g : Momentum → ℂ} {p : Momentum} {i : Axis} {n m : ℕ}

private lemma ray_smooth {F : Momentum × ℂ → ℂ} {p : Momentum × ℂ} (hf : ContDiffAt ℂ ω F p) (n : ℕ) :
    ContDiffAt ℂ ω (fun z : Momentum × ℂ => iteratedDeriv n (fun t => F (z.1,t)) z.2) p := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    let A (z : Momentum × ℂ) (t : ℂ) := iteratedDeriv n (fun t => F (z.1,t)) t
    have he : ContDiffAt ℂ ω (fun z : Momentum × ℂ => fderiv ℂ (A z) z.2) p := ContDiffAt.fderiv (n:=ω) (f:=A) (g:=Prod.snd) (ih.comp (f:=fun z : (Momentum × ℂ) × ℂ => (z.1.1,z.2)) (p,p.2) (by fun_prop)) contDiffAt_snd (by simp)
    simp_rw [iteratedDeriv_succ]; exact he.clm_apply (g:=fun _ => 1) contDiffAt_const

lemma line_cont (hf : ContDiffAt ℂ ω f 0) (n : ℕ) : Continuous (fun p => lineD f p n) := continuous_iff_continuousAt.mpr fun p =>
  ((ray_smooth (F:=fun z => f (z.2 • z.1)) ((show ContDiffAt ℂ ω f ((0:ℂ) • p) by simpa using hf).comp (p,0) (f:=fun z : Momentum × ℂ => z.2 • z.1) (contDiffAt_snd.smul contDiffAt_fst)) n).continuousAt.comp (f:=fun p => (p,0)) (continuousAt_id.prodMk continuousAt_const))
lemma frequent_ne_of_slope {p : Momentum} (h : fderiv ℂ f p ≠ 0) : ∃ᶠ z in 𝓝 p,f z ≠ 0 := fun hn => h (by rw [(show f =ᶠ[𝓝 p] 0 from hn.mono fun i hi => not_not.mp hi).fderiv_eq, fderiv_zero]; rfl)
lemma freqProj (i : Axis) (p : Momentum) : ∃ᶠ z in 𝓝 p, z i ≠ 0 := frequent_ne_of_slope (f:=fun z => z i) (by
    let L : Momentum →L[ℂ] ℂ := ContinuousLinearMap.proj i
    intro h; have he : fderiv ℂ L p = 0 := h; have hv := DFunLike.congr_fun (L.fderiv.symm.trans he) (unitAxis i); simp [L,unitAxis] at hv)
lemma freqQ (i : Axis) (p : Momentum) : ∃ᶠ z in 𝓝 p, q z i ≠ 0 := by
  let L : Momentum →L[ℂ] ℂ := ContinuousLinearMap.proj i
  refine frequent_ne_of_slope (f:=fun z => q z i) (fun h => ?_)
  have he := DFunLike.congr_fun ((((L.hasFDerivAt.const_mul I).cexp.sub_const 1).fderiv (x:=p)).symm.trans h) (unitAxis i)
  simp [L,unitAxis,exp_ne_zero, I_ne_zero] at he
lemma cancel_Q {f : Momentum → ℂ} (i : Axis) {p} (hf : ContinuousAt f p) (h : ∀ᶠ z in 𝓝 p, q z i * f z = 0) : f p = 0 := tendsto_nhds_unique_of_frequently_eq hf tendsto_const_nhds ((freqQ i p |>.and_eventually h).mono (fun _ ⟨hz,he⟩ => (mul_eq_zero.mp he).resolve_left hz))

lemma reduce_below (hf : ContDiffAt ℂ ω f 0) (i : Axis) (h : ∀ p,Below (fun z => q z i * f z) p (n+1)) (p : Momentum) : Below f p n := by
  induction n generalizing p with
  | zero => exact below_zero
  | succ n ih =>
    have he p := ih (fun p j hj => h p j (hj.trans (Nat.lt_succ_self _))) p
    refine below_succ.mpr ⟨he p,tendsto_nhds_unique_of_frequently_eq ((line_cont hf n).continuousAt (x:=p)) tendsto_const_nhds ((freqProj i p).mono fun z hz => ?_)⟩
    have hl := h z (1+n) (by omega)
    rw [Below.product (q_diff i).contDiffAt hf (q_below i) (he z),q_first] at hl
    have h1 : 1 + (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : 1+n ≠ 0)

    simpa [I_ne_zero,hz,h1] using hl

variable {η C : ℝ}
lemma division_order (i : Axis) (h : Vane f η) (hb : ∀ p∈Tube η, ‖f p‖≤ C) (he : ∀ p, Below f p (n+1)) (p : Momentum) : Below (divided i f) p n := by
  have hη : 0 < η/6 := by linarith [h.side]
  have h0 (η) (he : 0 < η) := Work.F07.realStrip _ he (star_zero (R:=Momentum))
  apply reduce_below (division_diff _ h hb (h0 _ hη)) i _ p
  intro z j hj; rw [line_congr (eventually_of_mem ((Work.F07.stripOpen _).mem_nhds (h0 _ hη)) (fun x hx => division_mult i h hb hx) : (fun z => q z i * divided i f z) =ᶠ[𝓝 0] fun z => f z - f (mask i z))]
  have hf := (PolyDisc.finiteD f (eventually_of_mem ((Work.F07.stripOpen _).mem_nhds (h0 _ h.side)) h.hol)).contDiffAt (n:=ω)
  have hg : ContDiffAt ℂ ω (f ∘ mask i) 0 := (show ContDiffAt ℂ ω f (mask i 0) by simpa using hf).comp 0 (mask_diff i).contDiffAt
  rw [line_sub hf (g:=fun z => f (mask i z)) hg,he _ j hj,show lineD (fun z => f (mask i z)) z j = lineD f (mask i z) j by simp only [lineD,mask_ray], he _ j hj,sub_zero]
end YM.Push.Loops
