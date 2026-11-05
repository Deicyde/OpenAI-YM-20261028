import YM.Next.MAXWELL.System

/-!
# Why the tensor rotation on Bel gives actual finite matrices (entire extension)

Analytic lift on complex matrix-entry arrays. Don't use values off
(admissible, seen by analytic continuation) matrices as any claimed
group action. We'll only specialize to descended matrices later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} (F : Labels.Frames G) {d n : ℕ}

abbrev Ink := Axis → Axis → ℂ
def paints (s : Ortho) : Ink := fun i j => (s.val i j : ℂ)

lemma reads_cont : Continuous paints := continuous_pi fun i => continuous_pi fun j =>
  Complex.continuous_ofReal.comp (show Continuous fun s : Ortho => s.val i j from ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)))

def Writes (f : Ortho → ℂ) : Prop := ∃ g : Ink → ℂ, ContDiff ℂ ω g ∧ ∀ s, g (paints s)=f s

private lemma writes_const (x : ℂ) : Writes (fun _ => x) := ⟨_,contDiff_const,fun _ => rfl⟩
private lemma writes_mul {f g} (h : Writes f) (k : Writes g) : Writes (fun x => f x*g x) := by
  obtain ⟨a,A,ha⟩ := h; obtain ⟨b,B,hb⟩ := k; exact ⟨fun z => a z*b z,A.mul B,fun s => by dsimp; rw [ha,hb]⟩
private lemma writes_add {f g} (h : Writes f) (k : Writes g) : Writes (fun x => f x+g x) := by
  obtain ⟨a,A,ha⟩ := h; obtain ⟨b,B,hb⟩ := k; exact ⟨fun z => a z+b z,A.add B,fun s => by dsimp; rw [ha,hb]⟩

/-- Complex stencil on real test Taylor coefficients (acts on the two
    curvature indices and *all* of the derivative indices). -/
def curled (A : Shell G d) (v : Fin d → E4) (c : G.ColorIndex) (a b : Axis) (Z : Ink) :=
    ∑ i : Axis, ∑ l : Axis, Z i a * Z l b * (∑ w : Fin d → Axis,
      (∏ k : Fin d, ∑ m : Axis, Z (w k) m * (v k m : ℂ)) * (A.val i l (basis ∘ w) c : ℂ))

lemma writes_basic (A : Shell G d) (v : Fin d → E4) (c : G.ColorIndex) (a b : Axis) :
    ContDiff ℂ ω (curled A v c a b) ∧ ∀ s : Ortho, curled A v c a b (paints s) =
    (probeTurn s (leg v c a b) A : ℂ) := by
    classical
    let T (k : Fin d) (Z : Ink) (i : Axis) : ℂ := ∑ l : Axis, Z i l * (v k l : ℂ)
    let L (i l : Axis) (Z : Ink) := ∑ w : Fin d → Axis,
      (∏ k : Fin d, T k Z (w k)) * (A.val i l (basis ∘ w) c : ℂ)
    change ContDiff ℂ ω (fun Z => ∑ i : Axis, ∑ l : Axis, Z i a * Z l b * L i l Z) ∧ _
    refine ⟨?_,fun s => ?_⟩
    · have he (i l : Axis) : ContDiff ℂ ω (L i l) := by
        unfold L; refine ContDiff.sum fun w _ => ContDiff.mul (contDiff_prod ?_) contDiff_const
        intro k _; unfold T
        apply ContDiff.sum; intro l _; exact ContDiff.mul (by fun_prop) contDiff_const
      apply ContDiff.sum; intro i _; apply ContDiff.sum; intro l _
      exact ContDiff.mul (ContDiff.mul (by fun_prop) (by fun_prop)) (he i l)
    · have ht (i l : Axis) : L i l (paints s) = ((A.val i l (Ortho.move s ∘ v) c : ℝ):ℂ) := by
        let g := fun k => Ortho.move s (v k)
        have hi k a : T k (paints s) a = (g k a:ℂ) := by simp only [T,paints,← Complex.ofReal_mul,← Complex.ofReal_sum]; rfl
        have hk : A.val i l g = ∑ w : Fin d → Axis,(∏ k : Fin d,g k (w k)) • A.val i l (basis ∘ w) := by
          let B := A.val i l
          let U (k : Fin d) (i : Axis) := g k i • basis i
          conv_lhs => rw [show g=fun k => ∑ i, U k i from funext fun k => by ext a; simp [U]]
          rw [ContinuousMultilinearMap.map_sum]
          apply Finset.sum_congr ?_
          · intro k _; exact B.map_smul_univ _ _
          ext w; simp
        change L _ _ _ = (A.val i l g c:ℂ); rw [hk]; simp only [WithLp.ofLp_sum,Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
        unfold L; simp_rw [hi]; push_cast; rfl
      change (∑ i : Axis, ∑ l : Axis, paints s i a * paints s l b * L i l (paints s))= (turnJ s⁻¹ A.val a b v c : ℂ)
      simp_rw [turns_apply,inv_entry,inv_inv,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul, ht]; push_cast; rfl

lemma writes_entry (p : Probe G d) (A : Shell G d) : Writes (fun s => (probeTurn s p A : ℂ)) := by
  classical
  induction p using leg_probe_induction with
  | vars v c a b =>
    exact ⟨_, (writes_basic A v c a b).1,(writes_basic A v c a b).2⟩
  | zero => simpa using writes_const 0
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply,Complex.ofReal_add]; exact writes_add hp hq
  | smul t p hp =>
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; exact writes_mul (writes_const _) hp

lemma writes_pol (A : TaylorTower G) (p : WickPol G) : Writes (fun s => probe A (reflectPol s p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [reflectPol,probe] using writes_const a
  | add p q hp hq => simpa only [map_add] using writes_add hp hq
  | mul_X p k hp =>
    simp_rw [← symbol_coordinate k, map_mul,reflect_symbol,symbol_test]
    exact writes_mul hp (writes_entry _ _)

lemma writes_derivative (A : TaylorTower G) (p : WickPol G) (s : Ortho.Skew) :
    HasDerivAt (fun t => probe A (reflectPol (Ortho.oneParameter s t) p)) (probe A (rewired (wheel G s) p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [reflectPol,rewired,probe]; exact hasDerivAt_const _ _
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p k hp =>
    rw [← symbol_coordinate k]; simp_rw [map_mul,reflect_symbol,symbol_test,Derivation.leibniz, smul_eq_mul,
      map_add,map_mul,rewired_symbol,symbol_test]
    have he := hp.fun_mul (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (rotate_test s (coordinateLeg k) (A k.1)))
    refine he.congr_deriv ?_
    rw [Function.comp_apply,Work.A13.oneParameter_zero, pol_one];
    have hs : ∀ q : Probe G k.1, probeTurn 1 q=q := fun q => by
      ext x; change q (solutionTurn (1:Ortho)⁻¹ x)=_; rw [inv_one,solution_id]
    rw [hs,mul_comm (probe A (rewired (wheel G s) p)),add_comm]; rfl

variable (d)

def process (A : TaylorTower G) : (Model F).Field d →ₗ[ℂ] ℂ :=
  (probe A).toLinearMap.comp (address F d)

lemma separates : Submodule.span ℂ (Set.range (process F d)) = ⊤ := by
  let V := Submodule.span ℂ (Set.range (process F d))
  change V=⊤
  have he : V.dualCoannihilator=⊥ := by
    apply le_antisymm _ bot_le; intro p hp; apply (Submodule.mem_bot ..).mpr
    apply address_inj F d; rw [map_zero]; refine equalPol _ _ fun A => ?_
    rw [map_zero]; exact (Submodule.mem_dualCoannihilator _).1 hp _ (Submodule.subset_span ⟨A,rfl⟩)
  apply Submodule.eq_top_of_finrank_eq
  have hm := Subspace.finrank_add_finrank_dualCoannihilator_eq V
  rw [he,finrank_bot,add_zero] at hm
  rw [hm,Subspace.dual_finrank_eq]

lemma paints_gear (s : Ortho) (x : (Model F).Field d) : address F d ((gear F).act d s x) = reflectPol s (address F d x) :=
  address_rot ..

lemma writes_any (p : Module.Dual ℂ ((Model F).Field d)) (x : (Model F).Field d) :
    Writes (fun s => p ((gear F).act d s x)) := by
  refine Submodule.span_induction (p := fun p _ => Writes (fun s => p ((gear F).act d s x)))
    ?_ (writes_const _) (fun a b _ _ ha hb => writes_add ha hb)
    (fun c a _ ha => writes_mul (writes_const c) ha) (show p∈_ from separates F d |>.symm ▸ Submodule.mem_top)
  rintro w ⟨A,rfl⟩
  change Writes (fun s => probe A (address F d _)); simp_rw [paints_gear]
  exact writes_pol ..

lemma actual_generator (v : Module.Dual ℂ ((Model F).Field d)) (u : (Model F).Field d) (s : Ortho.Skew) :
    HasDerivAt (fun t => v ((gear F).act d (Ortho.oneParameter s t) u)) (v ((gear F).lie d s u)) 0 := by
  refine Submodule.span_induction (p := fun v _ => HasDerivAt (fun t => v ((gear F).act d (Ortho.oneParameter s t) u))
    (v ((gear F).lie d s u)) 0) ?_ (hasDerivAt_const (0:ℝ) (0:ℂ)) (fun _ _ _ _ ha hb => ha.add hb)
    (fun c b _ h => h.const_mul c) (show v ∈ _ from separates F d |>.symm ▸ Submodule.mem_top)
  rintro v ⟨A,rfl⟩; change HasDerivAt (fun t => probe A (address F d _))
    (probe A (address F d (scopeRise F d s u))) 0
  simp_rw [paints_gear,scopeRewrite]; exact writes_derivative ..
end YM.Maxwell.Free
