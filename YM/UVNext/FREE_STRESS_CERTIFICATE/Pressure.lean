import YM.UVNext.FREE_STRESS_CERTIFICATE.Choose
import YM.UVNext.FREE_STRESS_CERTIFICATE.Contact
import YM.UVNext.FREE_STRESS_CERTIFICATE.TripleMeter



set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Fix the numerical κ on canonical MaxwellData

Test `lit.delta` on only the degree-four square pair. Don't need any
general determinant or Ward validity ante beyond success of delta on this
sample (and W reading d4 derivatives). Does not establish delta on every
B,q from W/K/κ, as would be needed to fill MaxwellData, but a necessity
result for those assemblers and for `ignite`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Set MeasureTheory Filter Analysis Function Table Work.A01 Climb Labels Next.UVStress
open scoped Topology ContDiff RealInnerProductSpace
variable {G : Gauge} (F : Frames G) (τ : ℝ)

private def earth : Points 2 := points (readings 0 (-basis 0))
@[simp] private lemma center : earth 0=0 := rfl
@[simp] private lemma abroad : earth 1= -basis 0 := read_one 0 _
private lemma farAway : earth∈conf _ := by
  have he : earth 0≠earth 1 := fun h => (zero_ne_one (α:=ℝ)) (by simpa using congr_arg norm h)
  intro i j h; rcases (show i=(0:Fin 2)∨i=1 by fin_cases i <;> decide) with rfl|rfl <;> rcases (show j=(0:Fin 2)∨j=1 by omega) with rfl|rfl
  exacts [rfl,(he h).elim,(he h.symm).elim,rfl]

private def sea : Set E4 := {z | z≠ -basis 0}
private def wake : Maxwell.Field ℝ := fun i j x => bareCurl i j 0 1 (x+basis 0)

private lemma chain (f : E4 → ℝ) {x} (h : DifferentiableAt ℝ f (x+basis 0)) (a) :
    grad a (fun x : E4 => f (x+basis 0)) x=grad a f (x+basis 0) := by
  unfold grad D
  change fderiv ℝ (f ∘ fun x => id x+basis 0) x _ = _
  rw [fderiv_comp x h (differentiableAt_id.add_const _),(hasFDerivAt_id x).add_const (basis 0) |>.fderiv,ContinuousLinearMap.comp_apply]; rfl

private lemma sail : WaveOn sea wake := by
  have he {x} (hx : x∈sea) : x+basis 0≠0 := fun hh => hx (eq_neg_of_add_eq_zero_left hh)
  have ht (a b : Axis) (x) (hx : x∈sea) := Bare.curl_diff (he hx) a b 0 1
  have hd (a i j : Axis) (x) (hx : x∈sea) : grad a (wake i j) x = grad a (bareCurl i j 0 1) (x+basis 0) :=
    chain _ ((ht i j x hx).differentiableAt (by simp)) a
  refine ⟨fun a b x hx => (ht a b x hx).comp x (contDiffAt_id.add contDiffAt_const),
    fun a b x hx => (Bare.equation 0 1).form a b _ (he hx), fun a b c x hx => ?_, fun b x hx => ?_⟩
  · simp_rw [hd _ _ _ x hx]; exact (Bare.equation 0 1).cycle a b c _ (he hx)
  simp_rw [hd _ _ _ x hx]; exact (Bare.equation 0 1).divergence b _ (he hx)

private lemma on_wake : grad 0 (wake 0 1) 0 = 16 * normal := by
  have h : (0:E4)+basis 0≠0 := by intro h; simpa using congr_arg norm h
  change grad 0 (fun x => bareCurl 0 1 0 1 (x+basis 0)) 0=_
  rw [chain _ ((Bare.curl_diff h 0 1 0 1).differentiableAt (by simp)),zero_add,view_ray,
    show rotate (ray 0 0) 0 1 0 1=16 from by decide]; push_cast; ring

private def call : FourFields F := flat F 0 1 0 1
private def cap : Fin 1→(freeTable F).Tag := fun _ => ⟨4,call F⟩
private def monitor (a : Axis) (z : E4) := crossing (fun i j => bareCurl i j 0 1 z) (fun i j => wake i j z) a (0:Axis)
private def burning (G : Gauge) := 4*(G.lieDim:ℝ)*(-4*normal)

private lemma transmitted {χ : E4 → ℝ} (hχ : Window earth χ) (a : Axis) :
    ∫ z : E4, ((D (basis a) χ z : ℝ):ℂ) * (freeTable F).useAt (freeTable F) (Points.cons z earth)
          (Fin.cons ⟨4,torch F τ a 0⟩ (Fin.cons ⟨4,call F⟩ (cap F))) =
      ((τ * burning G * (∫ z, D (basis a) χ z * monitor a z) : ℝ):ℂ) := by
  rw [show (fun z : E4 => ((D (basis a) χ z : ℝ):ℂ) * (freeTable F).useAt (freeTable F) (Points.cons z earth)
          (Fin.cons ⟨4,torch F τ a 0⟩ (Fin.cons ⟨4,call F⟩ (cap F)))) =
      fun z : E4 => ((τ*burning G : ℝ):ℂ) * ((D (basis a) χ z * monitor a z : ℝ):ℂ) from ?_, integral_const_mul]
  · rw [integral_complex_ofReal]; push_cast; rfl
  funext z
  by_cases he : D (basis a) χ z=0
  · simp [he]
  have hm := separated_of_D farAway hχ he
  have hi := battery F τ hm 0 1 0 1 a 0
  have h (s : E4) : (Points.cons s earth) 1=0 := by
    change (Points.cons s earth) (0:Fin 2).succ=0; rw [Points.cons,points_apply,Fin.cons_succ,center]
  have hw (s : E4) : (Points.cons s earth) 2= -basis 0 := by
    change (Points.cons s earth) (1:Fin 2).succ= -_; rw [Points.cons,points_apply,Fin.cons_succ,abroad]
  have hc : charge (G:=G) (Points.cons z earth) 0 1 0 1= burning G := by
    unfold charge burning; rw [h z,hw z, zero_sub,neg_neg,one_view,show rotate (curve 0) 0 1 0 1 = -4 from by decide]; push_cast; ring
  rw [hc] at hi
  unfold monitor wake
  rw [show Fin.cons (α:=fun _ : Fin 2 => (freeTable F).Tag) ⟨4,call F⟩ (cap F)= readings ⟨4,call F⟩ ⟨4,call F⟩ from rfl,
    ← front_eval]
  change ↑(D (basis a) χ z) * tripod F (Points.cons z earth) 0 1 0 1 _ = _
  rw [hi]
  rw [h z,hw z, show Points.cons z earth 0=z from rfl,sub_zero,sub_neg_eq_add]
  push_cast; ring

section callK
variable (W : DiffPlan (freeTable F))

-- same kernel differentiation reading as before, now translated to (0,-basis 0)
lemma at_tower (hW : W.Derivatives (freeTable F)) :
    (freeTable F).useAt (freeTable F) earth (Fin.cons ⟨5,W.deriv 4 0 (call F)⟩ (cap F)) =
      -256*(G.lieDim:ℂ)*(normal:ℂ)^2 := by
  rw [show cap F = negs F 0 1 0 1 from rfl, ← listens F earth 0 1 0 1]
  -- compare hearing at the camera by homogeneity (any arity), or redo germ
  let w := Fin.cons (α:=fun _ : Fin 2 => (freeTable F).Tag) ⟨4,call F⟩ (cap F)
  let f := fun y : Points 2 => (freeTable F).useAt (freeTable F) y w
  have H (v : Fin 2 → (freeTable F).Tag) (x y : Points 2) (h : x 0-x 1 = y 0-y 1) :
      (freeTable F).useAt (freeTable F) x v = (freeTable F).useAt (freeTable F) y v := by
    -- decisions use abstract moment not only ff samples
    let A i := v i
    suffices h : Maxwell.Wick.moment G x = Maxwell.Wick.moment G y from
      DFunLike.congr_fun h (fun i => observable G (A i).1 ((F.level (A i).1).coords.symm ((freeTable F).representative _ (A i).2)))
    refine Module.Basis.ext_multilinear (fun _ => Maxwell.Wick.monBasis G) fun g => ?_
    simp_rw [Maxwell.Wick.moment_basis,Maxwell.Wick.monomial]; apply Finset.sum_congr rfl; intro k _
    unfold Wick.Occ.graph
    apply Finset.prod_congr rfl; rintro j hj
    have he : j.label < (Wick.Occ.partner k j).label := (Finset.mem_filter.mp hj).2
    unfold Wick.Occ.edge Wick.entry
    rw [show j.label=0 by omega,show (Wick.Occ.partner k j).label=1 by omega, h]
  have hh := listens_to F W hW 0 0 0 1 0 1 0 1 0 1
  rw [listens F, H _ earth (camera 0) (by simp), ← listens F _ 0 1 0 1,show hearing _ _ _ _ _ _ _ (W.deriv 4 0 (call F)) =_ from hh,show slide 0 0 0 1 0 1 0 1 0 1 = -256 from by decide]
  unfold loud; push_cast; ring

lemma translation_signal (κ : ℝ) (χ : E4 → ℝ) (hχ : Window earth χ) (p : Ward.SpinRows (freeTable F))
    (h : StressLaws (freeTable F) (torch F τ) (κ • W.deriv) p) :
    -∑ a : Axis, (((τ * burning G * ∫ z, D (basis a) χ z * monitor a z):ℝ):ℂ)=
      ((κ:ℝ):ℂ) • (freeTable F).useAt (freeTable F) earth (Fin.cons ⟨5,W.deriv 4 0 (call F)⟩ (cap F)) := by
  simp_rw [← transmitted F τ hχ]
  have he := h.translation farAway (cap F) hχ 0 4 (call F)
  rw [← front_eval, ← map_smul]
  exact he.trans <| by rw [front_eval]; congr 3

/-- Necessity of the *numeric* normalization `κ=-τ` as well (from δ success
on the real comparator). In particular the canonical t=1 output of `ignite`
uses κ=-1, not merely some unknown factor. -/
theorem negated (hG : G.Simple) (κ : ℝ) (p : Ward.SpinRows (freeTable F))
    (hW : W.Derivatives (freeTable F)) (h : StressLaws (freeTable F) (torch F τ) (κ • W.deriv) p) : κ= -τ := by
  obtain ⟨χ,hχ⟩ := exists_window earth farAway
  have ha : tsupport χ ⊆ sea := by
    intro x hx h
    exact hχ.2.2.2 (0:Fin 1) (by change earth (1:Fin 2) ∈ _; rwa [abroad, ← h])
  have hx := translation_signal F τ W κ χ hχ p h
  simp_rw [← Complex.ofReal_sum,← Finset.mul_sum] at hx
  have ht := single_cross wake sail (show IsOpen sea from isOpen_compl_singleton) χ hχ.1 hχ.2.1 ha (center ▸ hχ.2.2.1) 0 1 0
  rw [on_wake] at ht
  change -(∑ a : Axis, ∫ z, D (basis a) χ z * monitor a z) = _ at ht
  have hv : ∑ a : Axis, ∫ z, D (basis a) χ z * monitor a z = 16*normal := neg_injective ht
  rw [hv,at_tower F W hW, smul_eq_mul] at hx
  unfold burning at hx
  have hp : G.lieDim ≠ 0 := by
    rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := hG.nontrivial_color; exact Module.finrank_pos.ne'
  apply Complex.ofReal_injective
  apply (mul_right_cancel₀ (show (G.lieDim:ℂ)*(normal:ℂ)^2*256 ≠ 0 by exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hp) (by exact_mod_cast pow_ne_zero 2 normal_pos.ne')) (by norm_num)))
  push_cast at *
  linear_combination hx
end callK

open Org
variable {C : Family G}

/-- In particular, callers using from_data obtain the exact κ as well. -/
theorem required (h : G.Simple) (T : MaxwellData C) (ht : T.T.J=torch C.book.grid τ) : T.T.κ= -τ := by
  have he := T.lit.delta
  rw [ht] at he
  exact negated C.book.grid τ _ h _ _ T.lit.pales he

/-- Assemble canonical MaxwellData at E-normalized flux even if only some
other MaxwellData was constructed so far (no waiver for that extremely
strong obligation incl window identities). Use before weak-sequence choices
as for `Choose.fire`. -/
theorem names (hG : G.Simple) (T : MaxwellData C) (h : τ≠0) : ∃ Q : MaxwellData C,
    Q.T.J=torch C.book.grid τ ∧ Q.T.κ= -τ ∧ Q.vacuum=T.vacuum ∧ Q.T.W=T.T.W ∧ Q.T.K=T.T.K ∧
      Tensorial T.T.K Q.T.J ∧ FreeDiv Q.T Q.hT Q.lit.hers := by
  obtain ⟨Q,hv,hV,hD,hb,-,ha,ha'⟩ := fire hG T τ h
  exact ⟨Q,hv,required τ hG Q hv,hb,hV,hD,ha,ha'⟩

end YM.UVNext.FreeStress
