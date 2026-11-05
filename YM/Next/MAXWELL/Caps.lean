import YM.Euclid.Comparator
import YM.Next.MAXWELL.Core


/-!
# Free test obligations on Bel

Ranks without any quotient identification of YM. The only null sector
of the freeTable is the equation sector. Positivity and H spin hold on
this actual table. Uniform positional caps at order zero now (can
raise by Bid.B10 after producing the derivatives).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Table.Pairing Wick Occ
open scoped ContDiff Topology BigOperators ComplexOrder
variable {G : Gauge} {n : ℕ}

section price
private def Holds (f : Points n → ℂ) := ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
    ∀ x, spaced r x → ‖f x‖ ≤ C*r⁻¹^A

private lemma holds_fix (c : ℂ) : Holds (n:=n) (fun _ => c) := ⟨0,‖c‖,norm_nonneg _,by simp⟩

private lemma holds_add {f g : Points n → ℂ} (hf : Holds f) (hg : Holds g) : Holds (f+g) := by
  obtain ⟨A,C,hc,H⟩ := hf
  obtain ⟨B,D,hd,K⟩ := hg
  refine ⟨A+B,C+D,add_nonneg hc hd,fun r hr hu x hx => ?_⟩
  have hp : 1 ≤ r⁻¹ := one_le_inv₀ hr |>.mpr hu
  rw [add_mul]
  refine (norm_add_le _ _).trans ((add_le_add (H r hr hu x hx) (K r hr hu x hx)).trans ?_)
  gcongr <;> omega

private lemma holds_mul {f g : Points n → ℂ} (hf : Holds f) (hg : Holds g) : Holds (f*g) := by
  obtain ⟨A,C,hc,H⟩ := hf
  obtain ⟨B,D,hd,K⟩ := hg
  refine ⟨A+B,C*D,mul_nonneg hc hd,fun r hr hu x hx => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  calc
    _ ≤ (C*r⁻¹^A)*(D*r⁻¹^B) := by gcongr; exacts [H r hr hu x hx,K r hr hu x hx]
    _ = _ := by rw [pow_add]; ring

private lemma holds_sum {ι : Type*} (s : Finset ι) (f : ι → Points n → ℂ) (H : ∀ i ∈ s,Holds (f i)) :
    Holds (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using holds_fix (n:=n) 0
  | @insert i s h ih =>
    simp_rw [Finset.sum_insert h]; exact holds_add (H i (by simp)) (ih fun a ha => H a (Finset.mem_insert_of_mem ha))

private lemma holds_prod {ι : Type*} (s : Finset ι) (f : ι → Points n → ℂ) (H : ∀ i ∈ s,Holds (f i)) :
    Holds (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using holds_fix (n:=n) 1
  | @insert i s h ih =>
    simp_rw [Finset.prod_insert h]; exact holds_mul (H i (by simp)) (ih fun a ha => H a (Finset.mem_insert_of_mem ha))

private lemma entry_hold (p q : Slot G) (a b : Fin n) (h : a≠b) : Holds (fun x : Points n => entry p q (x a) (x b)) := by
  obtain ⟨C,hc,H⟩ := (kernel_pole (coordinateLeg p) (coordinateLeg q)).bounds
  refine ⟨4+p.1+q.1,C,hc,fun r hr hp x hx => ?_⟩
  have he : r ≤ ‖x a - x b‖ := le_trans (hx a b h) (by
    unfold cubedist; rw [dist_eq_norm_sub]; apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i; exact PiLp.norm_apply_le (x a-x b) i)
  unfold entry; rw [Complex.norm_real]
  apply (H _ (norm_pos_iff.mp (hr.trans_le he))).trans; gcongr

lemma cap_moment (v : Fin n → WickPol G) : ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
    ∀ x, spaced r x → ‖moment G x v‖ ≤ C*r⁻¹^A := by
  classical
  change Holds (fun x => moment G x v)
  simp_rw [sumFormula]; apply holds_sum
  intro i _; refine holds_mul (holds_fix _) (show Holds (fun x => monomial x i) from holds_sum _ _ fun P _ => ?_)
  exact holds_prod (corners P) _ fun p _ => entry_hold _ _ _ _ (different P p).symm

lemma kernel_analytic {x : Points n} (v : Fin n → WickPol G) (h : x ∈ conf n) :
    ContDiffAt ℝ ω (fun y => moment G y v) x := by
  classical
  have he (p q : Slot G) (a b : Fin n) (h' : a≠b) : ContDiffAt ℝ ω (fun z : Points n => entry p q (z a) (z b)) x := by
    have hx : x a-x b ∈ away := sub_ne_zero.mpr ((show Injective x.ofLp from h).ne h')
    have ht (i : Fin n) : ContDiffAt ℝ ω (fun y : Points n => y i) x :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ => E4) i).contDiff.contDiffAt
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x (((kernel_pole (coordinateLeg p) (coordinateLeg q)).diff _ hx).comp x (f:=fun z : Points n => z a-z b) ((ht a).sub (ht b)))
  simp_rw [sumFormula]; apply ContDiffAt.sum
  intro i _; apply contDiffAt_const.mul; unfold monomial; apply ContDiffAt.sum
  intro P _; exact contDiffAt_prod fun j hj => he _ _ _ _ (different P j).symm
end price

lemma no_residual (G : Gauge) (d : ℕ) : residual G d=⊥ := by
  apply le_antisymm _ bot_le; intro y hy
  by_contra hs
  have ht : y.val≠0 := fun h => hs ((Submodule.mem_bot ..).mpr (Subtype.ext h))
  let x := basis timeAxis
  let w := points (fun _ : Fin 1 => x)
  let s := Signed.reflect timeAxis
  have hp : 0 < score timeAxis x y.val y.val := detects _ _ (by simp [x]) _ ht
  have hu : single w timeAxis := ⟨injective_of_subsingleton _,fun _ => by simp [w,x]⟩
  let z : Points (1+1) := closedUp timeAxis w w
  let r := Equiv.swap (0 : Fin (1+1)) 1
  have hr : z ∈ conf _ := Table.Pairing.spans hu hu
  obtain ⟨p,H⟩ := (show y.val ∈ shellSector G d from y.property)
  let q : shellSector G d := (observable G d).rangeRestrict (Labels.tensor s (Labels.realBar p))
  have He : score timeAxis x y.val y.val = (ProbeFamily.mk 1 (fun _ => d) (fun _ => q) (Points.rearrange r z) (Points.rearrange_in r hr)).test d y := by
    rw [test_formula]
    let t := Fin.append (mirrorBar (G:=G) s ∘ (fun _ : Fin 1 => y.val)) (fun _ : Fin 1 => y.val)
    change moment G z t = _
    have he : q.val = mirrorBar s y.val := by
      rw [← H]; exact (pulls_label ..).trans (congr_arg (reflectPol s) (real_eats p))
    rw [exchangeSites r hr t]; congr 1
    ext1 i; fin_cases i <;> simp [r,t,he, Points.rearrange] <;> rfl
  rw [He, show ProbeFamily.test _ d y = _ from congr_fun (LinearMap.mem_ker.mp hy) _] at hp
  exact lt_irrefl _ hp

variable (L : Labels.Frames G)

def ready (p : (standard L).Token) := observable G p.1 ((L.level _).coords.symm p.2)

lemma ready_signed (s : Signed) (p : (standard L).Token) :
    ready L ((standard L).move s p) = reflectPol s.ortho (ready L p) := by
  unfold ready Register.move; rw [← pulls_label]; congr 1
  simp [Register.mirrorGroup, standard, Labels.Frame.act, Register.coord]; exact (L.level p.1).coords.symm_apply_apply _
lemma ready_bar (p : (standard L).Token) : ready L ((standard L).conjugate p) = realForm (ready L p) := by
  unfold ready Register.conjugate; rw [← real_eats]
  exact congr_arg (observable G _) ((standard L).geom_conj _ _).symm

lemma spin_free : (freeTable L).RealSpin where
  mirror s x v q := by
    rw [decodes,decodes]; change moment _ _ (fun i => ready L ((standard L).move s (q i)))=moment _ _ (fun i => ready L (q i))
    simp_rw [ready_signed]; exact moment_rotation _ v _ _
  real := by
    intro n x h v
    change moment G x (fun i => ready L ((standard L).conjugate (v i))) = star (moment G x (fun i => ready L (v i)))
    simp_rw [ready_bar]; exact moment_real _ h _


lemma positive_table : (freeTable L).RP := by
  intro a m w h c
  let x i := Word.positions (w i)
  let v i := Word.tokens (w i)
  let p i := ready L ∘ v i
  have ht i : single (x i) a := ⟨(h i).1,fun j => (h i).2 ((w i).get j) (List.get_mem ..)⟩
  have he i j : (freeTable L).gram a (w i) (w j) = cabinet a (x i) (x j) (p i) (p j) := by
    calc
      _ = (freeTable L).gram a (Word.realize (v i) (x i)) (Word.realize (v j) (x j)) := by simp [x,v]
      _ = _ := by
        rw [displacement _ (table_sym L) _ _ (ht i) (ht j)]
        change moment G _ (ready L ∘ tied (v i) (v j) a) = _
        unfold cabinet
        congr 1
        ext1 k; refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp only [Function.comp_apply,
          tied,Fin.append_left,Fin.append_right]
        · rw [← Register.token_adjoint, ready_signed,ready_bar]; rfl
        rfl
  simp_rw [he]; exact cabinets_positive a x ht p c
end YM.Maxwell.Free
