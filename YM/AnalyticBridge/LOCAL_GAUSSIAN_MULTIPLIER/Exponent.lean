import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Jets
import YM.Next.BOUNDARY.Alias
import YM.Push.CUTOFF_PROJECTORS.Passage

/-!
# Jacobian/scalar/ratio arithmetic on ordered jets

In particular charge an exponential with the amplitude at this Z and *this*
sector (not worst-case exponential of a derivative allowance). Taylor radii
in `Ticket` here are order prices only. No claim of holomorphic continuation,
nor of interchange with a Z/Palm integral from exponentiating formal germs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Lattice Wilson RG Next.Foundations ProjectorNext.Equivariance
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k j : ℕ} {U : Config G n} {f g : Config G n → E}
  {D : Directions G n → Prop} {w v r s : ℝ}

/-- Positive ORDER tickets for exponents. Separate from value receipts. -/
structure Charge (D : Directions G n → Prop) (k : ℕ) (U : Config G n) (r : ℝ)
    (f : Config G n → E) : Prop where
  smooth : HasOrderAt f U k
  nonneg : 0 ≤ r
  price (l : List (Directions G n)) : l ≠ [] → l.length ≤ k → (∀ i∈l, D i) →
    ‖leftDerivs f l U‖ ≤ r^l.length

lemma Ticket.tip (h : Ticket D k U w r f) : Charge D k U ((1+w)*r) f := by
  refine ⟨h.smooth,mul_nonneg (add_nonneg zero_le_one h.price_nonneg) h.radius_nonneg, fun l he hl hi => ?_⟩
  apply (h.price _ hl hi).trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (calc
    w ≤ (1+w)^1 := by linarith
    _ ≤ (1+w)^l.length := pow_le_pow_right₀ (by linarith [h.price_nonneg]) (List.length_pos_iff.mpr he)) (pow_nonneg h.radius_nonneg _)

namespace Charge
lemma freeze (x : E) (hr : 0 ≤ r) : Charge D k U r (fun _ => x) := by
  classical
  refine ⟨contDiffAt_const,hr,fun l hl _ _ => ?_⟩
  rw [Work.G07.left_const]; split
  next h => exact (hl h).elim
  next => rw [norm_zero]; exact pow_nonneg hr _

lemma halt (h : Charge D k U r f) (he : j ≤ k) : Charge D j U r f :=
  ⟨h.smooth.fewer he,h.nonneg,fun l hi hl => h.price l hi (hl.trans he)⟩
lemma radius (h : Charge D k U r f) (he : r ≤ s) : Charge D k U s f :=
  ⟨h.smooth,h.nonneg.trans he,fun l hi hl H => (h.price l hi hl H).trans (pow_le_pow_left₀ h.nonneg he l.length)⟩
lemma offset (h : Charge D (k+1) U r f) {A : Directions G n} (hi : D A) :
    Ticket D k U r r (leftDerivs f [A]) := by
  refine ⟨last_shift A h.smooth,h.nonneg,h.nonneg,fun l hl H => ?_⟩
  rw [← Work.G07.left_append]
  refine (h.price _ (by simp) (by simpa) (fun i hi' => ?_)).trans_eq ?_
  · rcases List.mem_append.mp hi' with hh|hh
    · exact H _ hh
    rwa [List.mem_singleton.mp hh]
  simp only [List.length_append,List.length_singleton,pow_succ]; ring

lemma add (h : Charge D k U r f) (he : Charge D k U s g) : Charge D k U (r+s) (f+g) := by
  refine ⟨(show ContDiffAt ℝ k _ _ from h.smooth).add (show ContDiffAt ℝ k _ _ from he.smooth), add_nonneg h.nonneg he.nonneg,
    fun l hl hi H => ?_⟩
  rw [add_parts h.smooth he.smooth hi]
  apply (norm_add_le ..).trans ((add_le_add (h.price _ hl hi H) (he.price _ hl hi H)).trans ?_)
  cases l with
  | nil => exact (hl rfl).elim
  | cons i l =>
    simp only [List.length_cons,pow_succ, mul_add]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ h.nonneg (le_add_of_nonneg_right he.nonneg) l.length) h.nonneg
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ he.nonneg (le_add_of_nonneg_left h.nonneg) l.length) he.nonneg

lemma total {ι : Type*} {I : Finset ι} {r : ι → ℝ} {f : ι → Config G n → E}
    (h : ∀ i∈I, Charge D k U (r i) (f i)) : Charge D k U (∑ i∈I, r i) (∑ i∈I, f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact freeze _ le_rfl
  | insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))
end Charge

section real
lemma exp_cost {w v x y : ℝ} (hWx : Real.exp x ≤ w) (hWy : Real.exp y ≤ w)
    (h : ‖x-y‖ ≤ v) : ‖Real.exp x - Real.exp y‖ ≤ w*v := by
  rcases le_total y x with hh|hh
  · exact he' hWx h hh
  rw [norm_sub_rev]
  exact he' hWy ((norm_sub_rev ..).trans_le h) hh
where
  he' {x y : ℝ} (hWx : Real.exp x ≤ w) (h : ‖x-y‖ ≤ v) (he : y≤x) :
      ‖Real.exp x - Real.exp y‖ ≤ w*v := by
    rw [Real.norm_of_nonneg (sub_nonneg.mpr he)] at h
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (Real.exp_monotone he))]
    have h1 := Real.add_one_le_exp (y-x)
    rw [Real.exp_sub,le_div_iff₀ (Real.exp_pos x)] at h1
    exact le_trans (b:=Real.exp x*(x-y)) (by linarith only [h1])
      (mul_le_mul hWx h (sub_nonneg.mpr he) ((Real.exp_pos x).le.trans hWx))

variable {x y : Config G n → ℝ}

def climbing (k : ℕ) (r : ℝ) : ℝ := (k+1)*r
lemma climbing_succ (k : ℕ) (r : ℝ) : climbing (k+1) r = climbing k r + r := by unfold climbing; push_cast; ring
lemma climbing_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : r ≤ climbing k r := by unfold climbing; nlinarith only [Nat.cast_nonneg (α:=ℝ) k,hr]
lemma climbing_nonneg (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ climbing k r := hr.trans (climbing_le k hr)

lemma exp_part (h : HasOrderAt x U (k+1)) (A : Directions G n) :
    leftDerivs (Real.exp ∘ x) [A] U = Real.exp (x U) * leftDerivs x [A] U := by
  change deriv _ _ = _
  simpa only [zero_smul,Work.G07.at_zero_increment] using! ((left_has A (l:=[]) (Nat.zero_lt_succ _) h).exp).deriv

lemma exp_smooth (h : HasOrderAt x U k) : HasOrderAt (Real.exp ∘ x) U k :=
  (show ContDiffAt ℝ k _ _ from h).exp

lemma Charge.bill_exp (h : Charge D k U r x) (he : Real.exp (x U) ≤ w) :
    Ticket D k U w (climbing k r) (Real.exp ∘ x) := by
  have hw : 0 ≤ w := (Real.exp_pos _).le.trans he
  induction k with
  | zero =>
    refine ⟨exp_smooth h.smooth,hw,climbing_nonneg _ h.nonneg,fun l hl H => ?_⟩
    rw [Nat.le_zero,List.length_eq_zero_iff] at hl
    subst l
    simpa only [List.length_nil,pow_zero,mul_one,leftDerivs,comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le]
  | succ k ih =>
    have hx := climbing_le k h.nonneg
    have hr : climbing k r ≤ climbing (k+1) r := by rw [climbing_succ]; exact le_add_of_nonneg_right h.nonneg
    have hy := ih (h.halt (Nat.le_succ _))
    refine ⟨exp_smooth h.smooth,hw,hy.radius_nonneg.trans hr,fun l hl H => ?_⟩
    induction l using List.reverseRecOn with
    | nil => simpa only [List.length_nil,pow_zero,mul_one,leftDerivs,comp_apply,Real.norm_of_nonneg (Real.exp_pos _).le]
    | append_singleton l A _ =>
      have hK := hy.mul (h.offset (H A (by simp)))
      rw [Work.G07.left_append, along (H:=fun V => HasOrderAt x V (k+1)) h.smooth (fun V hv A => recur hv A)
        (show ∀ V, HasOrderAt x V (k+1) → leftDerivs (Real.exp ∘ x) [A] V = ((Real.exp ∘ x)*leftDerivs x [A]) V from fun V hv => exp_part hv A)]
      refine (hK.price l (by simpa using hl) (fun i hi => H _ (List.mem_append_left _ hi))).trans ?_
      rw [List.length_append,List.length_singleton,pow_succ',← mul_assoc,← climbing_succ]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hx.trans hr) hw) (pow_nonneg (climbing_nonneg _ h.nonneg) _)

/-- Cost both configurations at their respective logarithms. No
intermediate configuration or division by activity factors. -/
lemma Charge.bill_shift (hf : Charge D k U r x) (hg : Charge D k U r y) (hp : Ticket D k U v r (x-y))
    (he : Real.exp (x U) ≤ w) (he' : Real.exp (y U) ≤ w) :
    Ticket D k U (w*v) (climbing k r) ((Real.exp ∘ x)-(Real.exp ∘ y)) := by
  have hw : 0 ≤ w := (Real.exp_pos _).le.trans he
  induction k with
  | zero =>
    refine ⟨ContDiffAt.sub (exp_smooth hf.smooth) (exp_smooth hg.smooth),mul_nonneg hw hp.price_nonneg,climbing_nonneg _ hf.nonneg, fun l hl H => ?_⟩
    rw [Nat.le_zero,List.length_eq_zero_iff] at hl
    subst l; rw [List.length_nil,pow_zero,mul_one]; exact exp_cost he he' hp.base
  | succ k ih =>
    have hj := ih (hf.halt (Nat.le_succ _)) (hg.halt (Nat.le_succ _)) (hp.truncate (Nat.le_succ _))
    have hr : (2:ℝ)*r ≤ climbing (k+1) r := by have hh := climbing_le k hf.nonneg; rw [climbing_succ]; linarith only [hh]
    refine ⟨ContDiffAt.sub (exp_smooth hf.smooth) (exp_smooth hg.smooth), hj.price_nonneg,climbing_nonneg _ hf.nonneg,fun l hl H => ?_⟩
    induction l using List.reverseRecOn with
    | nil => rw [List.length_nil,pow_zero,mul_one]; exact hj.base
    | append_singleton l A _ =>
      let eX := Real.exp ∘ x; let dX := leftDerivs x [A]
      let eY := Real.exp ∘ y; let dY := leftDerivs y [A]
      let Z := fun V => HasOrderAt x V (k+1) ∧ HasOrderAt y V (k+1)
      have hz : Z U := ⟨hf.smooth,hg.smooth⟩
      have hd (V) (hV : Z V) (A : Directions G n) : ∀ᶠ t : ℝ in 𝓝 0, Z (increment V (t • A)) := (recur hV.1 A).and (recur hV.2 A)
      have hA := H A (by simp)
      have hb := hp.taper hA
      have hx := hf.offset hA
      have hy := hg.offset hA
      have hi : Ticket D k U (v*r) r (dX-dY) := by
        refine ⟨ContDiffAt.sub hx.smooth hy.smooth,hb.price_nonneg,hb.radius_nonneg,fun l hl hh => ?_⟩
        rw [← along hz hd (f:=leftDerivs (x-y) [A]) (g:=dX-dY) (fun i hi => sub_parts hi.1 hi.2 (by simp))]; exact hb.price l hl hh
      have hK := ((hf.halt (Nat.le_succ _)).bill_exp he).pair_shift hj hy hi
      have HH (i) (he : Z i) : leftDerivs (eX-eY) [A] i = (eX*dX-eY*dY) i := by
        rw [sub_parts (exp_smooth he.1) (exp_smooth he.2) (by simp),exp_part he.1,exp_part he.2]; rfl
      rw [Work.G07.left_append, along hz hd HH]
      refine (hK.price l (by simpa using hl) (fun i hi => H _ (List.mem_append_left _ hi))).trans ?_
      rw [List.length_append,List.length_singleton,pow_succ',← mul_assoc (w*v) (climbing (k+1) r) (climbing (k+1) r ^ l.length),← climbing_succ]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (climbing_nonneg _ hf.nonneg) _)
      have hW := hj.price_nonneg
      calc w*(v*r)+w*v*r=w*v*(2*r) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left hr hW

lemma Ticket.mayer (h : Ticket D k U w r x) :
    Ticket D k U (Real.exp w*w) (climbing k ((1+w)*r)) ((Real.exp ∘ x)-1) := by
  have hi := h.price_nonneg
  have hu : r ≤ (1+w)*r := le_mul_of_one_le_left h.radius_nonneg (by linarith)
  have hz (U : Config G n) : Real.exp ((0 : Config G n → ℝ) U) = 1 := Real.exp_zero
  rw [show (1:Config G n → ℝ)=Real.exp ∘ (0:Config G n → ℝ) from funext (fun U => (hz U).symm)]
  apply h.tip.bill_shift (y:=(0 : Config G n → ℝ)) (Charge.freeze (0:ℝ) (h.radius_nonneg.trans hu))
  · rw [sub_zero]; exact h.mono le_rfl hu
  · exact Real.exp_monotone ((le_abs_self _).trans h.base)
  rw [hz]; exact Real.one_le_exp hi


end real
end YM.AnalyticBridge.LocalGaussian
