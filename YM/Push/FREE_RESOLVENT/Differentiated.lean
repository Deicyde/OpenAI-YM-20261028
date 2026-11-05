import YM.Analysis.Polydisc
import YM.Push.FREE_RESOLVENT.Inverse
import YM.Push.FREE_RESOLVENT.Polar

/-!
# Inverse jets with polynomial input weights or fixed external positions

Give a coefficientwise price recursion on polarized derivatives. Genuine
Fréchet derivatives at the tested point; no differential on changing masks
here. s a reserved exponential rate of A, γ a usable
strip rate of its resolvent before the derivative comparisons, ε the small
positive-derivative factor; d an amount per mark per jump (up to k marks at once).
At most 2 reserved jumps spent per order (not per RG step). Works identically
on every principal compression; the formulas don't trim boundary rows.

The only regularity assumption is on the given precision. The magnitude
hypotheses `Knew` below are on derivatives THROUGH k of the precision itself,
plus positive L² gap. No weighted-inverse inputs. Preserve at least two factors
of `(1+u)⁻¹` (so integrable decay) in all positive derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Matrix RG Precision Laurent Bloch Mark TestD Filter Topology
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {τ X E ι κ μ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]

namespace TestD
variable {C : Mark τ X} {D : Cost X} {A B : E → Matrix ι ι ℝ} (v : τ → E) {x : E}

/-- Actual map on an open parameter germ where invertible; total via det.
No global differentiability assertion. -/
def action (A : E → Matrix ι ι ℝ) (u : ℝ) (x : E) := resolve (A x) u

def Neat (A : E → Matrix ι ι ℝ) (u : ℝ) (x : E) := IsUnit (A x+u • 1).det

omit [NormedSpace ℝ E] in
lemma germ_valid {u : ℝ} (h : Neat A u x) (hp : ContinuousAt A x) : ∀ᶠ y in 𝓝 x, Neat A u y := by
  unfold Neat at *
  simp_rw [isUnit_iff_ne_zero] at *
  have he : ContinuousAt (fun z => (A z + u • 1).det) x := continuous_id.matrix_det.continuousAt.comp (hp.add continuousAt_const)
  exact he.eventually_ne h

lemma action_smooth {k : ℕ} {u : ℝ} (h : Neat A u x) (hw : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (action A u) x := by
  let F := fun z => A z + u • 1
  have hh : ContDiffAt ℝ k F x := hw.add contDiffAt_const
  have he : IsUnit (F x) := ((F x).isUnit_iff_isUnit_det).mpr h
  have ht := he.unit_spec
  have hp : ContDiffAt ℝ k Ring.inverse (F x) := ht ▸ contDiffAt_ringInverse ℝ he.unit
  rw [show action A u = fun y => Ring.inverse (F y) from funext fun y => Matrix.nonsing_inv_eq_ringInverse (F y)]; exact hp.comp x hh

lemma action_rule {u : ℝ} (l : List τ) (hl : l ≠ []) (h : Neat A u x) (hw : ContDiffAt ℝ l.length A x) :
    jet v (action A u) l x = - (resolve (A x) u * ∑ m ∈ Finset.univ.erase (pureR l),
      jet v A (lo l m) x * jet v (action A u) (hi l m) x) := by
  let G := fun z => A z + u • 1
  have hg : ContDiffAt ℝ l.length G x := hw.add contDiffAt_const
  let T := action A u
  let H (m : Masks l) := jet v G (lo l m) x * jet v T (hi l m) x
  have he : (fun z => G z*T z) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [germ_valid h hw.continuousAt] with y hy
    exact Matrix.mul_nonsing_inv (G y) hy
  have hx : ∑ m, H m = 0 := (jet_mul v l hg (action_smooth h hw)).symm.trans ((identical v he l).trans
    (jet_const v l hl _ _))
  have hh := Finset.add_sum_erase (s:=Finset.univ) H (Finset.mem_univ (pureR l))
  rw [hx] at hh
  have hc (m) (hm : m ∈ Finset.univ.erase (pureR l)) : jet v A (lo l m) x = jet v G (lo l m) x := by
    have hi := smooth_of_le hw (len_low l m)
    unfold G; rw [jet_add v _ hi contDiffAt_const, jet_const v _ (lo_ne (Finset.ne_of_mem_erase hm)), add_zero]
  have ht : G x * jet v T l x = - ∑ m ∈ Finset.univ.erase (pureR l), jet v A (lo l m) x * jet v T (hi l m) x := by
    rw [show ∑ m ∈ Finset.univ.erase (pureR l), _ = ∑ m ∈ Finset.univ.erase (pureR l), H m from
      Finset.sum_congr rfl (fun m hm => congrArg (· * jet v T (hi l m) x) (hc m hm))]
    simpa only [H, lo_right,hi_right,zeroth] using (eq_neg_of_add_eq_zero_left hh)
  have hp : resolve (A x) u * G x = 1 := Matrix.nonsing_inv_mul _ h
  rw [← Matrix.mul_neg, ← ht, ← Matrix.mul_assoc, hp, Matrix.one_mul]
end TestD

/-- One convenient jet norm for generic product estimates. -/
structure Bundle {τ X E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype κ]
    (v : τ → E) (C : Mark τ X) (D : Cost X) (a : ι → X) (b : κ → X) (A : E → Matrix ι κ ℝ) (x : E) (k : ℕ) (s M : ℝ) : Prop where
  smooth : ContDiffAt ℝ k A x
  bound (l : List τ) : l.length ≤ k → Bill C D a b l s M (jet v A l x)

section bundle
variable [Fintype κ] {A B : E → Matrix ι κ ℝ} {a : ι → X} {b : κ → X}
variable {C : Mark τ X} {D : Cost X} {v : τ → E} {γ s t d U M N : ℝ} {x : E} {k : ℕ}
omit [DecidableEq ι] in
lemma Bundle.mono (H : Bundle v C D a b A x k s M) (hs : t ≤ s) (hm : M ≤ N) : Bundle v C D a b A x k t N :=
  ⟨H.smooth,fun l h => (H.bound l h).mono hs hm⟩
omit [DecidableEq ι] in
lemma Bundle.glue (H : Bundle v C D a b A x k s M) (he : A =ᶠ[𝓝 x] B) : Bundle v C D a b B x k s M :=
  ⟨H.smooth.congr_of_eventuallyEq he.symm,fun l h => by rw [← identical v he l]; exact H.bound l h⟩
def tagPrice (U : ℝ) (k : ℕ) (M N : ℝ) := 2^k*(U^k*M*N)
omit [DecidableEq ι] in
theorem Bundle.multiply [Fintype μ] {c : μ → X} {B : E → Matrix κ μ ℝ}
    (H : Bundle v C D a b A x k s M) (J : Bundle v C D b c B x k s N)
    (hu : C.Move D d U) (hn : 0 ≤ d) (hx : 1 ≤ U) (hm : 0 ≤ M) (hj : 0 ≤ N) (hg : 0 ≤ γ) (hy : γ+k*d ≤ s) :
    Bundle v C D a c (fun x => A x*B x) x k γ (tagPrice U k M N) := by
  constructor
  · exact prod_smooth H.smooth J.smooth
  intro l hl; rw [jet_mul v _ (smooth_of_le H.smooth hl) (smooth_of_le J.smooth hl)]
  let Q := U^k*M*N
  apply (Bill.sum_budget Finset.univ (fun _ => Q) _ fun m _ => Bill.mul hu hn hx hg k hy
    ((len_low l m).trans hl) ((len_high l m).trans hl) (fun x => pay_masks ..) hm hj (H.bound (lo l m) ((len_low l m).trans hl))
    (J.bound (hi l m) ((len_high l m).trans hl))).mono le_rfl
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,TestD.card,Nat.cast_pow, Nat.cast_ofNat,tagPrice]
  have ht : 0 ≤ U := zero_le_one.trans hx
  apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (show 0 ≤ Q from by unfold Q; positivity)
end bundle

namespace TestD
variable {C : Mark τ X} {D : Cost X} {A : E → Matrix ι ι ℝ} {v : τ → E} {a : ι → X}
variable {k : ℕ} {s M r d U γ η ε V u : ℝ} {x : E}

def charges (n : ℕ) (ε C w : ℝ) := if n=0 then C*w else C*w*w*ε

lemma charges_nn (n : ℕ) {ε C w : ℝ} (he : 0 ≤ ε) (hc : 0 ≤ C) (hw : 0 ≤ w) : 0 ≤ charges n ε C w := by
  unfold charges; split <;> positivity
lemma charges_mono (n : ℕ) {ε C W w : ℝ} (he : 0 ≤ ε) (hc : C ≤ W) (hw : 0 ≤ w) : charges n ε C w ≤ charges n ε W w := by
  unfold charges; split <;> gcongr
lemma charges_lax (n : ℕ) {ε C w : ℝ} (hε : ε ≤ 1) (hw : 0 ≤ w) (hh : w ≤ 1) (hc : 0 ≤ C) : charges n ε C w ≤ C*w := by
  unfold charges; split; · rfl
  exact (mul_le_of_le_one_right (by positivity) hε).trans (mul_le_of_le_one_right (by positivity) hh)

/-- harmless exponential in the derivative budget, independent of |period|. -/
def meter (k n : ℕ) (M U Q : ℝ) := Q * (1+U^k*Q*(2^k*(U^k*M)))^n
lemma meter_nn (k n : ℕ) {M U Q : ℝ} (hm : 0 ≤ M) (hu : 0 ≤ U) (hq : 0 ≤ Q) : 0 ≤ meter k n M U Q := by
  unfold meter; positivity

def drain (u : ℝ) := (1+u)⁻¹
lemma drain_pos (h : 0 ≤ u) : 0 < drain u := inv_pos.mpr (by linarith)
lemma drain_le (h : 0 ≤ u) : drain u ≤ 1 := inv_le_one_of_one_le₀ (by linarith)

def rise (V r : ℝ) := V*(min (r/2) 1)⁻¹
lemma rise_nn (hV : 0 ≤ V) (hr : 0 < r) : 0 ≤ rise V r :=
  mul_nonneg hV (inv_pos.mpr (lt_min (half_pos hr) zero_lt_one)).le

/-- `progress s` remaining paid rate after n derivatives budget. -/
def progress (s : ℝ) (d : ℝ) (k n : ℕ) := s-2*n*(k*d)
lemma progress_top (s : ℝ) (d : ℝ) (k : ℕ) : progress s d k 0=s := by simp [progress]
lemma progress_anti (s : ℝ) (hd : 0 ≤ d) (k : ℕ) : Antitone (progress s d k) := by
  intro i j hi; unfold progress; gcongr
lemma progress_next (s : ℝ) (d : ℝ) (k n : ℕ) : progress s d k (n+1) = progress s d k n - 2*(k*d) := by unfold progress; push_cast; ring

/-- Precision inputs, `ε` scales *positive derivatives only*. Nothing
about the derivative of any inverse matrix. -/
structure Knew (C : Mark τ X) (D : Cost X) (a : ι → X) (v : τ → E) (x : E) (k : ℕ) (s M r ε : ℝ)
    (A : E → Matrix ι ι ℝ) : Prop where
  smooth : ContDiffAt ℝ k A x
  gap : Gap (A x) r
  schur : D.Schur a a s M (A x)
  jets (l : List τ) : l ≠ [] → l.length ≤ k → Bill C D a a l s (M*ε) (jet v A l x)

lemma measured (hg : progress γ d k k ≥ 0) (h : C.Move D d U) (hd : 0 ≤ d) (hh : 1 ≤ U)
    (hw : Knew C D a v x k s M r ε A) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hs : 0 < s) (hx : D.Volume a (safeRate s M r-γ) V) (hc : γ ≤ s)
    (hu : 0 ≤ u) (hr : 0 < r) (hε : 0 ≤ ε) (he : ε ≤ 1) :
    ∀ n : ℕ, n ≤ k → ∀ l : List τ, l.length ≤ n → Bill C D a a l (progress γ d k n)
      (charges l.length ε (meter k n M U (rise V r)) (drain u)) (jet v (action A u) l x) := by
  intro n; let Y := action A u; let Q := rise V r; let w := drain u
  have hq : 0 ≤ Q := rise_nn hV hr
  have hy := resolve_schur hM hs hw.schur hw.gap hr hu hx
  have hk : Neat A u x := ((hw.gap.shift u).unit_det (by positivity))
  have hU := zero_le_one.trans hh
  have h0 : Bill C D a a [] γ (Q*w) (resolve (A x) u) := Bill.origin C (hy.mono le_rfl (by
    unfold w drain Q rise; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (uniform_shift _ _ hr hu) hV))
  have hv n : Q ≤ meter k n M U Q := by unfold meter; exact le_mul_of_one_le_right hq (one_le_pow₀
    (le_add_of_nonneg_right (by positivity)))
  have hz n : progress γ d k n ≤ γ := (progress_anti γ hd k (Nat.zero_le n)).trans_eq (progress_top ..)
  have hn := drain_pos hu |>.le
  induction n with
  | zero =>
    intro ht l hl; rw [Nat.le_zero, List.length_eq_zero_iff] at hl; subst l
    simp only [progress_top, List.length_nil, charges, if_true, meter, pow_zero, mul_one, zeroth]; exact h0
  | succ n ih =>
    intro ht l hl
    by_cases hL : l=[]
    · subst l; rw [TestD.zeroth]; exact h0.mono (hz _) (show Q*w ≤ meter k (n+1) M U Q*w from mul_le_mul_of_nonneg_right (hv _) hn)
    have hA := smooth_of_le hw.smooth (hl.trans ht)
    rw [action_rule v _ hL hk hA]
    let S := progress γ d k (n+1)
    let R := S+k*d
    have hS : 0 ≤ S := le_trans hg (progress_anti γ hd k ht)
    have hR : 0 ≤ R := add_nonneg hS (by positivity)
    have hb : R+k*d ≤ progress γ d k n := by unfold R S; rw [progress_next]; linarith
    have ho : R ≤ γ := (le_trans (le_add_of_nonneg_right (by positivity)) hb).trans (hz n)
    let A0 := meter k n M U Q
    let D0 := U^k*(M*ε)*(A0*w)
    have hD : 0 ≤ D0 := by unfold D0; have he : 0 ≤ A0 := meter_nn _ _ hM hU hq; positivity
    let G := Finset.univ.erase (pureR l)
    have hG (m : Masks l) (hm : m ∈ G) : Bill C D a a l R D0 (jet v A (lo l m) x * jet v Y (hi l m) x) := by
      have h' : lo l m ≠ [] := lo_ne (Finset.ne_of_mem_erase hm)
      have h1 := (len_low l m).trans (hl.trans ht)
      have h2 : (hi l m).length ≤ n := by
        have he : 1 ≤ (lo l m).length := List.length_pos_iff.mpr h'
        have hx := lengths l m; omega
      have hm : 0 ≤ A0 := meter_nn _ _ hM hU hq
      exact Bill.mul h hd hh hR k hb h1 (h2.trans (n.le_succ.trans ht)) (C.pay_masks l m) (mul_nonneg hM hε)
        (mul_nonneg hm hn) ((hw.jets _ h' h1).mono ((hz n).trans hc) le_rfl)
        ((ih (n.le_succ.trans ht) (hi l m) h2).mono le_rfl (charges_lax _ he hn (drain_le hu) hm))
    have hr' : (∑ _m ∈ G, D0) ≤ 2^k*D0 := by
      rw [Finset.sum_const,nsmul_eq_mul]
      have he : G.card ≤ 2^l.length := by rw [← card]; exact Finset.card_le_univ _
      have hh : (G.card:ℝ) ≤ 2^l.length := by exact_mod_cast he
      refine mul_le_mul_of_nonneg_right (hh.trans (pow_le_pow_right₀ (by norm_num) (hl.trans ht))) hD
    have hB := (Bill.sum_budget _ _ _ hG).mono le_rfl hr'
    have hZ := (h0.mono ho le_rfl).mul h hd hh hS k (show S+k*d ≤ R from le_rfl) (Nat.zero_le _) (hl.trans ht)
      (fun x => show C.pay l x=C.pay [] x*C.pay l x from (one_mul _).symm) (mul_nonneg hq hn) (mul_nonneg (by positivity) hD) hB
    apply hZ.neg.mono le_rfl
    rw [charges,if_neg (ne_of_gt (List.length_pos_iff.mpr hL))]
    change U^k*(Q*w)*(2^k*D0) ≤ meter k (n+1) M U Q*w*w*ε
    have hf : 0 ≤ A0 := meter_nn _ _ hM hU hq
    calc
      _ = A0*(U^k*Q*(2^k*(U^k*M)))*w*w*ε := by unfold D0; ring
      _ ≤ _ := by
        rw [show meter k (n+1) M U Q = A0*(1+U^k*Q*(2^k*(U^k*M))) by unfold A0 meter; rw [pow_succ]; ring]
        apply mul_le_mul_of_nonneg_right _ hε
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left zero_le_one) hf) hn) hn
end TestD
end YM.FreeResolvent
