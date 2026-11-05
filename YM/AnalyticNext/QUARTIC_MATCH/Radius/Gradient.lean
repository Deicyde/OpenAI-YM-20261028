import YM.AnalyticNext.QUARTIC_MATCH.Local.Limits
import YM.AnalyticNext.QUARTIC_MATCH.Local.Members
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Polish


/-!
# Due at the path's roots

All inside a real sup neighborhood; still no claim clipping prices. Weighted
external tests allow exponential growth with distance. Output use then in
compositions on the real graph. All costs independent of period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free
open Estimate Estimate.Purse Estimate.Village Estimate.Logfee Estimate.Plaque Joint Local Local.Wages  Local.Rotate
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Fetch
open Polish
open Green (wt)


variable {α K : Type*} {G : Gauge} {n l c f : Side}
def Amount {X : Type*} [NormedAddCommGroup X] (η : ℝ) (s : α → Site n) (i : Site n) : Ticket (α→X) :=
    fun x a => ∀ t, ‖x t‖ ≤ a*wt η (s t) i
section
variable {X : Type*} [NormedAddCommGroup X] {t s C D : ℝ} {ι : α→Site n} {i : Site n} {x : α → X}
lemma seek (he : t≤s) (hC : 0 ≤ C) (h : Amount t ι i x C) : Amount s ι i x C := fun u =>
    (h u).trans (mul_le_mul_of_nonneg_left (Wages.wt_le he ..) hC)
lemma Amount.elevate (h : Amount t ι i x C) (he : C≤D) : Amount t ι i x D := fun u =>
    (h u).trans (mul_le_mul_of_nonneg_right he (Green.wt_pos ..).le)
lemma Amount.origin (h : Amount t ι i x C) (j : Site n) (he : 0 ≤ t) (hC : 0 ≤ C) : Amount t ι j x (C*wt t j i) := fun u => by
    apply (h u).trans; rw [mul_assoc,mul_comm (wt t j i)]
    exact mul_le_mul_of_nonneg_left (Green.wt_triangle he ..) hC
lemma zeroed (t : ℝ) (i : Site n) (s : α → Site n) (X : Type*) [NormedAddCommGroup X] (he : 0 ≤ C) :
    Amount t s i (0 : α→X) C := fun j => by simp only [Pi.zero_apply,norm_zero]; exact mul_nonneg he (Green.wt_pos ..).le
lemma Amount.constant [Fintype α] (t : ℝ) (he : 0 ≤ t) (i : Site n) (x : α→X) : Amount t ι i x ‖x‖ :=
  fun _ => (norm_le_pi_norm ..).trans (le_mul_of_one_le_right (norm_nonneg _) (Wages.wt_ge he ..))
end

abbrev trials (G : Gauge) {n : Side} (η : ℝ) (x : Site n) : Ticket (Dir G n) := Amount η Prod.fst x
lemma shift_le (q : Signed) (x : Dir G n) : ‖shifts q 0 x‖≤‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; rintro ⟨i,j⟩; obtain ⟨k,rfl⟩ := axisEquiv.surjective j
  change ‖shifts q 0 x (i,coord k)‖ ≤ _; rw [Rotate.read_norm q k i x]; exact norm_le_pi_norm ..

variable {ι : Type*} [DecidableEq ι] (G : Gauge) (σ R : ℝ) (p : Clip)
def billage (m : ℕ) :=
    let t := down σ m; let v := baseCash G m t p.direct R; let u := gift G t m
    let f := 2^m*gratuity G t m
    Fintype.card PlaqAxes * (v*u^2) + f^ (3:ℕ)*R+ f^ (4:ℕ)*R

def dues (m : ℕ) := Real.exp (2*down σ m)^m*billage G σ R p m

variable {G σ R p} {Λ : ℝ} {W : PathData G} (h : W.Bounds p σ R Λ) {m : ℕ}
include h

private lemma station {d : ι→Dir G n} (x : Dir G n) (hp : ‖x‖<1) (S : Finset ι) (hm : S.card ≤ m)
    (P : Estimate.Purse ι (Site n)) (hh : Linkbill 1 P d) (he : tollRate P 1 (down σ m)) : P.Jets S d
      (Rotate.total p W) x (billage G σ R p m) := by
  let t := down σ m; let v := baseCash G m t p.direct R; let u := gift G t m; let a := 2^m*gratuity G t m
  have ht : 0<t := Estimate.down_pos m h.width
  have hq : 5*m*t ≤ σ*((1:Side).val:ℝ) := by simpa only [t,PNat.val_ofNat,Nat.cast_one,mul_one] using uses_down m h.width
  have he' (B) (T) (h' : T⊆S) := post_pop hh he ht.le T _ ((Finset.card_le_card h').trans hm) x hp.le B
  have hu : 0≤u := (gift_pos ..).le
  have hv B : P.Jets S d (expense p W B) x (v*u^2) := base_card h hh he ht x hp S m hm hq u he' B hu h.width (h.rows B)
  have hx (r : ℕ) (A : ℕ→Atom G r) (h' : Rotate.Ink A σ R) : P.Jets S d (Estimate.atend A) x (a^r*R) :=
    atom_budget A hh he ht x hp S m hm hq u he' hu h.width h'
  have hw := Jets.allotted Finset.univ (expense p W (n:=n)) (fun i _ j => expense_rate h i j _) (fun i _ => hv i)
  let f i (x : Dir G n) := ∑ j : PlaqAxes, expense p W j i x
  have hb' (i) : ContDiffAt ℝ ω (f i) x := ContDiffAt.sum fun j _ => expense_rate h j i x
  have h3 (i : Site n) := atend_rate _ h.width h.three i x
  apply (Jets.adding (fun i => (hb' i).add (h3 i)) (fun i => atend_rate _ h.width h.four i x) (Jets.adding hb' h3 hw (hx 3 W.cubic h.three)) (hx 4 W.quartic h.four)).mono
  rw [Finset.sum_const,nsmul_eq_mul, Finset.card_univ]; exact le_rfl

omit h in
lemma lin_rate_at {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Y→E) (Z : X →L[ℝ] Y) (x : X) (hf : ContDiffAt ℝ ω F (Z x)) (n : ℕ) (d : Fin n→X) : iteratedFDeriv ℝ n (F ∘ Z) x d=iteratedFDeriv ℝ n F (Z x) (fun i=> Z (d i)) := by
  let f y := F (Z x + y)
  have ht : iteratedFDeriv ℝ n f 0=iteratedFDeriv ℝ n F (Z x) := by unfold f; rw [iteratedFDeriv_comp_add_left,add_zero]
  have hu : iteratedFDeriv ℝ n (f ∘ Z) 0=iteratedFDeriv ℝ n (F ∘ Z) x := by
    rw [show f ∘ Z=(fun y => (F ∘ Z) (x+y)) from funext fun i => by simp [f], iteratedFDeriv_comp_add_left,add_zero]
  have he : ContDiffAt ℝ n f 0 := hf.of_le (show (n:WithTop ℕ∞)≤ω from le_top) |>.comp_of_eq (g:=F) (f:=fun y=>Z x+y) 0 (contDiffAt_const.add contDiffAt_id) (fun _ _=> Set.mem_univ _) (add_zero _)
  rw [← hu, ← ht, Next.Foundations.jets_linear Z he]; rfl

lemma first (k : ℕ) (hm : k ≤ m) (x : Dir G n) (hp : ‖x‖<1) (z : Site n) :
    Costs (trials G (down σ m) z) (budget ℝ) (byStage p W z) x k (dues G σ R p m) := by
  intro d c hc; let t := down σ m; let P : Purse (Fin k) (Site n) := Local.Wages.account 1 none (fun _=>z) (fun _=> -t) c (fun i => (hc i).1)
  let u (i : Fin k) (p : Site n) : ℝ := P.toll i p
  have ht : 0<t := down_pos m h.width
  have hu i y : u i y=(wt t y z)⁻¹ := by simp [u,P,Wages.account, Green.wt, Real.exp_neg]
  have hf : tollRate P 1 t := Wages.travels _ _ _ _ _ _ (fun _ => by rw [abs_neg,abs_of_nonneg ht.le])
  have he : Linkbill 1 P d := by
    intro i j; refine ⟨by positivity,fun _ y => ?_,fun he => ?_⟩
    · rw [Purse.price, Finset.prod_singleton,Purse.target, Finset.prod_singleton]
      rw [show P.toll i y=_ from hu i y,inv_mul_eq_div]; simp only [PNat.val_ofNat,Nat.cast_one,inv_one, one_mul]
      exact (div_le_iff₀ (Green.wt_pos ..)).mpr ((hc i).2 (y,j))
    simp [P, Wages.account, Purse.tagged] at he
  let f s (x : Site n) (a : Dir G n) := total p W (s⁻¹.act x) (shifts s 0 a)
  let a := dues G σ R p m; let S : Finset (Fin k) := Finset.univ
  have hM : S.card≤m := by simpa [S] using hm
  have hb (s : Signed) : P.Jets S d (f s) x a := by
    have hv := station h (shifts s 0 x) (lt_of_le_of_lt (shift_le s x) hp) _ hM _ (bonds s hf ht.le he) (stays s hf)
    refine ((Rotate.restores s hv).mono (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Real.one_le_exp (by positivity)) hM) hv.1)).under fun i => ?_
    have ht : bill S d (f s i) x=bill S (shifts s 0 ∘ d) (Rotate.total p W (s⁻¹.act i)) (shifts s 0 x) := by
      unfold bill; rw [show f s i=_ from (show f s i=Rotate.total p W (s⁻¹.act i) ∘ shifts s 0 from rfl)]
      exact lin_rate_at _ _ _ (total_rate h (s⁻¹.act i) _) _ _
    exact (congr_arg (‖·‖) ht).le
  let w (i : Site n) z := ∑ s : Signed, f s i z
  have hh (s i) : ContDiffAt ℝ ω (f s i) x := (total_rate h (s⁻¹.act i) (shifts s 0 x)).comp x (shifts s (0:Site n)).contDiff.contDiffAt
  have hw i : ContDiffAt ℝ ω (w i) x := ContDiffAt.sum fun s _ => hh s i
  unfold Polish.budget
  rw [← Estimate.univEstimate _ _ _ (stage_rate h z _)]
  have hv : P.Jets S d (byStage p W) x a := by
    apply (Jets.rate (Jets.allotted Finset.univ f (fun s _ i => hh s i) (fun s _ => hb s)) _ hw).mono
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; exact le_of_eq (by rw [abs_of_nonneg (by positivity)]; field_simp)
  have hU := hv.2.1 (show ¬P.tagged S from by simp [P,Purse.tagged,Wages.account]) z
  rw [show P.price S z=1 by simp [Purse.price,P,Wages.account,Green.wt],one_mul] at hU
  exact hU
end Fetch
end YM.AnalyticNext.QuarticMatch.Radius
