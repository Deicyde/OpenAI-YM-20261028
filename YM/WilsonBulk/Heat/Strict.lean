import YM.WilsonBulk.Heat.Paid
import YM.WilsonBulk.Cost.Bower

/-!
# Polynomial strict-event tariff for the conditional Wick step

Input leg tables in coupling powers, width σ strictly interior mesh-generic
native norm. `Intake` assumes ONLY preceding-rank or lower-grade costs; no
assumed bounds for the same component. `strict_heat` controls COVER overlap
jets after subtracting the time-zero transmission. Every positive-time term
at that grade obeys. Pay polynomial in fixed schedule caps. Width charged on
both value and cutoff variation, with an explicit stage-prescribable ratio.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Equiv Finset Filter Pert.Bulk
variable {X : Type} {σ θ p δ ε : ℝ} {G : Rule X} {e n k : ℕ}
/-- common tariff (can use δ=1 for single-history use) -/
def tariff : ℕ→ℕ→ℕ→ℝ→ℝ
| 0,_,_,p => p
| t+1,e,n,p => ((t+1:ℕ):ℝ)⁻¹*(dab n*(2*(tariff t e (n+2) p*p))+∑ i : Split e,∑ j : Split t,∑ k: Split n, brush (l k) (r k) * (2*(2*(tariff (l j) (l i) (l k+1) p*p)*tariff (r j) (r i) (r k+1) p)))
termination_by t _ _ _ => t
decreasing_by all_goals first| exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (left_small _) | exact Nat.lt_succ_of_le (right_small _)
lemma tariffed (d e n : ℕ) : Tariff (tariff d e n) := by
  induction d using Nat.strong_induction_on generalizing n e with
  | h t ih=>
     cases t with
     | zero => convert Tariff.one using 1; ext x; rw [tariff]
     | succ t =>
        have ht : ∀ i : Split e,∀ j : Split t,∀ k : Split n, Tariff fun p=> brush (l k) (r k) * (2*(2*(tariff (l j) (l i) (l k+1) p*p)*tariff (r j) (r i) (r k+1) p)) := fun i j k=>
            (Tariff.const _ (brush_pos ..).le).prod ((Tariff.const 2 (by norm_num)).prod (((Tariff.const _ (by norm_num)).prod ((ih (l j) (by have H:=left_small j; omega) _ _).prod Tariff.one)).prod (ih (r j) (by have he:= right_small j; omega) _ _)))
        refine Eq.mp (congr_arg Tariff ?_) ((Tariff.const ((t+1:ℕ):ℝ)⁻¹ (by positivity)).prod (((Tariff.const _ (dab_pos n).le).prod ((Tariff.const 2 (by norm_num)).prod ((ih t (by omega) (n:=n+2) (e:=e)).prod Tariff.one))).add (Tariff.gather univ fun i _=>Tariff.gather univ fun j _=>Tariff.gather univ fun k _=> ht i j k)))
        ext1 p; rw [tariff]

def thinness (σ : ℝ) (W : ℝ) : ℕ→ℝ
  | 0 => σ
  | t+1 => (thinness σ W t / W) / W
@[simp] lemma heater_width (σ W : ℝ) : thinness σ W 0=σ := rfl
lemma width_debt (σ W : ℝ) (i : ℕ) : thinness σ W i = σ/(W^2)^i := by
  induction i with
  | zero => simp
  | succ i ih=>
     rw [thinness,ih,pow_succ,div_div,div_div]; ring
lemma thin_nonneg (he : 0≤σ) (W : ℝ) (i : ℕ) : 0 ≤ thinness σ W i := by rw [width_debt]; positivity
lemma thin_pos (he : 0<σ) {W : ℝ} (hp : 0<W) (i : ℕ) : 0<thinness σ W i := by rw [width_debt]; positivity
lemma cooling (he : 0≤σ) {W : ℝ} (hp : 2≤W) : Antitone (thinness σ W) := antitone_nat_of_succ_le fun i=>
    (div_le_self (div_nonneg (thin_nonneg he _ _) (show 0≤W by linarith)) (show 1≤W by linarith)).trans (div_le_self (thin_nonneg he ..) (show 1≤W by linarith))
def Intake (G : Rule X) (σ δ p : ℝ) (I J : Record X) (e n : ℕ) := ∀ i≤ e,∀ k>0,k ≤ i+2→ (i=e → n<k) →
  Options G σ δ p (I i k) (J i k)
lemma Intake.crop {I J : Record X} (h : Intake G σ δ p I J e n) (i : ℕ) (he : i < e) (r : ℕ) : Intake G σ δ p I J i r := fun k hk x hx hh _=> h k (hk.trans he.le) x hx hh (by omega)

variable {I J : Record X} {A B : Page X 2} {t e n i k : ℕ}
/-- reach predicate for paying through a step. -/
lemma measure_heat (h : Intake G σ δ p I J e n)
    (ha : Options G σ δ p A B) (he : 0≤σ) (hf : Free I) (hf' : Free J)
    (hr : FrameBound I) (hr' : FrameBound J) (W : ℝ) (hw : (e:ℝ)+4 ≤ W) (hi : i ≤ e) (hg : i=e → n≤k)
    (htt : i=e → k=n → t ≠ 0) :
    Options G (thinness σ W t) δ (tariff t i k p) (immerse A I true t i k) (immerse B J true t i k) := by
  induction t using Nat.strong_induction_on generalizing i k with
  | h t ih=>
     have H(t i k : ℕ) := (tariffed t i k).1 p ha.baseline
     have hh := ha.nonneg
     have hW : 2≤ W:= by linarith only [hw,Nat.cast_nonneg (α:=ℝ) e]
     by_cases hk : k=0
     · subst hk; rw [cashless_at,cashless_at]; exact Options.zero (H ..) hh
     by_cases hn : k ≤ i+2; swap
     · rw [immerse_bounded _ true hr t i k (by omega), immerse_bounded _ true hr' t i k (by omega)]; exact Options.zero (H ..) hh
     cases t with
     | zero => rw [tariff,start,start]; simp only [heater_width,hk,false_and,↓reduceIte]; exact h i hi k (by omega) hn (by omega)
     | succ t =>
        have hp := thin_nonneg he W t
        let y := thinness σ W (t+1)
        have hA : Options G (thinness σ W t) δ p A B := ha.more le_rfl le_rfl (by simpa using cooling he hW (t.zero_le))
        have hor v (hv:v<t+1) (i k) (hi': i ≤ e) (hg : i=e→ n<k) : Options G (thinness σ W t) δ (tariff v i k p) (immerse A I true v i k) (immerse B J true v i k) :=
          (ih v hv hi' (by omega) (by omega)).more le_rfl le_rfl (cooling he hW (Nat.le_of_lt_succ hv))
        have hx : Options G y δ (dab k*(2*(tariff t i (k+2) p*p))) (lap A (immerse A I true t i (k+2))) (lap B (immerse B J true t i (k+2))) :=
            (hA.lap (hor _ (by omega) _ _ hi (by omega)) hp hp hk).more le_rfl le_rfl (cooling he hW (show t≤t+1 by omega))
        let f (a:Split i) (b:Split t) (c:Split k) := brush (l c) (r c)*(2*(2*(tariff (l b) (l a) (l c+1) p*p)*tariff (r b) (r a) (r c+1) p))
        have hy (a: Split i) (b: Split t) (c: Split k) : Options G y δ (f a b c)
            (torpedo A (immerse A I true) t i k a b c) (torpedo B (immerse B J true) t i k a b c) := by
          have hl := parts a; have hl' := parts b; have hk' := parts c
          have H' : 0 ≤ f a b c := by dsimp only [f]; exact mul_nonneg (brush_pos ..).le (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (H ..) (ha.baseline))) (H ..)))
          rcases Nat.eq_zero_or_pos (l a) with hz|hl₁; · rw [torpedo_zero _ a b c (Or.inl (hz.symm ▸ immerse_free _ true hf (l b) (l c+1))), torpedo_zero _ a b c (Or.inl (hz.symm ▸ immerse_free _ true hf' (l b) (l c+1)))]; exact Options.zero H' hh
          rcases Nat.eq_zero_or_pos (r a) with hz|hl₂; · rw [torpedo_zero _ a b c (Or.inr (hz.symm ▸ immerse_free _ true hf (r b) (r c+1))), torpedo_zero _ a b c (Or.inr (hz.symm ▸ immerse_free _ true hf' (r b) (r c+1)))]; exact Options.zero H' hh
          have coin (x : ℕ) (hv:x≤k) : (x:ℝ)+1 ≤ W:= by
            refine le_trans ?_ hw; exact_mod_cast (show x+1≤e+4 by omega)
          exact (hA.bridge (hor (l b) (by omega) (l a) (l c+1) (by omega) (by omega)) (hor (r b) (by omega) (r a) (r c+1) (by omega) (by omega)) hp hW (coin (l c) (by omega)) (coin (r c) (by omega)) (by omega)).reindex _
        have he := (hx.add (Options.gather univ (fun a _=> Options.gather univ (fun b _=> Options.gather univ (fun c _=> hy a b c) hh) hh) hh)).scale (((t+1:ℕ):ℝ)⁻¹)
        rw [abs_of_pos (by positivity : 0< ((t+1:ℕ):ℝ)⁻¹)] at he
        rw [restore,restore,tariff]; simp only [hk,false_and,↓reduceIte]; exact he

def reheating (t : ℕ) := (spend t).erase 0
def recovery (e n : ℕ) (p : ℝ) := ∑ j∈reheating e, tariff j e n p
def saveWidth (e : ℕ) (σ : ℝ) : ℝ := thinness σ (e+4) (3*e)
lemma save_pos (h : 0<σ) (e : ℕ) : 0 < saveWidth e σ := thin_pos h (by positivity) _
lemma save_le (h : 0≤σ) (e : ℕ) : saveWidth e σ ≤ σ := cooling h (show (2:ℝ)≤(e:ℝ)+4 by linarith [Nat.cast_nonneg (α:=ℝ) e]) (show 0≤3*e from Nat.zero_le (3*e))
lemma tariff_recovery (e n) : Tariff (recovery e n) := Tariff.gather _ fun _ _=>tariffed ..
lemma receive_minus (i : ℕ) (hv : n ≠ 0) : receive A I true i n-I i n=∑ j∈reheating i, immerse A I true j i n := by
  have hi : 0 ∈ spend i:= by simp [spend]
  have he := (sum_erase_add (spend i) (fun j=> immerse A I true j i n) hi).symm; rw [start] at he;unfold receive; rw [he]; simp only [hv,false_and,↓reduceIte, add_sub_cancel_right,reheating]

lemma strict_heat (h : Intake G σ δ p I J e n)
    (ha : Options G σ δ p A B) (he : 0≤σ) (hf : Free I) (hf' : Free J)
    (hr : FrameBound I) (hr' : FrameBound J) (hn : n ≠ 0) :
    Options G (saveWidth e σ) δ (recovery e n p) (receive A I true e n-I e n) (receive B J true e n-J e n) := by
  rw [receive_minus _ hn, receive_minus _ hn]; unfold recovery
  refine Options.gather _ (fun i hi=>?_) ha.nonneg
  obtain ⟨H,H'⟩:=mem_erase.mp hi
  refine (measure_heat h ha he hf hf' hr hr' _ le_rfl le_rfl (fun _=>le_rfl) (fun _ _=> H)).more le_rfl le_rfl (cooling he (show (2:ℝ) ≤ (e:ℝ)+4 by linarith [Nat.cast_nonneg (α:=ℝ) e]) ?_)
  exact Nat.le_of_lt_succ (mem_range.mp H')
end Sheet
end YM.WilsonBulk
