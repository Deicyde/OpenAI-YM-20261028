import YM.FullVolume.Ray.Glimpse
/-! Univariate exponent price including far real nodes.
 We normalize sqrtβ-value. Departure may have either sign. Scaling convention all≥1;
    saving used through **actual number of seeds**, not total torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations Finset
open scoped Topology BigOperators NNReal ContDiff
variable {R δ c b:ℝ} {k i n:ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
-- maximum displacement over ±6 R for square-root band. Fixed deadline post-L.
structure Fold (R δ:ℝ) where
  peak : ℝ
  slope : ℝ
  price : 1≤R
  funds : 1≤ peak-6*R*|slope|
  covers : peak+6*R*|slope| ≤1+δ
  active : δ≤1
namespace Fold
variable (h:Fold R δ)
def flow (s:ℝ):= h.peak+h.slope*s
lemma full : 0<R∧1 ≤ h.peak∧0≤δ:= by
  have hp:= h.funds; have hf:= h.covers; have ht:=zero_lt_one.trans_le h.price
  have hz : 0 ≤ (6:ℝ)*R*|h.slope| := by positivity
  exact ⟨ht,by linarith,by linarith⟩
lemma moves (x:ℝ) (hx:|x|≤6*R): 1 ≤ h.flow x ∧ h.flow x ≤ 1+δ:=by
  unfold flow; have hh:= abs_le.mp (show |h.slope*x|≤ 6*R*|h.slope| from (by rw [abs_mul,mul_comm (6*R)]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
  constructor
  · linarith [h.funds,hh.1]
  linarith [h.covers,hh.2]
def sqcost (x:ℝ):=1-h.flow x^2
lemma printed: ink 2 h.sqcost:= by
  have ht:= (ink.termC 1).abreast (((ink.straight h.peak h.slope).docket (ink.straight h.peak h.slope)).scale (-1))
  refine Eq.mp (congr_arg (ink 2) ?_) ht; funext u; unfold sqcost flow; ring
-- exponential with at fixed q of either sign. Cost <= exp(q*(1 - peak²) + |q| (...) ) exact. Scout for flow^ν.
lemma pulse : Scout R h.flow (1+δ):=by
  have hp:= h.covers; unfold flow
  have hq:= (Scout.still h.price h.peak).pair ((Scout.line h.price).scale h.slope)
  apply hq.enlarged; rw [Real.norm_of_nonneg (zero_le_one.trans h.full.2.1),Real.norm_eq_abs]
  apply le_trans _ hp; nlinarith [h.full.1, abs_nonneg h.slope]
def scaleT (q:ℝ):= (h.sqcost 0)*q+|(2*h.peak*h.slope)*q| *R+h.slope^2*|q| *R^2
lemma unveils (q:ℝ): Scout R (fun s=> Real.exp (h.sqcost s*q)) (Real.exp (h.scaleT q)):=by
  let a:= h.peak; let d:= h.slope; let v:= (1-a^2)*q; let w₁:=-(2*a*d)*q; let w₂:=-(d^2)*q
  let t(s:ℝ):=w₁*s+w₂*s^2; have he:= Scout.line h.price
  have hp:= (he.scale w₁).pair ((he.power 2).scale w₂)
  have ht: Scout R t (‖w₁‖*R+‖w₂‖*R^2):=hp
  have hz:h.scaleT q=v+(‖w₁‖*R+‖w₂‖*R^2):= by
    unfold scaleT sqcost flow v w₁ w₂; simp only [neg_mul, Real.norm_eq_abs,abs_neg,abs_mul, mul_zero,add_zero]; unfold a d; rw [abs_of_nonneg (sq_nonneg h.slope)] -- abs_pow
    ring
  rw [hz,Real.exp_add]
  have hi:= ht.ignite.scale (Real.exp v); rw [Real.norm_of_nonneg (Real.exp_pos _|>.le)] at hi
  refine hi.replace (fun s hs=>?_)
  dsimp only; rw [smul_eq_mul,← Real.exp_add]; unfold v t w₁ w₂ a d sqcost flow; ring_nf
def pole (q:ℝ) : ℝ:= if 0 ≤ q*h.slope then -1 else 1
def mirror (σ:ℝ) (i:Fin (k+1)):ℝ:=σ*(3+i.val/(↑k+1:ℝ))
def seat (q:ℝ) (i:Fin (k+1)):=mirror (h.pole q) i
lemma poles (q:ℝ): |h.pole q|=1:=by unfold pole; split<;> simp
lemma image (σ) (hσ:σ≠0): Injective (mirror (k:=k) σ):=by
  intro i j hh; apply Fin.ext; apply Nat.cast_injective (R:=ℝ); apply mul_left_cancel₀ (show (↑k + (1:ℝ))⁻¹ ≠0 from (by positivity)); have ht:= mul_left_cancel₀ hσ hh
  unfold mirror at hh; change 3+_=3+_ at ht; rw [add_right_inj] at ht; field_simp at ht ⊢; exact ht
lemma extent (i:Fin (k+1)): 3 ≤ 3+i.val/(↑k+1:ℝ)∧ 3+i.val/(↑k+1:ℝ) ≤ 6 := by
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  have hp: 0< (↑k+1:ℝ):= by positivity
  apply le_trans (b:=(3:ℝ)+1) _ (by norm_num)
  apply add_le_add_right; rw [div_le_one hp]; exact le_trans (Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)) (by linarith)
lemma realms (q:ℝ) (i:Fin (k+1)): |h.seat q i|≤6:= by
  unfold seat mirror; rw [abs_mul,h.poles,one_mul, abs_of_nonneg (le_trans (by norm_num) (extent i|>.1))]; exact (extent ..).2
lemma landing (q:ℝ) (i:Fin (k+1)): h.scaleT q ≤ h.sqcost (R*h.seat q i)*q:=by
  let u:ℝ:=3+i.val/(↑k+1:ℝ); obtain ⟨hp,hk⟩:= extent i
  let a:= h.peak; let b:= h.slope*R
  have h₀ : 0< R:= h.full.1
  have hF: 1+6*|b| ≤ a:=by
    unfold b a; rw [abs_mul,abs_of_pos h₀]; nlinarith [h.funds]
  have he:0 ≤ a:=zero_le_one.trans h.full.2.1
  have ht : h.flow (R*h.seat q i)= a+b*h.pole q*u:=by unfold flow seat mirror u a b; ring
  rw [scaleT, sqcost,sqcost, ht]; have hh: h.flow 0=a:=by unfold flow a; ring
  rw [hh]; calc
    _ = (1-a^2)*q + |q| *(2*a*|b|+|b|^2):= by unfold b; rw [abs_mul h.slope R, abs_of_pos h₀]; simp only [abs_mul]; rw [abs_of_nonneg he, abs_of_pos (by norm_num: (0:ℝ)<2)]; ring_nf; rw [sq_abs]; ring
    _ ≤ _ := by
      change 3≤u at hp; change u≤6 at hk
      let d:= |b|; have hd:d≥0:= abs_nonneg _
      have hu:= h.funds; have hB : q*b*h.pole q = -(|q| *d):= by
        unfold pole; unfold d b; split
        · rw [abs_mul h.slope, abs_of_pos h₀, ← mul_assoc |q|, ← abs_mul,abs_of_nonneg (by assumption)]; ring
        rw [abs_mul h.slope, abs_of_pos h₀, ← mul_assoc |q|, ← abs_mul, abs_of_neg (lt_of_not_ge (by assumption))]; ring
      have hX : (b*h.pole q)^2=d^2:=by unfold d; rw [mul_pow, ← sq_abs (h.pole q), h.poles, sq_abs b]; ring
      have hdg : 2*a*d+d^2 ≤ 2*a*(d*u) - d^2*u^2:= by
        have hg:6*d≤a:=by unfold d; linarith
        calc
          _ ≤ 3*a*d := by nlinarith [mul_le_mul_of_nonneg_right hg hd]
          _ ≤ a*d*u := by nlinarith only [mul_le_mul_of_nonneg_left hp (mul_nonneg he hd)]
          _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right (show d*u≤a from (Eq.trans_le (mul_comm d u)  ((mul_le_mul_of_nonneg_right hk hd).trans hg))) (mul_nonneg hd ((by norm_num: (0:ℝ)≤3).trans hp))]
      have hc: |q| *d^2*u^2≥ q*d^2*u^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) (sq_nonneg _)
      have hh: - (|q| * d)*u=q*((b*h.pole q)*u) := by rw [← hB]; ring
      change (1-a^2)*q+ |q| *(2*a*d+d^2)≤_
      calc
        _ ≤ (1-a^2)*q+|q| *(2*a*(d*u)-d^2*u^2):= add_le_add_right (mul_le_mul_of_nonneg_left hdg (abs_nonneg _)) _
        _ ≤ (1-a^2)*q-2*a*q*(b*h.pole q*u)-q*d^2*u^2 := by nlinarith only [hc,show 2*a*q*(b*h.pole q*u)=2*a*(-(|q| *d)*u) from by rw [hh]; ring]
        _ = _ := by rw [← hX]; ring
end Fold
end YM.FullVolume.Ray
