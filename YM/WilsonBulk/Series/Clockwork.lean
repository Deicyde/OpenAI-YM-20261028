import YM.WilsonBulk.Series.Saturation

/-!
# Coupled clock changes and power-series-valued transports

Substitution of the latter (`A→ₐ[ℝ]S(B)`) is *not* same-ring substitution
in a scalar algebra via substituting X into PowerSeries only. Keep Taylor clock
through gauge formulas, and re-clock only at particular extraction. No convergence
radius used. Agreement in Steps is through degree < n.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open scoped Classical BigOperators
open Finset PowerSeries
variable {A B M : Type} [CommRing A] [CommRing B] [CommRing M]
  [Algebra ℝ A] [Algebra ℝ B] [Algebra ℝ M] {p q : PowerSeries A} {n : ℕ}
section
omit [Algebra ℝ A]
lemma Steps.dvd : Steps n p q ↔ X^n ∣ p-q := by simp only [Steps,X_pow_dvd_iff,map_sub,sub_eq_zero]
lemma Steps.trans {r : PowerSeries A} (hp : Steps n p q) (hq : Steps n q r) : Steps n p r := fun i hi=>Eq.trans (hp i hi) (hq i hi)
lemma Steps.symm (hp : Steps n p q) : Steps n q p := fun i hi=> (hp i hi).symm
lemma Steps.sum' {ι : Type} (s : Finset ι) {U V : ι→PowerSeries A} (h : ∀ i∈s, Steps n (U i) (V i)) : Steps n (∑ i∈s,U i) (∑ i∈s,V i) :=
  fun k hk=> by simp only [map_sum]; exact sum_congr rfl fun i hi=>h i hi k hk
lemma before_end (n : ℕ) (p : PowerSeries A) : Steps n p (∑ k∈range n,X^k*C (coeff k p)) := by
  intro i hi; simp only [map_sum,coeff_mul_C,coeff_X_pow]; simp [hi]
lemma step_monomial {P : PowerSeries A} (hp : constantCoeff P=0) {m n : ℕ} (h : n≤m) (q : PowerSeries A) : Steps n (P^m*q) 0 := by
  rw [Steps.dvd,sub_zero]; exact (dvd_trans (pow_dvd_pow _ h) (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hp) _)).trans (dvd_mul_right _ _)
end

-- proof by truncated assembly
variable (F : A→ₐ[ℝ]PowerSeries B) {g : PowerSeries B}
variable (g) in
def tuneAny (p : PowerSeries A) : PowerSeries B := PowerSeries.mk (fun i=>coeff i (∑ j∈range (i+1), g^j * F (coeff j p)))
lemma tuneAny_agree {U : A→ₐ[ℝ]PowerSeries B} {x : PowerSeries B} (h : ∀ p, Steps n (F p) (U p)) (hg : Steps n g x) (hx : Steps n p q) : Steps n (tuneAny F g p) (tuneAny U x q) := by
  intro i hi; unfold tuneAny; rw [coeff_mk,coeff_mk]; refine Steps.sum' _ (fun j hj=> (Steps.powers hg j).mul ?_) i hi
  rw [mem_range] at hj; rw [hx j (by omega)]; exact h _
lemma tuneAny_add (g) (p q) : tuneAny F g (p+q)=tuneAny F g p + tuneAny F g q := by ext1 i; simp [tuneAny,mul_add,sum_add_distrib]
lemma tuneAny_long (h : constantCoeff g=0) (p n) : Steps n (tuneAny F g p) (∑ j∈range n,g^j*F (coeff j p)) := by
  intro i hi; unfold tuneAny; simp only [coeff_mk,map_sum]
  refine sum_subset (range_mono hi) (fun j hj he=>?_)
  apply Eq.trans (step_monomial h (show i+1≤j by rw [mem_range] at he; omega) _ i (by omega)); rw [map_zero]
lemma tuneAny_C (a : A) (g) : tuneAny F g (C a)=F a := by
  ext1 i; simp only [tuneAny,coeff_mk,coeff_C,map_sum]; rw [sum_range_succ']; simp
lemma tuneAny_Cmul (a : A) (h : constantCoeff g=0) (p : PowerSeries A) : tuneAny F g (C a * p)=F a * tuneAny F g p := by
  ext1 i
  exact (Steps.trans ((tuneAny_long F h (C a*p) (i+1))) ((show ∑ j∈range (i+1), g^j*F (coeff j (C a*p))= F a * ∑ j∈range (i+1),g^j*F (coeff j p) by
    simp only [coeff_C_mul, map_mul,mul_sum]; exact sum_congr rfl fun _ _=> by ring) ▸ (Steps.mul (p:=F a) (q:=F a) Steps.self (tuneAny_long F h p _).symm))) i (by omega) -- direction transport?
lemma tuneAny_Xmul (h : constantCoeff g=0) (p : PowerSeries A) : tuneAny F g (X*p) = g*tuneAny F g p := by
  ext1 i
  calc
    _ = coeff i (∑ j∈range (i+1+1),g^j*F (coeff j (X*p))) := tuneAny_long F h (X*p) _ i (by omega)
    _ = coeff i (g* ∑ j∈range (i+1),g^j* F (coeff j p)) := congr_arg _ (by rw [sum_range_succ']; simp [pow_succ',coeff_succ_X_mul,mul_assoc,mul_sum])
    _ = _ := (Steps.mul Steps.self (tuneAny_long F h p _)).symm i (by omega)
lemma tuneAny_mul (h : constantCoeff g=0) (p q : PowerSeries A) : tuneAny F g (p*q)= tuneAny F g p * tuneAny F g q := by
  let t:= tuneAny F g
  have h0 : t 0=0 := by simpa only [map_zero] using tuneAny_C F 0 g
  have hm (a : A) (j : ℕ) : t (X^j*C a*q)= t (X^j*C a)*t q := by
    induction j with
    | zero=> simp only [pow_zero,one_mul,t,tuneAny_Cmul F _ h,tuneAny_C]
    | succ j ih=> dsimp only [t] at *; rw [pow_succ',mul_assoc X _ (C a),mul_assoc X _ q,tuneAny_Xmul F h, ih, tuneAny_Xmul F h,mul_assoc]
  ext1 i
  let s (j : ℕ) := X^j*C (coeff j p)
  have he : Steps (i+1) p (∑ j∈range (i+1), s j) := before_end (i+1) p
  have ht (i : ℕ) : t ((∑ j∈range i,s j)*q) = t (∑ j∈range i,s j)*t q := by
    induction i with
    | zero => simp [h0]
    | succ i ih=> dsimp only [t] at *; rw [sum_range_succ,add_mul,tuneAny_add,tuneAny_add,add_mul,ih]; exact congr_arg _ (hm (coeff i p) i)
  calc _ = coeff i (t ((∑ j∈range (i+1), s j)*q)) := (tuneAny_agree F (fun _=>Steps.self) Steps.self (he.mul Steps.self)) i (by omega)
       _ = coeff i (t (∑ j∈range (i+1), s j)*t q) := by rw [ht]
       _ = _ := (Steps.mul (tuneAny_agree F (fun _=>Steps.self) Steps.self he) Steps.self).symm i (by omega)
def tuner (h : constantCoeff g=0) : PowerSeries A→ₐ[ℝ]PowerSeries B where
  toFun:=tuneAny F g
  map_one':=by rw [show (1:PowerSeries A)=C (1:A) from (map_one _).symm,tuneAny_C,map_one]
  map_zero':=by rw [show (0:PowerSeries A)=C (0:A) from (map_zero _).symm,tuneAny_C,map_zero]
  map_mul':=tuneAny_mul F h
  map_add':=tuneAny_add F g
  commutes' a:=by rw [PowerSeries.algebraMap_apply,tuneAny_C,F.commutes]
lemma tuner_C (h : constantCoeff g=0) (a : A) : tuner F h (C a)=F a := tuneAny_C F a g
lemma tuner_X (h : constantCoeff g=0) : tuner F h X=g := by
  rw [show (X:PowerSeries A)=X*(1:PowerSeries A) from (mul_one _).symm]; exact (tuneAny_Xmul F h 1).trans (by change g*tuner F h 1=_; rw [map_one,mul_one])

-- all tapes algebra hom preserving clock zero ideal is continuous & determined
lemma Steps.push (U : PowerSeries A→ₐ[ℝ]PowerSeries B) (h : constantCoeff (U X)=0) (hu : Steps n p q) : Steps n (U p) (U q) := by
  rw [Steps.dvd,← map_sub]; obtain ⟨v,hv⟩ := Steps.dvd.mp hu; rw [hv,map_mul,map_pow]; exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h) _) _
lemma tuning (U : PowerSeries A→ₐ[ℝ]PowerSeries B) (h : constantCoeff (U X)=0) (ha : ∀ a,U (C a)=F a) : U=tuner F h := by
  ext1 p; ext1 i
  let s (j:ℕ) := X^j*C (coeff j p)
  have he : Steps (i+1) p (∑ j∈range (i+1), s j) := before_end (i+1) p
  calc _ = coeff i (U (∑ j∈range (i+1), s j)) := he.push U h i (by omega)
       _ = coeff i (tuner F h (∑ j∈range (i+1),s j)) := by simp only [s,map_pow,map_mul,map_sum,ha,tuner_C,tuner_X]
       _ = _ := tuneAny_agree F (fun _=>Steps.self) Steps.self he.symm i (by omega)
lemma tuner_const (h : constantCoeff g=0) (p : PowerSeries A) : constantCoeff ((tuner F h) p)=constantCoeff (F (constantCoeff p)) := by
  change constantCoeff (tuneAny F g p)=_; simp [tuneAny]
lemma tutor (h : constantCoeff g=0) {p : PowerSeries A} (hp : constantCoeff p=0) : tuner F h (tide p) = tide (tuner F h p) := by
  ext1 i
  calc _ = coeff i (tuner F h (budget i p)) := (tide_full hp i).push _ (by rw [tuner_X,h]) i (by omega)
       _ = coeff i (budget i (tuner F h p)) := by simp only [budget,allot,map_sum,map_smul,map_pow]
       _ = _ := (tide_full (p:=tuner F h p) (by rw [tuner_const,hp,map_zero,map_zero]) i).symm i (by omega)
end YM.WilsonBulk
