import YM.WilsonBulk.Slice.Still

/-!
# Algebraic Markov comparison criterion

This stage certifies finite-coordinate gauge re-expression for full
before-Haar action and interactions, not physical activity norms nor
change of actual density. General through assembling action leading
quadratic and log J (unit) on a fiber. Caller may insert marked vertices via
positive aggregate too. `R` positive exponent of COARSE log interactions,
so subtract from total coarse action. Same leading given up to Q shape lifted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Sheet
open scoped Topology Classical BigOperators ContDiff
open Function Finset PowerSeries Matrix
variable {A M : Type} [CommRing A] [CommRing M] [Algebra ℝ A] [Algebra ℝ M] {α β ι : Type} {n : ℕ}
lemma c_empty (U : PowerSeries A→ₐ[ℝ]PowerSeries M) (hz : constantCoeff (U X)=0) {u : PowerSeries A} (h : constantCoeff u=0) : constantCoeff (U u)=0 := by
  apply X_dvd_iff.mp; obtain ⟨v,h⟩:= X_dvd_iff.mpr h; rw [h,map_mul]; exact dvd_mul_of_dvd_left (X_dvd_iff.mpr hz) _
lemma blank_agrees {p q : Tape ι} (h : Steps n (boast α ι p) (boast α ι q)) : Steps n p q := by simpa only [blankD_X,boast_home] using h.push (blankD α ι) (by rw [blankD_X,constantCoeff_X])

namespace Sheet
variable [Fintype α] [Fintype ι]
variable {G H B J V : Matrix α α ℝ} {T : α→ StageD α ι}

omit [Fintype ι] in
lemma switchedQ (T : α→StageD α ι) : switch T (seedQ ι J) = forceQ J T := by rw [seedQ,forceQ_map]; simp_rw [switch_to]

omit [Fintype ι] in
lemma preserved (hp : Starting T V) (hj : V.transpose*J*V=B) {P Q : Tape ι} (he : Steps 1 (boast α ι P+seedQ ι B) (boast α ι Q+forceQ J T)) : constantCoeff P=constantCoeff Q := by
  have hu := contrast_empty hp hj; rw [contrast,switchedQ,map_sub,sub_eq_zero] at hu
  exact (steps_initial ..).mp (blank_agrees (Steps_cancel he ((steps_initial ..).mpr hu)))

-- Ward predicate on (fiber rotated-shifted) input/equality: interaction exponent formula
structure Cradle (B G : Matrix α α ℝ) (F M I : StageD α ι) (Q R : Tape ι) : Prop where
  -- quadratic precision of B in F, plus this external part Q. Include NO missing constant term; M is log Haar
  leading : Steps 1 F (boast α ι Q+seedQ ι B)
  jac : constantCoeff M=0
  centered : I = -F+boast α ι Q+seedQ ι B+M
  read : bags ι G (tide I) = tide R
  interact : constantCoeff R=0
lemma Cradle.positive {F M I Q R} (h : Cradle B G (ι:=ι) F M I Q R) : constantCoeff I=0 := by
  rw [h.centered]; simp only [map_add,map_neg,h.jac,(steps_initial ..).mp h.leading]; abel
variable {F1 F2 I1 I2 M1 M2 : StageD α ι} {P Q R S : Tape ι}
lemma starts_of (hx : Cradle B G F1 M1 I1 P R) (hy : Cradle J H F2 M2 I2 Q S) (h : F1=switch T F2) : Steps 1 (boast α ι P + seedQ ι B) (boast α ι Q + forceQ J T) := by
  have hb := hy.leading.push (switch T) (by rw [switch_X,constantCoeff_X]); rw [map_add,switch_sat, switchedQ] at hb; exact hx.leading.symm.trans (h.symm ▸ hb)

variable [DecidableEq α]
lemma duty_factor (hp : Starting T V) (hj : V.transpose*J*V=B)
    (hx : Cradle B G F1 M1 I1 P R) (hy : Cradle J H F2 M2 I2 Q S)
    (ha : F1=switch T F2) (hm : tide M1=switch T (tide M2)*levy V T) : tide (I1+boast α ι (Q-P)) = customs B J V T (tide I2) := by
    have hc : constantCoeff (contrast B J T)=0 := contrast_empty hp hj
    have hr : constantCoeff (switch T (I2-M2))=0 := c_empty _ (by rw [switch_X,constantCoeff_X]) (by rw [map_sub,hy.positive,hy.jac,sub_self])
    have he : switch T (I2-M2)+contrast B J T+M1=I1+boast α ι (Q-P) := by
      rw [hy.centered,hx.centered,ha]; simp only [contrast,map_sub,map_add,map_neg,switch_sat]; abel
    unfold customs
    have ht : tide I2=tide (I2-M2)*tide M2:= by rw [← tide_both (p:=I2-M2) (by rw [map_sub,hy.positive,hy.jac,sub_self]) hy.jac,sub_add_cancel]
    rw [← he,tide_both (by rw [map_add,hr,hc,add_zero]) hx.jac,tide_both hr hc ,hm, ht]
    rw [map_mul]; rw [show switch T (tide (I2-M2))=tide (switch T (I2-M2)) from tutor _ constantCoeff_X (by simp [hy.positive,hy.jac])]; ring
lemma equated (hp : Starting T V) (hv : V.det ≠0) (hj : V.transpose*J*V=B) (hh : V*G*V.transpose=H) (hB : B.IsSymm) (hb : B*G=1) (hg : G.IsSymm)
    (hx : Cradle B G F1 M1 I1 P R) (hy : Cradle J H F2 M2 I2 Q S)
    (ha : F1=switch T F2) (hm : tide M1=switch T (tide M2)*levy V T) : P-R=Q-S := by
  have hpq : constantCoeff (Q-P)=0 := by rw [map_sub, preserved hp hj (starts_of hx hy ha),sub_self]
  have ht : constantCoeff (boast α ι (Q-P))=0 := c_empty _ (by rw [boast_X,constantCoeff_X]) hpq
  have hv : tide (I1+boast α ι (Q-P)) = customs B J V T (tide I2) := by
    exact duty_factor hp hj hx hy ha hm
  have hr : tide ((Q-P)+R)=tide S := by
    rw [← hy.read, ← warp (tide I2) hg hB hb hp (by assumption) hj hh,← hv]
    rw [add_comm I1,tide_both ht hx.positive,show tide (boast α ι (Q-P))=boast α ι (tide (Q-P)) from (tutor (MvPolynomial.aeval ((fun i=>named (Sum.inr i)):ι→StageD α ι)) constantCoeff_X hpq).symm,bags_display hg,hx.read,tide_both hpq hx.interact]
  rw [← tide_injective (p:= (Q-P)+R) (by rw [map_add,hpq,hx.interact,add_zero]) hy.interact hr]; abel
end Sheet
end YM.WilsonBulk
