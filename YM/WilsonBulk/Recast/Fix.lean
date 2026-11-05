import YM.WilsonBulk.Recast.Tone

/-!
# Reset operations as integer-degree induction. Polynomial structure
 in any ℝ-algebra. Speed: through each fixed number of steps for order,
  no unbounded iteration costs from DEFINITION. (Bound elsewhere).
  Using inverse rho = recover p generic in unit. No arbitrary choice of
  alpha, force new ratio equation Step. PowerSeries; see rpow costs later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Recall
open Function Filter PowerSeries Finset Equiv Sheet
open scoped Topology Classical BigOperators
variable {A B X : Type} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B] {p g r q : PowerSeries A} {n : ℕ}

-- stable fixed point on constants-one
structure Poised (F : PowerSeries A→ PowerSeries A) : Prop where
  anchored u : constantCoeff u=1 → constantCoeff (F u)=1
  raise (p q : PowerSeries A) (n : ℕ) (he : Steps n p q) (hv : constantCoeff p=1) (hh : constantCoeff q=1) : Steps (n+1) (F p) (F q)
variable {F : PowerSeries A→ PowerSeries A}
def saga (F : PowerSeries A→ PowerSeries A) : PowerSeries A := mk fun i=> coeff i (F^[i+1] (1:PowerSeries A))
omit [Algebra ℝ A] in
lemma stage1 (p q : PowerSeries A) : Steps 1 p q ↔ constantCoeff p=constantCoeff q:= ⟨fun h=> by simpa only [coeff_zero_eq_constantCoeff] using h 0 (by norm_num),fun h i hi=>by rw [Nat.eq_zero_of_le_zero (by omega : i≤0)]; simpa only [coeff_zero_eq_constantCoeff] using h⟩
namespace Poised
omit [Algebra ℝ A]
variable (h : Poised F)
include h
lemma holds (k : ℕ) : constantCoeff (F^[k] 1)=1 := by induction k with
  | zero=> simp
  | succ k ih=>rw [Function.iterate_succ_apply']; exact h.anchored _ ih
lemma climbs (n : ℕ) (p q : PowerSeries A) (he : constantCoeff p=1) (hv : constantCoeff q=1) : Steps n (F^[n] p) (F^[n] q) := by
  induction n generalizing p q with
  | zero => intro i hi; omega
  | succ n ih=>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']; apply h.raise _ _ _ (ih p q he hv)
    · cases n with
      | zero=> exact he
      | succ n=> exact ((stage1 ..).mp ((ih p 1 he (map_one _)).small (by omega))).trans (h.holds _)
    cases n with
    | zero=> exact hv
    | succ n=> exact ((stage1 ..).mp ((ih q 1 hv (map_one _)).small (by omega))).trans (h.holds _)
lemma tenure (n m : ℕ) (hm : n≤m) : Steps n (F^[n] 1) (F^[m] 1) := by
  obtain ⟨u,rfl⟩:= Nat.exists_eq_add_of_le hm; rw [Function.iterate_add_apply]; exact h.climbs n _ _ (map_one _) (h.holds _)
lemma seasons (n : ℕ) : Steps n (saga F) (F^[n] 1) := fun i hi=> by rw [saga,coeff_mk, h.tenure (i+1) n (by omega) i (by omega)]
lemma sits : constantCoeff (saga F)=1 := Eq.trans ((stage1 ..).mp (h.seasons 1)) (h.holds 1)
lemma yields : F (saga F)=saga F := by
  ext1 i; rw [saga, coeff_mk]; refine Eq.trans (h.raise _ _ i (h.seasons i) h.sits (h.holds i) i (by omega)) ?_ ; rw [Function.iterate_succ_apply']
lemma uniq (p : PowerSeries A) (hp : constantCoeff p=1) (hv : F p=p) : p=saga F := by ext1 i; unfold saga; rw [coeff_mk]; simpa only [Function.iterate_fixed hv] using h.climbs (i+1) p 1 hp (map_one _) i (by omega)
end Poised

-- ratio least fixed point solves r^2=q(rX). q is either ω(V) or 1+...) with const1

def decision (V : PowerSeries A→ PowerSeries A) (s : PowerSeries A) := 1+(1/2:ℝ) • (V s-1-(s-1)^2)
def polling (q : PowerSeries A) := saga (decision fun p=> bar p q)
def arises (q : PowerSeries A) := saga (decision fun _=> q)
omit [Algebra ℝ A] in
lemma square_improves (hP : constantCoeff p=0) (hp : constantCoeff q=0) (hh : Steps n p q) : Steps (n+1) (p^2) (q^2) := by
  suffices Steps (n+1) (p*p-p*q) 0 ∧ Steps (n+1) (q*p-q*q) 0 by
    apply (Steps.dvd).2
    rw [show p^2-q^2=p*p-p*q+(q*p-q*q) from by ring]; exact dvd_add (by simpa using Steps.dvd.mp this.1) (by simpa using Steps.dvd.mp this.2)
  refine ⟨?_,?_⟩ <;> rw [← mul_sub];
  · simpa using StepsL (r:=p) (show Steps n (p-q) 0 from sub_self q ▸ minus_clock (s:=q) hh Steps.self) hP
  simpa using StepsL (r:=q) (show Steps n (p-q) 0 from sub_self q ▸ minus_clock (s:=q) hh Steps.self) hp
lemma decision_safe {U : PowerSeries A → PowerSeries A} (hf : ∀ p,constantCoeff (U p)=1) (hh : ∀ {p q : PowerSeries A} {n}, Steps n p q→Steps (n+1) (U p) (U q)) : Poised (decision U) := by
  constructor
  · intro p hp; simp [decision,hf,hp] -- constantCoeff_smul?
  intro p q n h hp hq; apply Steps.add Steps.self (Steps.scale _ _); exact minus_clock (minus_clock (hh h) Steps.self) (square_improves (p:=p-1) (q:=q-1) (by rw [map_sub,hp,map_one,sub_self]) (by rw [map_sub,hq,map_one,sub_self]) (minus_clock h Steps.self))
lemma eq_decision (q : PowerSeries A→ PowerSeries A) : decision q p=p ↔ p^2=q p := by
  unfold decision; rw [← eq_sub_iff_add_eq', one_div,inv_smul_eq_iff₀ (by norm_num : (2:ℝ) ≠ 0)]; rw [show (2:ℝ) • (p-1)=(p+p)-(1+1) from by rw [smul_sub, show (2:ℝ)=(1:ℝ)+1 by norm_num, add_smul, add_smul]; simp only [one_smul]]; constructor <;> intro h <;> linear_combination -h
lemma poll_safe (hp : constantCoeff p=1) : Poised (decision (fun u=>bar u p)) := decision_safe (by simp [bar_const,hp]) (fun h=>barSteps h Steps.self)
lemma arise_safely (hp : constantCoeff p=1) : Poised (decision (fun _:PowerSeries A=> p)) := decision_safe (fun _=>hp) (fun _=> Steps.self)
lemma poll_rule (hp : constantCoeff p=1) : constantCoeff (polling p)=1 ∧ (polling p)^2=bar (polling p) p:= ⟨(poll_safe hp).sits,(eq_decision _).mp (poll_safe hp).yields⟩
lemma poll_only (he : constantCoeff p=1) (hv : constantCoeff r=1) (hr : r^2=bar r p) : r=polling p:= (poll_safe he).uniq r hv ((eq_decision _).mpr hr)
lemma arises_rule (hp : constantCoeff p=1) : constantCoeff (arises p)=1 ∧ (arises p)^2=p:= ⟨(arise_safely hp).sits,(eq_decision _).mp (arise_safely hp).yields⟩
lemma arises_only (he : constantCoeff p=1) (hv : constantCoeff r=1) (hr : r^2=p) : r=arises p:= (arise_safely he).uniq r hv ((eq_decision _).mpr hr)
end YM.WilsonBulk.Recall
