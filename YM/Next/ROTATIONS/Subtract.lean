import YM.Next.ROTATIONS.Band
import YM.Next.ROTATIONS.Nodes


/-!
# Moment subtraction and positive response
One orbit of nodes under dilation. Constants fixed once its scale and order are set
(they may depend on m; cost exponents will not, unless so quantified).
-/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Nodes
open scoped Topology ContDiff NNReal ENNReal BigOperators

def menu (j k : ℕ) := width (num j) (slash (2*k) sun)
lemma menu_far (j k : ℕ) : Far (menu j k) := (slash_far sun_far _).width _
def dish (m j : ℕ) := Finset.range ((Nodes.coeff m j).natDegree+1)
def credits (m j k : ℕ) (s : ℝ) (f : Profile) := (Nodes.coeff m j).coeff k * tally (2*k) f * s⁻¹^(2*k)
def board (m j : ℕ) (s : ℝ) (f : Profile) := ∑ k∈dish m j, credits m j k s f • width s (menu j k)
/-- correction at scale s. Odd residuals use a different factor below. -/
def bake (m : ℕ) (s : ℝ) (f : Profile) := ∑ j∈Finset.range m, board m j s f
lemma bake_far (m : ℕ) (s) (f : Profile) : Far (bake m s f) := Far.sum _ fun i _ => Far.sum _ fun k _ => ((menu_far i k).width s).scale _
lemma menu_even (i k : ℕ) : Reflects false (menu i k) := by
  refine Reflects.tall ?_ _
  intro x
  simp_rw [slash_at sun_far, sun_even x,inv_neg]
  rw [(show Even (2*k) from ⟨k,by omega⟩).neg_pow]; rfl
lemma bake_even (m : ℕ) (s) (f : Profile) : Reflects false (bake m s f) :=
  Reflects.sum _ fun i _ => Reflects.sum _ fun k _ => ((menu_even i k).tall _).scale _
lemma Ends.paid {f : Profile} (h : Ends f) {g : ℝ → ℝ} (hg : Continuous g) : Integrable (fun x : ℝ => f x*g x) :=
  (f.continuous.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.mul_right h)

private lemma into (j k) (s : ℝ) (hs : 0<s) (g : ℝ → ℝ) :
    (∫ x,width s (menu j k) x*g x) = ∫ x,slash (2*k) sun x*g (s*x*num j) := by
  rw [pat _ hs _ _]; unfold menu; rw [pat _ (num_pos _)]; congr 1; funext x; rw [mul_comm (num j),← mul_assoc]

private lemma board_test (m j : ℕ) (s : ℝ) (hs : 0<s) (f : Profile) (g : ℝ→ℝ) (hg : Continuous g) :
    let q (v p : ℝ) := f p * sun v * (Nodes.coeff m j).eval ((p/(s*v))^2) * g (s*v*num j)
    Integrable (fun v => ∫ p,q v p) ∧ (∫ x,board m j s f x*g x)=∫ v,∫ p,q v p := by
  intro q
  let H := dish m j
  let b := Nodes.coeff m j
  let h (k : ℕ) v := slash (2*k) sun v * g (s*v*num j)
  have hx k : Integrable (h k) := (slash_far sun_far _).1.paid (g:=fun v => g (s*v*num j)) (by fun_prop)
  have hw v : (∫ p, q v p) = ∑ k∈H, credits m j k s f*h k v := by
    have he p : q v p = ∑ k∈H, b.coeff k * s⁻¹^(2*k) * h k v * (p^(2*k)*f p) := by
      dsimp only [q]; rw [Polynomial.eval_eq_sum_range]
      change (_*Finset.sum H _)*_=_; simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc
        _ = (f p*sun v)*(b.coeff k * (((p/(s*v))^2)^k))*g (s*v*num j) := rfl
        _ = _ := by
          simp only [h,slash_at sun_far,← pow_mul,div_eq_mul_inv,mul_inv,mul_pow]; ring
    simp_rw [he]
    rw [integral_finsetSum H ?_]; swap
    · intro k _
      have hu := (pump (2*k) f).integrable (μ:=volume)
      apply Integrable.const_mul; exact (integrable_congr (ae_of_all _ (pump_at (2*k) f))).1 hu
    simp_rw [integral_const_mul,← counts]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [b,credits]; ring
  simp_rw [hw]
  refine ⟨integrable_finsetSum H (fun k _ => (hx k).const_mul _),?_⟩
  have he (x) : board m j s f x*g x=∑ k∈H, credits m j k s f*(width s (menu j k) x*g x) := by
    simp [board,H,Finset.sum_mul,mul_assoc]
  simp_rw [he]
  rw [integral_finsetSum H (fun k _ => (((menu_far j k).1.width s).paid hg).const_mul _),
    integral_finsetSum H (fun k _ => (hx k).const_mul _)]
  simp_rw [integral_const_mul, into _ _ _ hs]; rfl

lemma bake_test (m : ℕ) (s : ℝ) (hs : 0<s) (f : Profile) (hf : Ends f) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ p,bake m s f p*g p)=
    ∫ v : ℝ,sun v * ∫ p,f p * ∑ j∈Finset.range m,(Nodes.coeff m j).eval ((p/(s*v))^2) * g (s*v*num j) := by
  let q (j : ℕ) (v p : ℝ) := f p * sun v * (Nodes.coeff m j).eval ((p/(s*v))^2) * g (s*v*num j)
  have he j := board_test m j s hs f g hg
  have hx : (∫ p,bake m s f p*g p)=∑ j∈Finset.range m, ∫ p, board m j s f p*g p := by
    simp_rw [bake, _root_.sum_apply, Finset.sum_mul]
    apply integral_finsetSum
    intro k _
    exact (show Far (board m k s f) from Far.sum _ (fun j _ => ((menu_far k j).width s).scale _)).1.paid hg
  rw [hx]
  simp_rw [(he _).2]; rw [← integral_finsetSum _ (fun j _ => (he j).1)]
  congr 1; funext v
  have hp i : Integrable (q i v) := by
    have ht : q i v = fun p => f p*(sun v * (Nodes.coeff m i).eval ((p/(s*v))^2)*g (s*v*num i)) := by
      funext p; unfold q; ring
    rw [ht]; exact hf.paid (by fun_prop)
  change ∑ j∈Finset.range m,(∫ p,q j v p)= _
  rw [← integral_finsetSum _ (fun j _ => hp j),← integral_const_mul]
  congr 1; funext p; unfold q
  simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

private lemma power_sum (v p s : ℝ) (hv : v ≠ 0) (hs : 0<s) (m j) (h : j<m) :
    (∑ i∈Finset.range m,(Nodes.coeff m i).eval ((p/(s*v))^2)*(s*v*num i)^(2*j))=p^(2*j) := by
  have he := sums m j h ((p/(s*v))^2)
  simp_rw [loc,← pow_mul] at he
  calc
    _ = (s*v)^(2*j)*∑ i∈Finset.range m, (Nodes.coeff m i).eval ((p/(s*v))^2)*(num i)^(2*j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [mul_pow (s*v),mul_left_comm]
    _ = _ := by rw [he,div_pow]; field_simp

lemma correct (m : ℕ) (s : ℝ) (hs : 0<s) (f : Profile) (hf : Ends f) (he : Reflects false f) :
    Centred (2*m) (f - bake m s f) := by
  intro j hj
  rw [map_sub]
  rcases Nat.even_or_odd j with ⟨k,hk⟩ | h
  · rw [show j=2*k by omega]; simp_rw [counts, mul_comm (_^_) (bake m s f _)]
    rw [bake_test m s hs f hf (fun x : ℝ => x^(2*k)) (by fun_prop)]
    have hz x : sun x*(∫ p, f p*∑ j∈Finset.range m,(Nodes.coeff m j).eval ((p/(s*x))^2)*(s*x*num j)^(2*k)) =
        sun x * ∫ p : ℝ,p^(2*k)*f p := by
      by_cases H : x=0
      · simp_rw [H,sun_far.at_zero,zero_mul]
      congr 1; congr 1; funext p; rw [power_sum x p s H hs m k (by omega),mul_comm]
    simp_rw [hz]; rw [integral_mul_const, show (∫ x,sun x)=1 from by simpa [counts] using sun_mass,one_mul,sub_self]
  · rw [tally_odd false f he j (by simpa),tally_odd false _ (bake_even m s f) j (by simpa),sub_self]

lemma linear_add (m : ℕ) (s) (f g : Profile) : bake m s (f+g)=bake m s f+bake m s g := by
  unfold bake board credits; simp_rw [map_add,mul_add,add_mul,add_smul,Finset.sum_add_distrib]
lemma linear_sub (m : ℕ) (s) (f g : Profile) : bake m s (f-g)=bake m s f-bake m s g := by
  refine eq_sub_of_add_eq ?_; rw [← linear_add,sub_add_cancel]
end YM.Outer
