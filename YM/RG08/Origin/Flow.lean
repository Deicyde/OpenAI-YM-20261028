import YM.RG08.Origin.Space

/-! # Log of actual Gaussian coefficient machine

Euler in coupling (ordinary factorial convention). All products on full
fields before capture. Heat-line marks also can bind to this log. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Finset Filter Analysis Matrix
open scoped Topology ContDiff
variable {X ι : Type}

abbrev Op (X : Type) := Scroll (Psalm X)
lemma dance_price (F W : Op X) (a : ℝ) : dancing (a • F) W=a • dancing F W := by
  funext n e x; simp only [Pi.smul_apply,dancing,Finset.sum_apply,Pi.mul_apply,smul_eq_mul, Finset.mul_sum,mul_assoc]
lemma dance_plus (F W U : Op X) : dancing (F+W) U=dancing F U+dancing W U := by rw [dance_sym,dance_add,dance_sym U F,dance_sym U W]
lemma sing_a (s : Finset ι) (F : ι→Op X) (u : Op X) : dancing (∑ i∈s,F i) u= ∑ i∈s,dancing (F i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => funext n e; simp [dancing]
  | insert i s hi ih => rw [sum_insert hi,sum_insert hi,dance_plus,ih]
private lemma flipF {M : Type} [AddCommMonoid M] {κ : Type} (x y : Finset ι) (u z : Finset κ) (f : ι → ι → κ → κ → M) :
    ∑ i∈x, ∑ j∈y,∑ a∈u,∑ b∈z,f i j a b=∑ a∈u,∑ b∈z,∑ i∈x,∑ j∈y,f i j a b := by
  simp_rw [Finset.sum_comm (s:=y) (t:=u)]; rw [sum_comm]; refine sum_congr rfl fun i _=> ?_
  simp_rw [Finset.sum_comm (s:=y) (t:=z)]; rw [sum_comm]
section flows
variable [Fintype X] [DecidableEq X] (M : Matrix X X ℝ)

def landP (F : Op X) : Op X := fun n e=> lap M (F n e)
def rim (F H : Op X) : Op X := fun n e=> ∑ b∈wheel n,∑ a∈wheel e, arch M (F b.1 a.1) (H b.2 a.2)
lemma landD (F : Op X) : landP M F=(1/2:ℝ) • ∑ i,∑ j, M i j • sway (zpk j) (sway (zpk i) F) := by
  funext n e x; unfold landP lap; simp only [Pi.smul_apply,Finset.sum_apply,sway]; rfl
lemma rimD (F H : Op X) : rim M F H=∑ i,∑ j, M i j • dancing (sway (zpk i) F) (sway (zpk j) H) := by
  funext n e x; unfold rim; simp only [Finset.sum_apply,arch,Pi.smul_apply,dancing,Pi.mul_apply,smul_eq_mul,sway,Finset.mul_sum];
  -- shuffle
  simp_rw [← mul_assoc]; exact flipF (wheel n) (wheel e) univ univ (fun i j a b => _)
lemma over_flu {F : Op X} (h : Muted _ F) (e : Fluid F) :
    landP M (priori F)=dancing (landP M F+(1/2:ℝ) • rim M F F) (priori F) := by
  rw [landD,landD,rimD,dance_plus,dance_price,dance_price,sing_a,sing_a]
  simp_rw [sway_exp _ e h,sway_dance _ (sway_fluid _ e) (priori_fluid e), sway_exp _ e h, ← dance_rotate, sing_a, dance_price, smul_add,sum_add_distrib,smul_add]
lemma heat_priori {F : Op X} (h : Muted _ F) (e : Fluid F) (hv : Views M F) : countT (priori F)=landP M (priori F) := by
  rw [rhyme_t _ h,over_flu M h e]
  congr 1
  funext n a; rw [countT,← Nat.cast_smul_eq_nsmul ℝ,hv]; rfl

-- no polynomial infrastructure on X needed yet

def wickLayer (n : ℕ) (f : Psalm X) : Psalm X := (↑(n.factorial):ℝ)⁻¹ • ((lap M)^[n] f)
lemma wick_eq_n (F : Op X) (h : countT F=landP M F) : Fluid F → ∀ n e,F n e=wickLayer M n (F 0 e) := by
  intro hg n e; have hx (k : ℕ) : ContDiff ℝ ω ((lap M)^[k] (F 0 e)) := by induction k with | zero => exact hg 0 e| succ n ih => rw [Function.iterate_succ_apply']; exact lap_prime M ih
  induction n with
  | zero => simp [wickLayer]
  | succ n ih =>
    have he := congr_fun (congr_fun h n) e
    change (n+1) • F (n+1) e=lap M (F n e) at he
    unfold wickLayer at *; rw [ih] at he
    rw [Function.iterate_succ_apply']
    rw [lap_scale M (hx n), ← Nat.cast_smul_eq_nsmul ℝ] at he
    apply smul_right_injective _ (show (↑(n+1:ℕ):ℝ)≠0 by positivity)
    dsimp only; rw [he,Nat.factorial_succ, smul_smul]; congr 1; push_cast; field_simp
end flows
end YM.RG08
