import YM.Push.FREE_RESOLVENT.BlockRate
import YM.Push.FREE_RESOLVENT.TensorPrice
import YM.Work.B02.Slab

/-!
# Evaluating the inverse tensors in normalized directions

Use all color coordinates in real Taylor charts. Costed root
sums have a strictly positive rate including input-site displacements;
this file also gives direct directions use (can handle unbounded polynomial
growth on B directions through the whole torus, uniformly). Distinguish
E estimates on selected nonzero fields; the general pre-window arithmetic
in `JetWindows` works with the radial marks there, but the producer here
uses Taylor at the **flat field**. No differentiation across sector guards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Filter Function Set Matrix Mark TestD  Stars
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Mark
variable {τ κ ι α X : Type*} {D : Cost X}

def hill (D : Cost X) (o : X) (P : ℕ) (x : X) := (1+D.d x o)^P
lemma hill_pos (o : X) (P : ℕ) (x : X) : 0 < hill D o P x := by unfold hill; apply pow_pos; have := D.nonneg x o; linarith
lemma payment (τ : Type*) (D : Cost X) (o : X) (P : ℕ) (x : X) (l : List τ) :
    (radial τ D o P).pay l x=((hill D o P x)^l.length)⁻¹ := by
  induction l with
  | nil => simp [pay]
  | cons i l ih => rw [pay,List.length_cons, pow_succ, _root_.mul_inv_rev,ih]; rfl

section columns

-- evaluate a genuine Fréchet tensor on πⓘ spaces (no implicit Frobenius norm on those directions)
variable {a : ι → X} {b : κ → X} {p : τ → X} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
variable {d γ s M G V : ℝ} {o : X} {R : ℕ}
omit [Fintype ι] [Fintype κ] in
lemma play {n : ℕ} (F : (τ→ℝ) [×n]→L[ℝ] Matrix ι κ ℝ) (x : Fin n → (τ → ℝ)) :
    F x = ∑ k : Fin n → τ, (∏ i, x i (k i)) • F (fun i => Pi.single (k i) (1:ℝ)) := by
  let f := fun (i : Fin n) (j : τ) => x i j • (Pi.single j (1:ℝ):τ→ℝ)
  have h i : x i=∑ j,f i j := by ext b; simp [f, Pi.single_apply]
  calc
    F x = F (fun i => ∑ j, f i j) := congrArg (fun x => F x) (funext h)
    _ = ∑ k : Fin n → τ, F (fun i => f i (k i)) := F.map_sum ..
    _ = _ := Finset.sum_congr rfl fun i _ => F.map_smul_univ ..

lemma meter_rows {x : τ → ℝ} {F : (τ → ℝ) → Matrix ι κ ℝ} {l : List α} (u : α → τ → ℝ)
    (hf : ∀ w : Fin l.length → τ, (positions D p d).Rates D a b (List.ofFn w) γ M
            (jet (fun i : τ => Pi.single i 1) F (List.ofFn w) x))
    (hM : 0 ≤ M) (hG : 0 ≤ G)
    (ht : ∀ i∈l, ∀ j, ‖u i j‖ ≤ G*hill D o R (p j)) (hs : 0 < s) (hd : s+s ≤ d) (hv : D.Volume p s V) :
    Rates (radial α D o R) D a b l γ (V^l.length * ((G*polynomial s R)^l.length*M)) (jet u F l x) := by
  let n := l.length
  let Y := u ∘ l.get
  let f (k : Fin n → τ) := ∏ i, (Y i) (k i)
  let W (k : Fin n → τ) := jet (fun i : τ => Pi.single i (1:ℝ)) F (List.ofFn k) x
  have he : jet u F l x = ∑ k, f k • W k := by
    refine (play (iteratedFDeriv ℝ n F x) Y).trans (Finset.sum_congr rfl fun i _ => ?_)
    unfold W; rw [list_result]; rfl
  rw [he]
  constructor; intro i
  let χ := fun k => D.weight γ (a i) (b k)
  let C := hill D o R (a i)
  have hp : 0 < C := hill_pos ..
  let K := G*polynomial s R
  have hP : 0 < polynomial s R := zero_lt_one.trans_le (poly_le R hs)
  have hx : 0 ≤ K := mul_nonneg hG hP.le
  have hK (j) (hj : j∈l) (w : τ) : |u j w| ≤ K*C*D.weight s (a i) (p w) := by
    have hh := (radial_move (D:=D) α o R hs).widen j (a i) (p w)
    have he := hill_pos (D:=D) o R (p w)
    change C⁻¹ ≤ polynomial s R * _*(hill D o R (p w))⁻¹ at hh
    rw [← div_eq_mul_inv, le_div_iff₀ he, inv_mul_eq_div, div_le_iff₀ hp] at hh
    exact (ht j hj w).trans ((mul_le_mul_of_nonneg_left hh hG).trans_eq (by unfold K; ring))
  have hu' (w : Fin n → τ) : |f w| ≤ (K*C)^n*Real.exp (s*rays D (a i) (p ∘ w)) := by
    unfold f
    rw [Finset.abs_prod]
    refine (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hK _ (List.get_mem ..) (w j))).trans_eq ?_
    rw [Finset.prod_mul_distrib,rays, Finset.mul_sum, Real.exp_sum, Finset.prod_const, Finset.card_univ,Fintype.card_fin]; rfl
  let J (w : Fin n → τ) := ∏ j : Fin n, D.weight (-s) (a i) (p (w j))
  have hJ : (∑ w, J w) ≤ V^n := by
    unfold J; rw [← Fintype.prod_sum (fun j : Fin n => fun t : τ => D.weight (-s) (a i) (p t)), Finset.prod_const, Finset.card_univ,Fintype.card_fin]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => D.weight_nn ..) (hv.bound _) n
  have hk (w : Fin n → τ) :
      (radial α D o R).pay l (a i) * (∑ j, χ j * |(f w • W w) i j|) ≤ J w*(K^n*M) := by
    have he' := (hf w).rows i
    let T := rays D (a i) (p ∘ w)
    rw [Stars.pays] at he'
    simp_rw [Matrix.smul_apply, smul_eq_mul,abs_mul,mul_left_comm (χ _) |f w|,← Finset.mul_sum]
    have hy : 0 ≤ T := rays_nn ..
    have ht : Real.exp (s*T) ≤ J w*Real.exp (d*T) := by
      have he : J w=Real.exp ((-s)*T) := by unfold J Cost.weight T rays; rw [Finset.mul_sum, Real.exp_sum]; rfl
      rw [he,← Real.exp_add]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_right hd hy]
    let v := ∑ j, χ j*|W w i j|
    have hz : 0 ≤ v := Finset.sum_nonneg fun j _ => mul_nonneg (D.weight_nn ..) (abs_nonneg _)
    have hj : 0 ≤ J w := Finset.prod_nonneg fun i _ => D.weight_nn ..
    rw [payment]
    calc (C^n)⁻¹ * (|f w| * v) ≤ (C^n)⁻¹ * (((K*C)^n*Real.exp (s*T))*v) := by
            apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hu' w) hz); positivity
         _ = K^n * (Real.exp (s*T)*v) := by rw [mul_pow]; field_simp
         _ ≤ K^n * ((J w*Real.exp (d*T))*v) := by gcongr
         _ ≤ J w * _ := by rw [mul_assoc (J w),mul_left_comm]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he' (by positivity)) hj
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun j _ => hk j
  calc
    _ ≤ (radial α D o R).pay l (a i)*(∑ k, ∑ j, χ j * |(f k • W k) i j|) := by
      apply mul_le_mul_of_nonneg_left _ (pay_pos ..).le
      rw [Finset.sum_comm]; refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.mul_sum,Matrix.sum_apply]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (D.weight_nn ..)
    _ ≤ V^n * (K^n*M) := by rw [Finset.mul_sum]; rw [← Finset.sum_mul] at hh; exact hh.trans
                              (mul_le_mul_of_nonneg_right hJ (mul_nonneg (pow_nonneg hx _) hM))


lemma activated {x : τ → ℝ} {F : (τ → ℝ) → Matrix ι κ ℝ} {l : List α} (u : α → τ → ℝ)
    (h : ContDiffAt ℝ l.length F x)
    (hf : ∀ w : Fin l.length → τ, Bill (positions D p d) D a b (List.ofFn w) γ M
            (jet (fun i : τ => Pi.single i 1) F (List.ofFn w) x))
    (hM : 0 ≤ M) (hG : 0 ≤ G)
    (ht : ∀ i∈l, ∀ j, ‖u i j‖ ≤ G*hill D o R (p j)) (hs : 0 < s) (hd : s+s ≤ d) (hv : D.Volume p s V) :
    Bill (radial α D o R) D a b l γ (V^l.length * ((G*polynomial s R)^l.length*M)) (jet u F l x) := by
  refine ⟨meter_rows u (fun w => (hf w).row) hM hG ht hs hd hv,?_⟩
  let Q y := (F y).transpose
  have he : jet u Q l x=(jet u F l x).transpose := jet_linear u l (Bundle.switch ι κ) h
  rw [← he]; apply meter_rows u _ hM hG ht hs hd hv
  intro w
  have hx : ContDiffAt ℝ (List.ofFn w).length F x := by simpa
  erw [jet_linear (A:=F) _ _ (Bundle.switch ι κ) hx]
  exact (hf w).col
end columns
end Mark

-- concrete use on whole no-hole affine inversion
namespace Affine
open Mark Tree Precision RG TestD
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Forest S.ratio} {σ u fee M : ℝ}


end Affine
end YM.FreeResolvent
