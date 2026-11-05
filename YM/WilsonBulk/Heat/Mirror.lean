import YM.WilsonBulk.Heat.Wick

/-!
# Wick product identity and formal Gaussian integration by parts

This pins the normalized expectation used. Full free Wick moment, *does*
include coarse zero modes if present in G. Doesn't imply any estimate on
actual conditionals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators
open Function Finset
open MvPolynomial (pderiv X C)
variable {α : Type} [Fintype α] (G : Page α 2)

abbrev kick (i : α) (p : Formula α) := ∑ j, G (two i j) • pderiv j p
abbrev hitchW (i : α) (p : KTime α) := ∑ j, G (two i j) • wall (pderiv j) p
omit [Fintype α] in
lemma deriv_commutes (i j : α) (p : Formula α) : pderiv i (pderiv j p)=pderiv j (pderiv i p) := by
  by_cases he : i=j; · rw [he]
  ext1 z
  simp [MvPolynomial.coeff_pderiv,he, Ne.symm he] -- reindex
  rw [add_right_comm z]; ring
lemma laplace_deriv (f : Formula α) (j : α) : pderiv j (laplace G f)=laplace G (pderiv j f) := by
  simp only [laplace_eval,map_sum,Derivation.map_smul]; apply sum_congr rfl fun x _=> sum_congr rfl fun y _=>?_
  rw [deriv_commutes j y,deriv_commutes j x]
lemma Wields.wall {f : Formula α} {p : KTime α} (h : Wields G f p) (j : α) : Wields G (pderiv j f) (wall (pderiv j) p) := by
  refine ⟨by rw [wall_price,h.1],?_⟩; ext1 i
  rw [lapTime_price, sun_price, wall_price,wall_price,← laplace_deriv]; rw [← lapTime_price,h.2.symm, sun_price,Derivation.map_smul]
lemma gasp (f : Formula α) (p : Formula α) : laplace G (f*p) = laplace G f * p + airing G f p + airing G p f + f * laplace G p := by
  simp only [laplace_eval,airing,MvPolynomial.pderiv_mul,map_add,smul_add,mul_sum,sum_mul, ← sum_add_distrib]
  apply sum_congr rfl fun x _=>sum_congr rfl fun y _=>?_; simp only [smul_mul_assoc,mul_smul_comm,← smul_add]; congr 1; ring
lemma laplace_X (x : α) : laplace G (X x)=0 := by simp [laplace_eval, Pi.single_apply, apply_ite (pderiv ..)]
omit [Fintype α] in
lemma line_symm (h : Regular G) (i j) : G (two i j)=G (two j i) := (congr_arg G (show two i j=two j i ∘ (Equiv.swap (0:Fin 2) 1) from by ext1 k; fin_cases k <;> simp [two])).trans (h.eq _ _)
lemma air_raise (h : Regular G) (x : α) (p : Formula α) : airing G p (X x)+airing G (X x) p=kick G x p := by
  calc _ = (∑ j,(G (two x j)/2) • (pderiv j p)) + ∑ j,(G (two x j)/2) • (pderiv j p) := by
            unfold airing; rw [sum_comm (f:=fun x' y:α=> (G (two x' y)/2) • ((pderiv x' (X x))*pderiv y p))];
            simp only [MvPolynomial.pderiv_X,Pi.single_apply];
            simp [mul_ite,ite_mul,smul_ite]; exact sum_congr rfl fun i _=> by rw [line_symm G h i x]
       _ = _ := by rw [← sum_add_distrib]; unfold kick; refine sum_congr rfl fun j _=>?_ ; rw [← add_smul]; congr 1; ring
lemma responseX (h : Regular G) (x : α) (p : Formula α) : laplace G (X x*p)=X x * laplace G p + kick G x p := by rw [gasp,laplace_X,zero_mul,zero_add,add_comm _ (airing ..),air_raise G h]; abel
lemma wedgeTime (h : Regular G) (x : α) (p : KTime α) :
    lapTime G (Polynomial.C (X x)*p)=Polynomial.C (X x)*lapTime G p + hitchW G x p := by ext1 n; simp only [lapTime_price, hitchW, Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff,Polynomial.coeff_add,Polynomial.coeff_smul,wall_price]; exact responseX G h x _
lemma lapTime_X (p : KTime α) : lapTime G (Polynomial.X*p)= Polynomial.X*lapTime G p := by
  ext1 n; rw [lapTime_price]; cases n with
  | zero => rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul_zero, map_zero]
  | succ n => rw [Polynomial.coeff_X_mul,Polynomial.coeff_X_mul,lapTime_price]
omit [Fintype α] in
lemma lapTime_c (p : Formula α) : sundial α (Polynomial.C p)=0 := by ext1 n; simp [sun_price]
lemma hTime {x : α} (p : Formula α) : hitchW G x (timer G p) = timer G (kick G x p) := by
  unfold hitchW kick; rw [map_sum]; refine sum_congr rfl fun j _=>?_; rw [map_smul,timer_ray,timer_ray]
  exact congr_arg _ (((ray_thin G p).wall G j).is G)
lemma Wick_Xt (h : Regular G) (x : α) (p : Formula α) :
    timer G (X x*p) = Polynomial.C (X x) * timer G p + Polynomial.X * timer G (kick G x p) := by
  simp_rw [timer_ray]; symm; apply Wields.is
  have hp := ray_thin G p; have hk:= ray_thin G (kick G x p)
  refine ⟨by rw [Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_mul_zero,hp.1,add_zero],?_⟩
  simp only [map_add,D_leib,wedgeTime G h x, lapTime_X,lapTime_c,hp.2,hk.2,zero_mul,zero_add]
  rw [show sundial α Polynomial.X=1 from Polynomial.derivative_X]; rw [one_mul]
  rw [show hitchW G x (timeRead G p)=timeRead G (kick G x p) from hTime G (x:=x) p]; abel
lemma Wick_X (h : Regular G) (x : α) (p : Formula α) :
    wick G (X x*p)= X x * wick G p+∑ y,G (two x y) • wick G (pderiv y p) := by
  -- Wick polynomial means evaluating timer at t=1. Hence equivalent to
  -- normalized translated Gaussian; at mean plug in element. No linear response removed.
  have H : ∑ y,G (two x y) • wick G (pderiv y p)= wick G (kick G x p) := by unfold kick; simp [map_smul]
  rw [H]; change reader _ (timer G (X x*p)) = X x*reader _ (timer G p)+reader _ (timer G _)
  rw [Wick_Xt G h]; simp only [map_add,map_mul]; simp [reader_actual]
end YM.WilsonBulk.Sheet
