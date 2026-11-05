import YM.PertExtension.Normalized

/-! Finite-regulator coupling-degree parity inputs. For an unscaled fixed
stencil the expectation series has even parity (not generally after dividing
by odd powers from the curvature slot convention). -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension.Orb
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory
open scoped ContDiff Topology Classical BigOperators ENNReal
open Chart Series Series.Radial Series.Tested
open PowerSeries
variable {G : Gauge}{n : Side}{P : ChartRatio G}
instance : (tangent G (Cotree n)).IsNegInvariant := ⟨by
  exact (measurePreserving_pi _ _ (fun (_:Cotree n)=>Measure.measurePreserving_neg (volume : Measure G.Color))).map_eq⟩

lemma kerTerms_neg (n : ℕ){E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (K f : E→ℝ)(u : E) : normTerm K f n (-u)=(-1)^n * normTerm K f n u:=by
  have h (f:E→ℝ)(k : ℕ) : jet f k (-u)=(-1)^k * jet f k u := by simpa only [neg_smul,one_smul] using jet_smul f k (-1) u
  have ht (j) : layers f j (-u)=(-1)^j*layers f j u:=by
    by_cases hj:j=0
    · simp [Radial.layers,hj]
    unfold Radial.layers;rw [if_neg hj] -- one if actually both rw?
    rw [h, pow_add]; simp [hj]
  let H := fun (a : ℕ→E→ℝ)=>∀ n, a n (-u)=(-1)^n*a n u
  have hh (a b : ℕ→E→ℝ)(ha : H a)(hb : H b):H (Zone.mul a b):=by
    intro i; simp_rw [Zone.mul]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
    rw [ha j.1,hb j.2,←Finset.mem_antidiagonal.mp hj,pow_add];ring
  have hb (k : ℕ) : H (Zone.TaylorPow (layers f) k) := by
    induction k with
    | zero=> intro n;by_cases hn:n=0 <;> simp [Zone.TaylorPow,hn]
    | succ k ih=> exact hh _ _ ih ht
  have ha : H (fun i=>expsum (layers f) i i):=by
    intro j;unfold expsum; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _;rw [hb k j];ring
  have he := hh (jet K) (fun i=>expsum (layers f) i i) (h K) ha
  simp_rw [normTerm,show integrandSeries f K n (-u)= (-1)^n*Zone.mul _ _ n u from he n,kernel,h f 2,show (-1:ℝ)^2=1 from by norm_num,one_mul,integrandSeries];ring

lemma rowsWith_odd (O : Observable G n){k : ℕ}(hk : Odd k) : rowsWith P O k=0:= by
  unfold rowsWith Radial.moment
  have H u: normTerm (accountingWith P O) fiscal k (-u)= -normTerm (accountingWith P O) fiscal k u:= by rw [kerTerms_neg,hk.neg_one_pow,neg_one_mul]
  have h:=integral_neg_eq_self (normTerm (accountingWith P O) fiscal k) (tangent G (Cotree n))
  simp_rw [H] at h; rw [integral_neg] at h;linarith

lemma rows_with_head (R : LocalRatio P)(even:Even n.val)(O : Observable G n): conv (diagonalWith P O) (rowsWith P (n:=n) 1)=rowsWith P O := by
  let y := PowerSeries.mk (rowsWith P O); let d := PowerSeries.mk (rowsWith P (n:=n) 1)
  have hh :PowerSeries.constantCoeff d ≠ 0:= by rw [←coeff_zero_eq_constantCoeff_apply,show coeff 0 d=rowsWith P (n:=n) 1 0 by simp [d]]; exact (pivot even R).ne'
  have he : PowerSeries.mk (diagonalWith P O) *d=y:= by
      convert (show y*d⁻¹*d=y from by rw [mul_assoc,d.inv_mul_cancel hh,mul_one])
      change PowerSeries.mk (term (y*d⁻¹))=y*d⁻¹; ext j;simp [term]
  unfold conv; change term _= _; rw [he]
  ext j;simp [term,y]

lemma normalized_odd (R : LocalRatio P)(even:Even n.val)(O : Observable G n) {k : ℕ}(hk : Odd k) : diagonalWith P O k=0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih=>
    have H := congr_fun (rows_with_head R even O) k
    simp only [conv,term,coeff_mul,coeff_mk,rowsWith_odd O hk] at H
    rw [Finset.sum_eq_single_of_mem (k,0) (Finset.mem_antidiagonal.mpr (add_zero k))] at H
    · have he:=eq_zero_or_eq_zero_of_mul_eq_zero H
      exact he.resolve_right (pivot even R).ne'
    intro ⟨a,c⟩ h hh; have hh':=Finset.mem_antidiagonal.mp h; change _ + c = k at hh'
    rcases Nat.even_or_odd c with he|ho
    · have hp:0<c:=by by_contra! heq;apply hh; ext1 <;> simp [show a=k by omega, show c=0 by omega]
      have hlt : a<k:=by omega
      have ho' : Odd a := by obtain ⟨j,hj⟩:=he;obtain ⟨m,hm⟩:=hk;exact ⟨m-j,by omega⟩
      simp only [ih a hlt ho',zero_mul]
    simp only [rowsWith_odd _ ho,mul_zero]

end YM.PertExtension.Orb
