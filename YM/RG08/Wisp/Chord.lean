import YM.RG08.Camera.Due

/-! # First marker in formal Ward, before mean reinterpretation.
No g analytic threshold, full exponent in log link. Avoid identifying the
coefficient of a formal exponential by transport of ordinary rank bills.
Derived from actual polynomial-centered-stove equality applied to a g^τ-
delayed source to arbitrary order; a single (possibly scalar & disconnected)
marked response therefore obeys the same algebraic denominator-preserving
law.
-/
noncomputable section
namespace YM.RG08.Wisp
open Function Finset PowerSeries Glyph Room Cloud Camera Room.Haze
open scoped BigOperators Topology PowerSeries Classical Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {R:Type}[CommRing R][Algebra ℝ R]
abbrev Cued (n:ℕ)(V W:PowerSeries R) := ∀ i:ℕ,i<n → coeff i V=coeff i W
variable {n u:ℕ}{V W Y Z:PowerSeries R}

omit [Algebra ℝ R] in
theorem Cued.paint (h:Cued n V W)(he:Cued n Y Z):Cued n (V+Y) (W+Z):=fun i hi=>by rw [map_add,map_add,h i hi,he i hi]
omit [Algebra ℝ R] in
theorem Cued.spare (h:Cued n V W)(he:Cued n Y Z):Cued n (V*Y) (W*Z):=fun i hi=>by
 rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul];apply sum_congr rfl; intro x hx
 obtain ⟨a,b⟩:=x; have hs:a+b=i:=mem_antidiagonal.mp hx
 rw [h _ (by simp;omega),he _ (by simp;omega)]

omit [Algebra ℝ R] in
theorem rhythm (hn:0<n)(V:PowerSeries R): tiny (X^n*V):=by rw [tiny,coeff_X_pow_mul',if_neg (by omega)]
lemma raw (hn:0<n):Cued (n+n) (rise (X^n*V)) (1+X^n*V):=by
 intro i hi
 rw [rise_late (rhythm hn _) i (i+1) (by omega),Finset.sum_range_succ' _ (i+1),Finset.sum_range_succ' _ i,Finset.sum_eq_zero (s:=range i) (fun j _=>?_)]
 · simp only [zero_add,pow_zero,pow_one,rfactor,Nat.factorial_zero,Nat.cast_one,Nat.factorial_one,inv_one,one_smul,map_add];exact add_comm ..
 rw [mul_pow,←pow_mul,coeff_X_pow_mul',if_neg,smul_zero]
 have hh:n+n≤n*((j+1)+1):=by calc
    _=n*2:=by omega
    _ ≤ _:=Nat.mul_le_mul_left n (by omega)
 omega

lemma lag (hv:tiny W)(hn:0<n):Cued (n+n) (rise (W+X^n*V)) (rise W*(1+X^n*V)):=by rw [rise_together hv (rhythm hn _)]; exact Cued.spare (fun i _=>rfl) (raw hn)

variable {I J:Type}[Fintype I][Fintype J]
lemma tapped {H:Haze I}{A B:Port I}(he:Cued n A B):Cued n (H.brew A) (H.brew B):=fun i hi=>H.brew_steady i _ _ (fun j hj=>he j (hj.trans_lt hi))

/-- Formal Ward transformation on the CENTERED joint polynomial (center before Haze).
Single mark with scalar/vacuum terms absolutely retained. -/
lemma stirred (H:Haze I){x:I→Port I}{Q:Inn I}{P:I→I→ℝ}
    (h:Near x)(hh:anchored H.foam x)(hc:Boil H P Q){F:Port I}(hp:tiny F)(M:Port I):
    let U:=belt x F+belt x (liftInn Q)-liftInn Q
    ; H.brew ((rise U * (gate x).det) * belt x M)=H.brew (rise F*M):=by
 intro U
 let D:Port I:=(gate x).det
 let L(N:ℕ):Port I:=X^(N+1)
 have he(N:ℕ):H.brew (rise (U+L N*belt x M)*D)=H.brew (rise (F+L N*M)):=by
    have hz:tiny (L N*M):=rhythm (show 0<N+1 by omega) M
    have hs:tiny (F+L N*M):=by unfold tiny at *;rw [map_add,hp,hz,zero_add]
    have hh':=H.absorbed h hh hc (F+L N*M) hs;unfold evolve at hh'
    rw [map_add (belt x) F (L N * M), _root_.map_mul (belt x) (L N) M] at hh'
    have hL:belt x (L N)=L N:=by unfold L;rw [_root_.map_pow,belt_g]
    rw [hL,show belt x F+_+belt x (liftInn Q)-liftInn Q=U+L N*belt x M by unfold U;abel] at hh'; exact hh'
 have hu:tiny U:=neartiny h hp _
 have hAbs:H.brew (rise U * D)= H.brew (rise F):=H.absorbed h hh hc F hp
 ext i :1
 let n:=i+1
 have hn:0<n:=by unfold n;omega
 have hi:i+n<n+n:=by unfold n;omega
 let t1:Port I:=rise U * (1+L i*belt x M)*D;let t2:Port I:= rise F * (1+L i*M)
 have hv:Cued (n+n) (H.brew t1) (H.brew t2):=by
    have ht:= tapped (H:=H) ((lag (n:=n) (V:=belt x M) hu hn).spare (V:=rise (U+X^n*belt x M)) (Y:=D) (Z:=D) (fun _ _=>rfl))
    have hy:= tapped (H:=H) (lag (n:=n) (V:=M) hp hn)
    intro j hj;rw [←ht j hj,←hy j hj];exact congrArg (coeff j) (he i)
 have hx:=hv (i+n) hi
 have hc' (A:Port I): H.brew (X^n * A)=X^n *H.brew A:=H.brew_shunt (H.power_easy _) _
 rw [show t1=rise U*D+X^n * (rise U*D*belt x M) from by unfold t1 L n; ring,show t2=rise F+X^n * (rise F*M) from by unfold t2 L n;ring] at hx
 rw [map_add,map_add,map_add,map_add,hc',hc',coeff_X_pow_mul,coeff_X_pow_mul,hAbs,add_right_inj] at hx;exact hx

end YM.RG08.Wisp
