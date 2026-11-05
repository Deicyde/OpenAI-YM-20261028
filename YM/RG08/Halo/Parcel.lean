import YM.RG08.Halo.Beam
import YM.RG08.Yurt.Levy

/-! # Priced rows act on test-bearing directions. Whole market polynomial. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Halo
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon Yurt
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {G:Gauge}{I J:Type}{n m k p d:ℕ}{u D C B θ σ:ℝ}{K:Kernel I J}{L:Side}
-- absolute row around shifted root.
def tub {I:Type}(p:ℕ)(x:Market I):ℝ:= (1+abroad x)^p
lemma tub_nn (p:ℕ)(x:Market I):0≤tub p x:=pow_nonneg (by linarith [abroad_nn x]) _
lemma tub_s (L:Side)(h:0<σ)(o:Site L)(p:ℕ)(x:Market I)(y:Market J): tub p y≤(5^p*Jetty.blade 0 p σ)*tub p x*Real.exp (σ*Pert.Bulk.delta L (x.1+lift o) y.1):=by
 let w:=Pert.Bulk.delta L (x.1+lift o) y.1; have hw:0≤w:=Pert.Bulk.delta_nonneg ..
 have hh:=hustle_fee p h hw
 have he: abroad y ≤ w + abroad x + 4:=by
    apply (length_off L x.1 _ (lift o)).trans;gcongr
    · exact div_le_self (abroad_nn x) (Nat.one_le_cast.mpr L.property)
    exact length_lift L o
 unfold tub; refine (pow_le_pow_left₀ (by linarith [abroad_nn y]) (show 1+abroad y≤ 5*(1+abroad x)*(1+w) from by nlinarith only [he,hw,abroad_nn x,mul_nonneg (abroad_nn x) hw]) p).trans ?_
 rw [mul_pow, mul_pow]; exact (mul_le_mul_of_nonneg_left hh (mul_nonneg (by positivity:(0:ℝ)≤5^p) (tub_nn p x))).trans_eq (by unfold tub w;ring)

def treasure (J:Type)[Fintype J](p:ℕ)(s:ℝ):ℝ:= (((Fintype.card J:ℕ):ℝ)*5^p*blade 0 p s)
lemma treasure_nn (J:Type)[Fintype J](p:ℕ)(h:0≤σ):0≤treasure J p σ:=by unfold treasure; have ht:=blade_nn 0 p h;positivity

def push (K:Kernel I J)(o:Cover)(V:Market J→ℝ)(x:Market I)(y:Market J):ℝ:=K (x.1+o,x.2) y*V y
def melt (K:Kernel I J)(o:Cover)(V:Market J→ℝ)(x:Market I):ℝ:=∑' y,push K o V x y

lemma row_budget [Fintype J](h:RowCost σ L K C)(hk:0<σ)(hc:0≤C){V:Market J→ℝ}(hv:Bearing (stance J) p 0 D V)(o:Site L)(x:Market I):
 let T (y:Market J):=‖push K (lift o) V x y‖
 ; Summable T ∧∑' y,T y ≤ treasure J p σ * C * D * tub p x:=by
 intro T
 let R:=treasure J p σ*C*D*tub p x
 have hw:= hv.1; have hr:0≤R:=mul_nonneg (mul_nonneg (mul_nonneg (treasure_nn J _ hk.le) hc) hw) (tub_nn ..)
 let X:= (x.1+lift o,x.2)
 have hE:(∑' y,ENNReal.ofReal (T y))≤ ENNReal.ofReal R:=by
    let F:=D*(5^p*blade 0 p σ)*tub p x; have hF:0≤F:= by unfold F; have he:= blade_nn 0 p hk.le;have hi:=tub_nn p x;positivity
    apply (ENNReal.tsum_le_tsum (g:=fun y:Market J=>ENNReal.ofReal F * bill (K X y) (σ*Pert.Bulk.delta L X.1 y.1)) (fun y=>?_)).trans
    · rw [ENNReal.tsum_mul_left]
      have he:=Pert.Bulk.convert_market (fun y:Market J=>bill (K X y) (σ*Pert.Bulk.delta L X.1 y.1)) (ENNReal.ofReal C) (fun i=>h X i)
      apply (mul_le_mul_right he _).trans_eq
      rw [←ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul hF]; congr 1;unfold F R treasure;ring
    unfold T push; rw [Real.norm_eq_abs,abs_mul,bill,← ENNReal.ofReal_mul hF]; apply ENNReal.ofReal_le_ofReal
    rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hx:=hv.2 y;rw [hustle,zero_mul,Real.exp_zero,mul_one] at hx
    exact hx.trans ((mul_le_mul_of_nonneg_left (tub_s L hk o p x y) hw).trans_eq (by unfold F;ring))
 have ht:Summable T:=(ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE)).congr (fun i=>ENNReal.toReal_ofReal (norm_nonneg _))
 rw [← ENNReal.ofReal_tsum_of_nonneg (fun _=> norm_nonneg _) ht] at hE
 exact ⟨ht,(ENNReal.ofReal_le_ofReal_iff hr).mp hE⟩
lemma wallet [Fintype J](h:RowCost σ L K C)(hσ:0<σ)(hc:0≤C){V:Market J→ℝ}(he:Bearing (stance J) p 0 D V)(o:Site L):
 Bearing (stance I) p 0 (treasure J p σ*C*D) (melt K (lift o) V):=by
 have hz:=row_budget h hσ hc he o
 have hh:0 ≤ treasure J p σ*C*D:=mul_nonneg (mul_nonneg (treasure_nn J _ hσ.le) hc) he.1
 refine ⟨hh,fun i=>?_⟩
 rw [hustle,zero_mul,Real.exp_zero,mul_one,←Real.norm_eq_abs]
 exact (norm_tsum_le_tsum_norm (hz i).1).trans (hz i).2

lemma norms_all {a:Fin n→I→ℝ}(ha:∀ i,Summable fun j=>‖a i j‖): Summable (fun x:Tape n I=> ‖∏ i,a i (x i)‖):=by
 have h: (∑' x:Tape n I,ENNReal.ofReal ‖∏ i,a i (x i)‖)≠⊤:=by
    simp_rw [Real.norm_eq_abs,Finset.abs_prod,ENNReal.ofReal_prod_of_nonneg (fun _ _=>abs_nonneg _),all_Δ (fun i (j:I)=>ENNReal.ofReal |a i j|)]
    refine ENNReal.prod_ne_top (fun i _=>?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _=>abs_nonneg _) (by simpa [Real.norm_eq_abs] using ha i)];exact ENNReal.ofReal_ne_top
 exact (ENNReal.summable_toReal h).congr fun x=>ENNReal.toReal_ofReal (norm_nonneg _)
lemma tsum_tape (a:Fin n→I→ℝ)(ha:∀ i,Summable fun j=>‖a i j‖):(∑' x:Tape n I,∏ i,a i (x i))=∏ i,∑' j,a i j:=by
 induction n with
 | zero=>simp [tsum_fintype]
 | succ n ih=>
    rw [Fin.prod_univ_succ,← ih (fun i:Fin n=>a i.succ) (fun i=>ha _),tsum_mul_tsum_of_summable_norm (ha 0) (norms_all (fun i:Fin n=>ha i.succ))]
    rw [← (Fin.consEquiv (fun _:Fin (n+1)=>I)).tsum_eq]
    exact tsum_congr fun ⟨i,t⟩=>by rw [Fin.prod_univ_succ]; simp
lemma melt_read [Fintype J](h:RowCost σ L K C)(hσ:0<σ)(hc:0≤C){V:Fin n→Market J→ℝ}{F:Pack n (Market I)}{a:Fin n→ℝ}(he:∀ i,Bearing (stance J) p 0 (a i) (V i))(hf:Lyrics F)(ht:0<θ)(hy:Sings (stance I) d ht F B)(hb:0≤B)
 (o:Site L)(v:E4)(α:ℝ)(f:Pearl):
 sonic (Yurt.ferry K F α v (lift o)) f V= sonic F (aisle α v f) (fun i=>melt K (lift o) (V i)):=by
 let U(x:Tape n (Market I))(y:Tape n (Market J)):= ∏ i:Fin n,push K (lift o) (V i) (x i) (y i)
 let P:Pearl:=aisle α v f
 let F':=fun (x:Tape n (Market I)) (y:Tape n (Market J))=>F x P * U x y
 let D(i:Fin n):=treasure J p σ*C*a i
 have hd(i):0≤D i:=mul_nonneg (mul_nonneg (treasure_nn J p hσ.le) hc) (he i).1
 have hx(i : Fin n): Bearing (stance I) p 0 (D i) (fun x:Market I=>D i*tub p x):=by
    constructor
    · exact hd i
    intro x;change |D i*tub p x|≤ _;rw [abs_of_nonneg (mul_nonneg (hd _) (tub_nn ..)),hustle,zero_mul,Real.exp_zero,mul_one];exact le_refl _
 -- show joint absolute summability for F' using ENN product tape and F abs.
 let X(x:Tape n (Market I)):= |F x P| *∏ i:Fin n,(D i *tub p (x i))
 have hX:Summable X:=by
    have H:=sonic_abs hf hy hb P (p:=p) (a:=D) (hx:=le_refl (0:ℝ))
      (hy:=show (n:ℝ)*0≤θ/2 from by rw [mul_zero]; linarith) hx
    apply H.congr
    intro x
    change ‖F x P * ∏ i,D i*tub p (x i)‖ = |F x P| * ∏ i,D i*tub p (x i)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (prod_nonneg fun i _=>mul_nonneg (hd i) (tub_nn p (x i)))]
 have hY(x:Tape n (Market I)):(∑' y:Tape n (Market J),ENNReal.ofReal ‖F' x y‖)≤ ENNReal.ofReal (X x):=by
    simp only [F',U, Real.norm_eq_abs,abs_mul,Finset.abs_prod,ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_prod_of_nonneg (fun _ _=>abs_nonneg _),X,ENNReal.ofReal_prod_of_nonneg (fun i _=>mul_nonneg (hd i) (tub_nn ..))]
    rw [ENNReal.tsum_mul_left,all_Δ (fun i (y:Market J)=>ENNReal.ofReal |push K (lift o) (V i) (x i) y|)];gcongr with z
    have hi:= row_budget h hσ hc (he z) o (x z)
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun _=> abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hi.1)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hi.2)
 have hs:Summable (uncurry F'):=by
    have hC:Summable (fun z=>‖uncurry F' z‖):=(ENNReal.summable_toReal (f:=fun z=>ENNReal.ofReal ‖Function.uncurry F' z‖) (by
        change (∑' z : Tape n (Market I) × Tape n (Market J), ENNReal.ofReal ‖F' z.1 z.2‖) ≠ ⊤
        rw [ENNReal.tsum_prod (f:=fun x y=>ENNReal.ofReal ‖F' x y‖)];refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hY)
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun x=>mul_nonneg (abs_nonneg _) (prod_nonneg (fun i _=>mul_nonneg (hd i) (tub_nn ..)))) hX];exact ENNReal.ofReal_ne_top)).congr (fun i=>ENNReal.toReal_ofReal (norm_nonneg _))
    exact hC.of_norm
 calc
  sonic (Yurt.ferry K F α v (lift o)) f V = ∑' y, ∑' x, F' x y := by
    apply tsum_congr
    intro y
    change (∑' x:Tape n (Market I), F x P * ∏ i,Yurt.tender K (lift o) 0 (y i) (x i))
      * (∏ i,V i (y i)) = ∑' x, F' x y
    rw [←tsum_mul_right]
    apply tsum_congr
    intro x
    simp only [F',U,push,Yurt.tender,Yurt.offer,zero_mul,Real.exp_zero,one_mul,
      Finset.prod_mul_distrib,mul_assoc]
  _ = ∑' x,∑' y,F' x y := hs.tsum_comm
  _ = sonic F (aisle α v f) (fun i=>melt K (lift o) (V i)) := by
    apply tsum_congr
    intro x
    change (∑' y,F x P * U x y) = F x P * ∏ i,∑' y,push K (lift o) (V i) (x i) y
    rw [tsum_mul_left]
    exact congrArg (fun z:ℝ=>F x P*z)
      (tsum_tape (fun i=>push K (lift o) (V i) (x i)) (fun i=>(row_budget h hσ hc (he i) o _).1))
end YM.RG08.Halo
