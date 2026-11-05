import YM.MergeProof.West.Mural
/-!
# Power bounds on polynomials of chamber,varying V
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {α V : Type*}
def coinRate (X:Clump V) (r : ℝ) := (X.map fun w=> ‖((↑w.1):ℂ)‖ * r ^ w.2.length).sum
def lumpD (X:Clump V) :ℕ := (X.map fun w=> w.2.length).sum
variable (X:Clump V) (L : List V) (W P:V→poly α)
lemma coins_list (v:ℝ)(hv:0≤v)(H:∀ i,coin (W i) ≤ v): coin (L.map W).prod ≤ v^L.length:= by
   induction L with
   | nil=>simp [coin]
   | cons t s IH=>exact (funds _ zero_le_one ..).trans ((mul_le_mul (H t) IH (Rise.sign _ _ zero_le_one) hv).trans_eq (pow_succ' v _).symm)
lemma degree_list (d : ℕ)(h:∀ i, totalDegree (W i)≤d) : totalDegree (L.map W).prod≤ L.length*d:= by
   induction L with
   | nil=>simp
   | cons t s IH=>simp only [List.map_cons,List.prod_cons]; apply (totalDegree_mul ..).trans ((add_le_add (h t) IH).trans ?_); simp [add_mul,add_comm]

lemma massX (r : ℝ)(hv : 0≤r): 0≤coinRate X r:=by
   induction X with
   | nil=>rfl
   | cons a l IH=>exact add_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hv _)) IH
lemma coinCost (r:ℝ)(hv:0≤r)(h:∀ i,coin (W i)≤ r): coin (honors X W) ≤ coinRate X r:= by
   induction X with
   | nil=>simp [honors,coin,coinRate]
   | cons a l H=> exact (Rise.taller _ zero_le_one ..).trans (add_le_add ((Rise.funds _ zero_le_one _ _).trans (mul_le_mul (show coin (C ((a.1:ℝ):ℂ)) ≤ ‖(↑a.1:ℂ)‖ from (by simp [coin])) (coins_list _ _ r hv h) (Rise.sign _ _ zero_le_one) (norm_nonneg _))) H)
lemma degreeCost (d:ℕ)(h:∀ i,totalDegree (W i) ≤ d): totalDegree (honors X W) ≤ lumpD X * d:=by
    induction X with
    | nil=>simp [honors]
    | cons a l H=>
      rw [show honors (a::l) W=C (↑a.1)*(a.2.map W).prod + honors l W from rfl]
      apply (totalDegree_add ..).trans (max_le ?_ ?_)
      · refine (totalDegree_mul ..).trans ((add_le_add le_rfl (degree_list _ _ _ h)).trans ?_); simp [lumpD,add_mul]
      exact H.trans (Nat.mul_le_mul_right _ (show lumpD l ≤ _ by simp [lumpD]))

def cents (X:Clump V) (r : ℝ):= (X.map fun w=> ‖((↑w.1):ℂ)‖ * w.2.length * r ^ w.2.length).sum
lemma penny (r : ℝ)(hv : 0≤r): 0≤cents X r:=by
   induction X with
   | nil=>rfl
   | cons a l IH=>exact add_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hv _)) IH
lemma pursesC (r ε : ℝ)(hr : 1≤r)(he:0≤ε)(h:∀ i,coin (W i)≤r)(hc:∀ i,coin (P i)≤ r)(ht:∀ i,coin (W i - P i) ≤ ε) :
    coin (honors X W-honors X P) ≤ cents X r * ε:=by
  have hP := zero_le_one.trans hr
  have hv (l:List V): coin ((l.map W).prod - (l.map P).prod) ≤ l.length*r^l.length * ε := by
    induction l with
    | nil=>simp [coin]
    | cons i l H=>
       let y:=(l.map W).prod; let z:= (l.map P).prod
       change coin (W i*y - P i*z) ≤ ↑(l.length+1 : ℕ)*r^(l.length+1)*ε
       rw [show W i*y-P i*z=(W i-P i)*z+W i*(y-z) by ring]; refine (taller _ zero_le_one ..).trans ((add_le_add (show coin _ ≤ ε*r^l.length from ?_) (show coin _ ≤ r*(↑l.length*r^l.length*ε) from ?_)).trans ?_)
       · exact (funds _ zero_le_one ..).trans (mul_le_mul (ht i) (coins_list _ _ _ hP hc) (Rise.sign _ _ zero_le_one) he)
       · exact (funds _ zero_le_one ..).trans (mul_le_mul (h i) H (Rise.sign _ _ zero_le_one) hP)
       push_cast; have hh:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr l.length.le_succ) he; rw [pow_succ] at hh ⊢; linarith only [hh]
  induction X with
  | nil=> simp [honors,cents,coin]
  | cons a l H=>
    let u:ℂ:=a.1; let f:=(a.2.map W).prod; let g:=(a.2.map P).prod
    change coin (C u*f+honors l W-(C u*g+honors l P)) ≤ (‖u‖*a.2.length* r^a.2.length+cents l r)*ε
    rw [add_sub_add_comm,← mul_sub]; refine (taller _ zero_le_one ..).trans ((add_le_add ((funds _ zero_le_one ..).trans (mul_le_mul (show coin (C (σ:=α) u) ≤ ‖u‖ from by simp [coin]) (hv a.2) (Rise.sign _ _ zero_le_one) (norm_nonneg _))) H).trans_eq ?_)
    ring
end YM.Next.Rank.Tapes.West
