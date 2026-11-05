import YM.RG08.Nacre.Larch
/-! # Adjacent yarn: powers including inverse for negative exponents; triangular and
 parity; quantitative strict-event fees later. !-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Nacre
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost
open PowerSeries Finset.Nat
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {w:ℕ→ℝ}
private lemma parityL {p:Essence}{e:ℕ}(hp:∀ n ≤ e, coeff n p≠0→Even n)(i:ℕ):∀ n ≤ e, coeff n (p^i)≠0→Even n:=by
 induction i with
 | zero=> intro n _ h;rw [pow_zero,coeff_one] at h; by_cases hp:n=0
          · rw [hp];apply Even.zero
          · rw [if_neg hp] at h;exact (h rfl).elim
 | succ i ih=>
    intro n hn h; by_contra hN; apply h
    rw [pow_succ,coeff_mul];apply Finset.sum_eq_zero; intro a ha;obtain ⟨x,j⟩:=a;have ht : x+j=n:=HasAntidiagonal.mem_antidiagonal.mp ha;dsimp only;by_cases hz:coeff x (p^i)=0
    · rw [hz,zero_mul]
    by_cases hu:coeff j p=0
    · rw [hu,mul_zero]
    exfalso;exact hN (ht ▸ (ih x (by omega) hz).add (hp j (by omega) hu))
abbrev prudent (w:ℕ→ℝ):Prop:=∀ n,w n ≠0 → Even n
lemma loyal (h:prudent w)(n:ℕ):coeff n (ratio w)≠0→Even n:=by
 induction n using Nat.strong_induction_on with
 | h n ih=>
            rcases n with _|n
            · intro _; apply Even.zero
            intro H;by_contra hk;apply H
            have ht:=fixed w (n+1);rw [birch (hasHead w)] at ht -- birch private; expose, pos premise
            have hy:boost w (ratio w) (n+1)=0:=by
               apply Finset.sum_eq_zero; intro i hi; obtain ⟨he,hf⟩:=Finset.mem_erase.mp hi
               rw [factor,coeff_X_pow_mul'];split_ifs with hv; swap; rfl
               rw [coeff_smul];by_cases hz:w i=0
               · rw [hz,zero_smul]
               rw [show coeff (n+1-i) (ratio w ^ i)=0 from Classical.byContradiction (fun hV=>?_),smul_zero]
               have hJ := parityL (fun m (hn:m ≤ n)=> ih m (by omega)) i (n+1-i) (by omega) hV
               apply hk; rw [← Nat.sub_add_cancel hv];exact hJ.add (h i hz)
            have hn:contour (ratio w) (n+1)=0:=by
               apply Finset.sum_eq_zero; intro a ha;split
               next h=>
                  by_contra H;have H1:=left_ne_zero_of_mul H;have H2:=right_ne_zero_of_mul H; apply hk;exact HasAntidiagonal.mem_antidiagonal.mp ha ▸ (ih _ h.1 H1).add (ih _ h.2 H2)
               next h=>rfl
            rw [hy,hn,if_neg (by omega)] at ht;linarith
            omega
lemma inv_loyal {p:Essence}(h:∀ i, coeff i p≠0→Even i)(n:ℕ)(hn:coeff n p⁻¹≠0): Even n:=by
 induction n using Nat.strong_induction_on with
 | h n ih=>by_contra he;apply hn;rw [coeff_inv,if_neg (by rintro rfl; exact he (Even.zero)),Finset.sum_eq_zero (fun a ha=>?_),mul_zero]
           split
           next h'=>
             by_contra H;have H1:=left_ne_zero_of_mul H;have H2:=right_ne_zero_of_mul H;apply he;exact HasAntidiagonal.mem_antidiagonal.mp ha ▸ (h _ H1).add (ih _ h' H2)
           next h'=>rfl

def shift (w:ℕ→ℝ)(i k:ℕ):= ratio w^i * (ratio w)⁻¹ ^k
def dues (w:ℕ→ℝ)(i k e:ℕ):ℝ:= if i ≤ e then coeff (e-i) (shift w i k) else 0
lemma beam_dues (w:ℕ→ℝ)(i k e:ℕ):dues w i k e=coeff e (PowerSeries.X^i* shift w i k):= (coeff_X_pow_mul' ..).symm
lemma due_self (w:ℕ→ℝ)(i k:ℕ): dues w i k i=1:=by
 have he:constantCoeff (ratio w)=1:= (coeff_zero_eq_constantCoeff_apply _).symm.trans (hasHead w)
 rw [dues,if_pos le_rfl,Nat.sub_self,coeff_zero_eq_constantCoeff_apply];simp [shift,he] -- constantCoeff_inv
lemma due_even (h:prudent w)(i k n:ℕ)(ht:dues w i k n≠0):i ≤ n∧Even (n-i):=by
 unfold dues at ht;split at ht
 next H=>refine ⟨H,?_⟩;by_contra he; apply ht;rw [shift,coeff_mul];apply Finset.sum_eq_zero; intro a ha; by_contra hx; have hf:=parityL (p:=ratio w) (e:=a.1) (fun k _=>loyal h k) i a.1 le_rfl (left_ne_zero_of_mul hx);have hz:=parityL (p:=(ratio w)⁻¹) (e:=a.2) (fun i _=>inv_loyal (loyal h) i) k a.2 le_rfl (right_ne_zero_of_mul hx); exact he (HasAntidiagonal.mem_antidiagonal.mp ha ▸ hf.add hz)
 contradiction
-- normalization identity (read kinetic exactly; scalar at p=0 independent)
lemma reciprocity (w:ℕ→ℝ): ratio w*(ratio w)⁻¹=1:= PowerSeries.mul_inv_cancel _ (by rw [←coeff_zero_eq_constantCoeff_apply,hasHead w];exact one_ne_zero)
lemma reset (w:ℕ→ℝ)(h:w 0=1){n e:ℕ}(he:e ≤ n): (∑ i∈range (n+1),dues w i 2 e*w i)= if e=0 then 1 else 0:=by
 let F:Essence:=1+∑ i∈ (Finset.range (n+1)).erase 0,factor w (ratio w) i
 have hx:coeff e (F*((ratio w)⁻¹)^2)=if e=0 then 1 else 0:=by
    have hz:coeff e (F*(ratio w)⁻¹ ^2)= coeff e (ratio w^2*(ratio w)⁻¹ ^2):=Room.wired e (fun k hk=> (guaranteed w (hk.trans he)).symm) (fun _ _=>rfl)
    rw [hz, ←mul_pow,reciprocity,one_pow,coeff_one] -- tap def
 rw [←hx]
 have hA:F=∑ i∈range (n+1),factor w (ratio w) i:=by
    rw [←Finset.sum_erase_add _ _ (show 0∈range (n+1) by simp)];unfold F factor; simp [h,add_comm]
 rw [hA, Finset.sum_mul,map_sum];apply Finset.sum_congr rfl; intro i _
 unfold factor; rw [mul_smul_comm, smul_mul_assoc, mul_assoc,coeff_smul,smul_eq_mul,←shift,←beam_dues]; ring
end YM.RG08.Nacre
