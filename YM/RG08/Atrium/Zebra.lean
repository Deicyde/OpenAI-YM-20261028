import YM.RG08.Atrium.Bays
import YM.RG08.Fete.Muse
import YM.RG08.Fete.Olds
/-!
# Primary read crossing formula under scalar ring. Sharp degree filtration preserved.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Atrium
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo Trill
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius PowerSeries Matrix
variable {I:Type}{G:Gauge}{d n p l e D k:ℕ}
local notation "E₀"=>Ed G Cover
local notation "Y"=>Snap G d
local notation "A₀"=>Loc G 1
variable {X:Labels.Frame G d}
private lemma sonic_sum' (f:Pearl){X:Fin n→E₀→ℝ}{s:Finset I}{M:I→Pack n E₀}(u:I→ℝ){a:Fin n→ℝ}(h:∀ i∈s,Trill.Ready D G n (M i))(hx:∀ i,Bearing (stance _) p 0 (a i) (X i)):sonic (∑ i∈s,u i • M i) f X=∑ i∈s,u i*sonic (M i) f X:=by
 have ht(i:I)(hi:i∈s): Summable (fun x:Tape n E₀=> (u i) * (M i x f*(∏ j,X j (x j)))):=by
    obtain ⟨σ,hσ,B,hB,h₁⟩:=(h i hi).well
    exact ((sonic_abs (h i hi).coherent h₁ hB f le_rfl (by rw [mul_zero];exact half_pos hσ|>.le) hx).of_norm).mul_left _
 unfold sonic tote;simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,sum_mul,mul_assoc,← tsum_mul_left]
 exact Summable.tsum_finsetSum (f:=fun (i:I) (x:Tape n E₀)=> u i*(M i x f*(∏ j,X j (x j)))) ht
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
lemma pix_clock (X:Labels.Frame G d)(z:X.Index)(v:pedal)(s:Finset I)(u:I→ℝ){M:I→Pack n E₀}(h:∀ i∈s,Trill.Ready D G n (M i)):pix X z v (∑ i∈s,u i • M i)=∑ i∈s,u i*pix X z v (M i):=by
 let k:=(X.grades z).1; let p:=(X.grades z).2;let f:=celloTest v
 unfold pix harrow
 let N(i:I):Y→ℝ:=grants (M i) f p d
 have H:(grants (∑ i∈s,u i • M i) f p d)=∑ i∈s,u i • N i:=by
    funext x;unfold N grants; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply,smul_eq_mul,mul_sum];rw [sum_comm];apply sum_congr rfl;intro i hi
    choose C hC hZ using key_budget G d
    exact sonic_sum' f u h (p:=d*p) (X:=fun j=>pluck (i j).val x) (a:=fun j=> C _*∏ _m:Fin (i j).val,‖x‖) (fun j=>(hZ (i j).val (fun _=>x)).here le_rfl (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (i j).isLt)))
 change (tally X p k z (Tensor.coeff (grants (s.sum _) f p d) p (0:Y))) = _
 have hs'(i:I)(hi:i∈s):ContDiffAt ℝ (p:WithTop ℕ∞) (N i) 0:=by
    obtain ⟨σ,hσ,B,hB,h₁⟩:=(h i hi).well
    exact (grants_smooth (h i hi).coherent h₁ hB f).contDiffAt.of_le le_top
 rw [H,Tensor.coeff_sum p (0:Y) (fun i=>u i • N i) s (fun i hi=>(hs' i hi).const_smul (u i)),map_sum];apply sum_congr rfl;intro i hi
 rw [show Tensor.coeff (u i • N i) p (0:Y)=u i • Tensor.coeff (N i) p 0 from ?_,_root_.map_smul];rfl
 unfold Tensor.coeff;rw [iteratedFDeriv_const_smul_apply (hs' i hi)];apply smul_comm
-- smaller Pack addition Ready, mix heights.
lemma Ready_sum (s:Finset I)(u:I→ℝ){M:I→Pack n E₀}(hs:∀ i∈s,Trill.Ready D G n (M i)):Trill.Ready D G n (∑ i∈s,u i • M i):=by
 -- induction
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty];exact ⟨hush,fun _=>Forms.Sym.zero,1,zero_lt_one,0,le_rfl,tin⟩
 | @insert i s hi ih=>
   obtain ⟨H,hsx,σ,hσ,B,hB,h₁⟩:=hs i (by simp)
   let V:=∑ i∈s,u i • M i
   obtain ⟨Q,hq,τ,hτ,C,hC,h₂⟩:= ih (fun j hj=>hs j (by simp [hj]))
   rw [sum_insert hi]
   let a:=min σ τ; have ha:0<a:=lt_min hσ hτ
   refine ⟨(H.smul (u i)).add Q,fun f=>((hsx f).smul _).add (hq f),a,ha,|u i| *B+C,by positivity,?_⟩
   refine ((h₁.mono (min_le_left ..) le_rfl (fun _=>le_rfl) le_rfl).smul _).add (h₂.mono (min_le_right ..) le_rfl (fun _=>le_rfl) le_rfl) (by positivity) hC
-- collect full rank at e with convolution. even when ℓ=0 & n0 shifts
local notation "Ra"=>GrainS E₀

def ballot (P:GrainS (Ed G Cover))(c:Accent X):Dig:=PowerSeries.mk (project X P · c)
lemma ballot_value (P:Ra)(c:Accent X)(e:ℕ):tap e (ballot P c)=project X P e c:=PowerSeries.coeff_mk ..
lemma relieved (u:I→ℝ)(s:Finset I){P:I→Ra}(a:Accent X)(h:∀ i∈s,∀ k n,Trill.Ready D G n (P i k n)):ballot (∑ i∈s,u i • P i) a=∑ i∈s,u i • ballot (P i) a:=by
 ext e:1;change tap e _= PowerSeries.coeff e _;rw [map_sum];simp_rw [PowerSeries.coeff_smul,←show tap e=(fun t:Dig=>PowerSeries.coeff e t) from rfl,ballot_value,project,smul_eq_mul,mul_sum];rw [sum_comm];apply sum_congr rfl; intro b hb
 split_ifs
 · rw [Finset.sum_apply,Finset.sum_apply];simp_rw [Pi.smul_apply,pix_clock X a.ear a.test.play s u (M:=fun i=>P i _ b) (h:=fun i hi=>h i hi _ b)]  
 exact (Finset.sum_eq_zero (s:=s) fun i hi=>mul_zero _).symm
lemma voted (u:Dig)(c:Accent X)(P:Ra)(h:∀ i n,Trill.Ready D G n (P i n)):ballot (slip u P) c=u*ballot P c:=by
 ext i:1;change tap i _=tap i _;rw [ballot_value,tap_mul];simp_rw [ballot_value,project,mul_sum];rw [sum_comm];apply sum_congr rfl;intro j hj
 let r:=(X.grades c.ear).2-j
 change (if _ then _ else _) =∑ a∈range (i+1), tap a u * if r ≤ _ then _ else _
 by_cases hg:r ≤ i
 · rw [if_pos hg,slip,pix_clock X c.ear c.test.play _ _ (M:=fun a=>P (_-a) j) (h:=fun _ _=>h _ _),overrange (e:=i) _ (Nat.sub_le i r)]
   apply sum_congr rfl;intro a ha;have ha:=mem_range.mp ha
   split_ifs with hp hP
   · rw [show i-r-a=i-a-r by omega]
   · omega
   · omega
   rw [mul_zero]
 rw [if_neg hg];exact (sum_eq_zero fun j (_:j∈range (i+1))=>by rw [if_neg (by omega),mul_zero]).symm
lemma ballot_slow (P:Ra)(h:Skiff.Lit l P)(a:Accent X):Paces (X.grades a.ear).2 l (ballot P a):=by
 intro i hi;rw [ballot_value];let r:=(X.grades a.ear).2
 unfold project;refine sum_eq_zero fun j hj=>?_;have hj:=mem_range.mp hj;split_ifs with h₁;swap;rfl
 rw [show P (i-(r-j)) j=0 from ?_,Fete.opus_mask]
 exact Classical.not_not.mp (fun hu=>by have ht:=h (i-(r-j)) j hu;unfold r at ht;omega)
