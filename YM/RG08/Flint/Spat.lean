import YM.RG08.Flint.Stores
import YM.RG08.Weald.Fields

/-!
# Quantitative test of the nonlinear local gauge reader on exponentially and polynomially growing
constant terms. No analyticity assumptions uniform in filter. Only on gauge grammar, before L.
Carry included address shift of b. Include arbitrary global d. Constants here might depend
on d; apply at d=1 for bounds. No rooted transfer pricing here.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Flint
open Forms Function Finset Jetty Lattice Isles Pert.Bulk
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter
open Stationary
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal
variable {I J:Type}{G:Gauge}{n l p e:ℕ}{C δ a σ:ℝ}

-- color-bearing probes. shape steering
variable (X:Ed G Cover→ℝ)(U:Nd G Cover→ℝ)(w:G.El)
abbrev drift (i:Plot G Cover):ℝ:= Sum.elim (fun t=>X (i.1,t)) (fun t=>U (i.1,t)) i.2
lemma plan :kiosk (drift X U)=Weald.paint (kiosk X) (kiosk U):=by funext i; rcases i with ⟨i,t|t⟩ <;> rfl
lemma ksound (i:Ed G Cover):gain w (kiosk X) (kiosk U) i= breath (kiosk (drift X U ∘ jab (hot w) i)) (eye ((hot w).fare i.2)):=by rw [gain,rend,←plan];rfl
lemma tip (i:Ed G Cover)(j:ℕ):tap j (gain w (kiosk X) (kiosk U) i)=MvPolynomial.eval (drift X U ∘ jab (hot w) i) (Camera.print (j+1) ((hot w).fare i.2)):=by rw [ksound,tutor,Quarry.eye,look,flute]
-- no analytical norms for tabulated prices; evaluate flask deck as ordered word using absolute sum.
def ledger [Fintype I](n:ℕ)(f:Still I):ℝ:= ∑ t:Tape n I,|Camera.deck n f t|
lemma ledger_nn [Fintype I](n:ℕ)(f:Still I):0≤ledger n f:=sum_nonneg fun _ _=>abs_nonneg _
lemma ledger_out [Fintype I](n:ℕ)(f:Still I){V:I→ℝ}(hV:∀ i,|V i| ≤ C)(_hC:0≤C):|MvPolynomial.eval V (Camera.print n f)| ≤ ledger n f*C^n:=by
 rw [←deck_parley f,parley_street,ledger,sum_mul]
 refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _=>?_)
 rw [abs_mul,Finset.abs_prod];apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
 exact (prod_le_prod (fun _ _=>abs_nonneg _) fun _ _=>hV _).trans_eq (by rw [prod_const,card_univ,Fintype.card_fin])

def service (G:Gauge)(w:G.El)(r:ℕ):ℝ:= ∑ i:Loc G 1,ledger r ((hot w).fare i)
lemma ser_rank (r:ℕ)(i:Loc G 1):ledger r ((hot w).fare i) ≤ service G w r:=single_le_sum (f:=fun i=> ledger r ((hot w).fare i)) (fun _ _=>ledger_nn ..) (mem_univ i)
lemma service_nn (r:ℕ):0≤ service G w r:=sum_nonneg fun _ _=>ledger_nn ..
-- jab height shift radius 1
lemma steep (i:Ed G Cover)(j:foil G):abroad (jab (hot w) i j) ≤ abroad i+1:=by
 unfold abroad jab Quarry.hot menu;dsimp only
 split_ifs with hs
 · simp
 · simp
 · exact (length_add ..).trans_eq (by rw [length_step])

variable {X:Ed G Cover→ℝ}{U:Nd G Cover→ℝ}
def shifter (G:Gauge)(w:G.El)(p j:ℕ)(a:ℝ):ℝ:= service G w (j+1)*(a*hustle p 1 1)^(j+1)
lemma shift_nn (p j:ℕ)(hA:0≤a):0≤ shifter G w p j a:=mul_nonneg (service_nn ..) (pow_nonneg (mul_nonneg hA (hustle_nn p _ zero_le_one)) _)
lemma shift_coin (hS:0≤δ)(hs:δ≤1)(hV:Bearing (stance (Loc G 1)) p δ a X)(hU:Bearing (stance G.ColorIndex) p δ a U)(j:ℕ)(i:Ed G Cover):|tap j (gain w (kiosk X) (kiosk U) i)|≤ shifter G w p j a * hustle p δ (abroad i) ^ (j+1):=by
 let r:=abroad i; have hr:0≤r:=abroad_nn i
 let C:=a*(hustle p δ r*hustle p 1 1); have hC:0≤C:=mul_nonneg hV.1 (mul_nonneg (hustle_nn _ _ hr) (hustle_nn p _ zero_le_one))
 have he(i:Plot G Cover):|drift X U i|≤a*hustle p δ (abroad i):=by rcases i with ⟨i,t|t⟩; exact hV.2 (i,t);exact hU.2 (i,t)
 have ht(t:foil G):|drift X U (jab (hot w) i t)|≤C:=by
    apply (he _).trans (mul_le_mul_of_nonneg_left _ hV.1)
    refine ((hustle_in hS (abroad_nn _) (steep w i t)).trans (hustle_plus hS hr (by norm_num))).trans ?_
    apply mul_le_mul_of_nonneg_left _ (hustle_nn p δ hr)
    unfold hustle; rw [mul_one,mul_one];apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (by norm_num)
 rw [tip X U w i j]; apply (ledger_out (V:=drift X U ∘ jab (hot w) i) _ _ ht hC).trans
 apply (mul_le_mul_of_nonneg_right (ser_rank _ _ _) (pow_nonneg hC _)).trans_eq
 unfold C shifter; rw [show a*(hustle p δ r*hustle p 1 1)=(a*hustle p 1 1)*hustle p δ r from by ring,mul_pow]; ring

-- also fixed-order leading metric exact, no growth fence
abbrev grad (U:Nd G Cover→ℝ)(i:Ed G Cover):ℝ:= U (i.1+step (Quarry.back i.2.1), i.2.2)-U (i.1,i.2.2)
-- signed orientations, positive slots only.
def settle (w:G.El)(x:Ed G Cover→ℝ)(i:Ed G Cover):ℝ:= G.adjoint w (Carrel.heavy G (fun j=>x (i.1,i.2.1,j))) i.2.2
lemma settle_one (Y:Ed G Cover→ℝ):settle 1 Y=Y:=by funext i;rw [settle,G.adjoint_one];rfl
lemma incoming (i:Ed G Cover):tap 0 (gain w (kiosk X) (kiosk U) i)=settle w (X+grad U) i:=by
 rw [ksound,tap,PowerSeries.coeff_zero_eq_constantCoeff_apply,lead,hot_speed]
 unfold settle; apply congrArg (fun x: G.Color=>G.adjoint w x i.2.2);
 -- show input colors by ext
 ext t
 change Quarry.cost (kiosk (drift X U ∘ jab (Quarry.hot w) i)) (0,t) - Quarry.cost (kiosk (drift X U ∘ jab (Quarry.hot w) i)) (1,t) + Quarry.cost (kiosk (drift X U ∘ jab (Quarry.hot w) i)) (2,t) = X _ + grad U _
 unfold Quarry.cost jab Quarry.hot menu drift; dsimp only [kiosk];simp [grad];ring

-- powerseries tapes, triangular fees (lumped pitch) for ward.
def Mbound (a:J→Dig)(e:ℕ)(U:J→ℝ):Prop:=∀ k≤e,∀ i, |tap k (a i)|≤ U i
lemma fret_mul {a b:J→Dig}{t u:J→ℝ}(h:Mbound a e t)(hu:Mbound b e u)(hz:0≤t):Mbound (a*b) e (fun i=>(e+1:ℝ)*(t i*u i)):=by
 intro k hk j
 rw [tap,Pi.mul_apply,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk];apply (abs_sum_le_sum_abs _ _).trans
 have hy:0≤u j:= (abs_nonneg _).trans (hu 0 (by omega) j)
 apply (sum_le_sum (s:=range (k+1)) (g:=fun _=>t j*u j) (fun x hx=>?_)).trans
 · rw [sum_const,card_range,nsmul_eq_mul]; push_cast;exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hk 1) (mul_nonneg (hz j) hy)
 rw [abs_mul]; exact mul_le_mul (h x (by simp only [mem_range] at *;omega) _) (hu _ (by omega) _) (abs_nonneg _) (hz _)
lemma podMul (n:ℕ){s:Fin n→J→Dig}{U:J→ℝ}(h:∀ i,Mbound (s i) e U):Mbound (fun j:J=> ∏ i:Fin n, s i j) e (fun j=> ((e+1:ℝ)*U j)^n):=by
 induction n with
 | zero=> simp only [prod_of_isEmpty,pow_zero];intro k _ _; rw [tap,PowerSeries.coeff_one]; split_ifs <;> norm_num
 | succ n ih=>
   simp_rw [Fin.prod_univ_succ]; intro k hk u
   have hN:0≤U:=fun i=> (abs_nonneg _).trans (h 0 0 (by omega) _)
   exact (fret_mul (h 0) (ih (fun i : Fin n =>h i.succ)) hN _ hk u).trans_eq (by dsimp;ring)

def vendor (G:Gauge)(w:G.El)(p e:ℕ)(a:ℝ):ℝ:= (e+1:ℝ)*∑ k∈range (e+1),shifter G w p k a
lemma vendor_nn (p e:ℕ)(h:0≤a):0≤vendor G w p e a:=mul_nonneg (by positivity) (sum_nonneg fun _ _=>shift_nn w p _ h)
lemma fret_ward (he:0≤δ)(hu:δ≤1)(t:Bearing (stance (Loc G 1)) p δ a X)(s:Bearing (stance G.ColorIndex) p δ a U){k:ℕ}(hk:k≤e) (x:Tape n (Ed G Cover)):
  |tap k (fret (gain w (kiosk X) (kiosk U)) x)| ≤ vendor G w p e a ^ n * hustle p δ ((stance (Loc G 1)).cage x) ^ ((e+1)*n):=by
 let B:=∑ k∈range (e+1),shifter G w p k a
 let W (x:Tape n (Ed G Cover)):=B*hustle p δ ((stance (Loc G 1)).cage x) ^ (e+1)
 let V(i:Fin n)(x:Tape n (Ed G Cover)):= gain w (kiosk X) (kiosk U) (x i)
 have h(i:Fin n):Mbound (V i) e W:=by
    intro j hj y;let L:=stance (Loc G 1); let H:=hustle p δ (L.cage y)
    have hv:1≤H:= one_le_hustle _ he (L.cage_nn y)
    have hf:=shift_coin w he hu t s j (y i)
    apply hf.trans
    let z(k:ℕ):= shifter G w p k a;have hz(i):0≤z i:= shift_nn w p _ t.1
    apply mul_le_mul (single_le_sum (f:=z) (fun i _=>hz i) (mem_range.mpr (by omega : j<e+1)))
    · exact (pow_le_pow_left₀ (hustle_nn p _ (abroad_nn _)) (hustle_in he (abroad_nn _) (L.float _ _)) (j+1)).trans (pow_le_pow_right₀ hv (by omega))
    · exact pow_nonneg (hustle_nn p _ (abroad_nn _)) _
    exact sum_nonneg fun i _=>hz i
 apply (podMul n h k hk x).trans_eq; change ((e+1:ℝ)*(B*hustle p δ _ ^(e+1)))^n=( ((e:ℝ)+1)*B)^n*_; rw [←mul_assoc,mul_pow,pow_mul]
end YM.RG08.Flint
