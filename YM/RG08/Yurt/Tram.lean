import YM.RG08.Yurt.Ferry
/-! # Deterministic estimate including gauge correction. Dual anchored cost
pre energy factor. F's Permit & Sworn/Calls at all levels BEFORE needed. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior Skiff
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{G:Gauge}{n p d e i:ℕ}{D C T B τ η σ δ s:ℝ}{L L':Side}
local notation "A" => Loc G 1
local notation "sV" => Nd G Cover
local notation "eV" => Ed G Cover

def tender (K:Kernel I J)(o:Cover)(τ:ℝ)(y:Market J)(z:Market I):ℝ:= offer K o τ y z.1 z.2
lemma tender_bearing {K:Kernel I J}(ht:0≤τ)(hs:τ ≤ s)(h:RowCost s L K C)(hc:0≤C)(hu:τ/(L.val:ℝ)≤δ)(o:Site L)(y:Market J):
 Bearing (stance I) p δ (C*Real.exp (4*s)) (tender K (lift o) τ y):= ((show Bearing (stance I) 0 (τ/(L.val:ℝ)) (C*Real.exp (4*s)) (tender K (lift o) τ y) from by
    constructor
    · exact mul_nonneg hc (Real.exp_pos _).le
    intro j
    rw [hustle,pow_zero,one_mul]; exact promote ht hs h hc o j.1 y j.2)).here hu (Nat.zero_le _)

def Crest (L:Side)(M:Carrier.Lines L)(P:Kernel G.ColorIndex A)(K:Kernel A A):Prop:=∀ (y:Market A)(z:eV),K z y=Ballet G L M [] z y+grad (fun s:sV=>P s y) z
lemma shaped {P:Kernel G.ColorIndex A}{K:Kernel A A}{M:Carrier.Lines L}(hc:Crest L M P K)(y:Market A)(τ:ℝ)(o:Site L):tender K (lift o) τ y=Yurt.full G o M τ y+grad (tender P (lift o) τ y):=by
 funext z;unfold Yurt.full; rw [tender,offer,hc y,Pi.add_apply,grad,grad]; unfold tender auction offer;dsimp only;rw [add_right_comm z.1];ring

/-- P family, h horizon (test letters), L still variable. Price D PRE on unchanged rank;
 nonlinear corrections may multiply lower by post Q^n involved in tree station.
B,χ projected lower costs & U,equal order all rank finite needed. Does not rely on positive
analytic outputs or connected group. -/
lemma prep (G:Gauge)(l h d e n:ℕ)(s C σ η δ:ℝ)(hη:0<η)(hh:0<σ)(hc:0≤C)(hs:0< s)(hd:h+1≤d)(hr:n≤l+e)(hδ:0≤δ)(hz:δ≤1)(ht:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2):∃ D:ℝ,0 ≤ D ∧ ∀ {Q T B V τ:ℝ}(L:Side)(o:Site L)(M:Carrier.Lines L)(N:Kernel G.ColorIndex (Loc G 1))(K:Kernel (Loc G 1) (Loc G 1))(F:GrainS (Ed G Cover))(f:Pearl)(y:Tape n (Ed G Cover)),Odd L.val→Tutor L s C M G h→Tutor L s C M G 0→Crest L M N K→0≤τ→τ≤ s→τ/(L.val:ℝ)≤δ→ η*unitStep L ≤ σ/2 →RowCost s L N Q →0≤Q→Calls l F→Permit d l F →0≤T→0≤B→0≤V → Minored G h n (F e n) B →(∀ k≤l+e,Sings (stance _) d hh (F e k) T) →(∀ a<e,∀ k≤l+a,Sings (stance _) d hh (F a k) V) →
 let u:=unitStep L
 ; |sonic (F e n) (aisle u (ahead L o) f) (fun i=>tender K (lift o) τ (y i))| ≤ D*(B+T*u^(h+1)+(Q+C)^n*V)*beam d hη f:=by
 have ht': (n:ℝ)*δ≤σ/2:=(mul_le_mul_of_nonneg_right (by exact_mod_cast hr.trans (Nat.le_mul_of_pos_left (l+e) (by omega))) hδ).trans ht
 obtain ⟨A',hA,H⟩:= lunch G h d n s C σ η δ hs.le hc hh hη hd ht'
 obtain ⟨F,hF,H'⟩:= spark_band G l e n h σ δ hh hδ hz ht hr
 let P:=Real.exp (4*s); let D:=A'+ F * P^n * Real.exp (4*η)
 refine ⟨D,by unfold D P;positivity,?_⟩
 intro Q T B V τ L o M N K S f y ho hM hM₀ he hsτ hτ hτ' hη' hN hQ hS hW hT hB hV hSg hEh hEl u
 let x:=aisle u (ahead L o) f; let X(i:Fin n):=Yurt.full G o M τ (y i); let Z(i:Fin n):=tender N (lift o) τ (y i)
 have hp(i): Bearing (stance _) h δ ((Q+C)*Real.exp (4*s)) (X i):=by
    have hv:=tender_bearing (p:=h) hsτ hτ (hM₀ [] (by simp)) (div_nonneg hc (by positivity)) hτ' o (y i)
    simp only [List.length_nil,zero_add,pow_one] at hv
    apply hv.up (mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le)
    exact (div_le_self hc (Nat.one_le_cast.mpr L.property)).trans (le_add_of_nonneg_left hQ)
 have hx(i): Bearing (stance _) h δ ((Q+C)*Real.exp (4*s)) (Z i):= (tender_bearing hsτ hτ hN hQ hτ' o _).up (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc) (Real.exp_pos _).le)
 have h₀:= (H' X Z _ hp hx S d V T x hS hW hV hT hEl hEh).1; rw [prod_const,card_univ,Fintype.card_fin] at h₀
 have h₁:= H L o M (S e n) f y ho hM hsτ hτ hτ' hη' ((hW.price _ _).1) (hEh _ hr) hT hSg hB
 change |sonic _ x _| ≤ D*(B+T*u^(h+1)+(Q+C)^n*V)*beam d hη f
 simp_rw [shaped he _ τ o]
 let β:=beam d hη f;have hβ:0≤β:=beam_nn ..
 have hu:0≤u:=(unitStep_pos L).le
 let b:= Real.exp (4*η)
 have HZ:beam d hh x ≤ β*b:=((Lagoon.spending (d:=d) (h:=hh) hη (ahead L o) u (by rw [abs_of_nonneg hu]; exact unitStep_le _) (by rw [abs_of_nonneg hu];linarith only [hη',hh]) f)).trans (by unfold β b;gcongr _*Real.exp ?_;have hh':=heading L o;nlinarith)
 have hf:=mul_le_mul_of_nonneg_left HZ (show 0≤F*((Q+C)*Real.exp (4*s))^n*V by positivity)
 have hX1:=h₀.trans hf
 rw [mul_pow] at hX1
 have htL:|sonic (S e n) x (fun i=>X i+grad (Z i))| ≤ |sonic (S e n) x (fun i=>X i+grad (Z i))-sonic (S e n) x X|+|sonic (S e n) x X|:=by
    nth_rw 1 [show sonic (S e n) x (fun i=>X i+grad (Z i))= sonic (S e n) x (fun i=>X i+grad (Z i))-sonic (S e n) x X+sonic (S e n) x X from by ring];apply abs_add_le
 apply htL.trans ((add_le_add hX1 h₁).trans ?_)
 have he': F*P^n*b≤D:=le_add_of_nonneg_left hA
 have ha':A'≤D:=le_add_of_nonneg_right (by unfold P;positivity)
 have hz1:=mul_le_mul_of_nonneg_right he' (show 0≤(Q+C)^n*V*β by positivity)
 have hz2:=mul_le_mul_of_nonneg_right ha' (show 0≤(B+T*u^(h+1))*β by positivity)
 change F*((Q+C)^n * P^n)*V*(β*b)+_≤_
 change F*((Q+C)^n * P^n)*V*(β*b)+A'*(B+T*u^(h+1))*β≤D*(B+T*u^(h+1)+(Q+C)^n*V)*β
 nlinarith only [hz1,hz2]
end YM.RG08.Yurt
