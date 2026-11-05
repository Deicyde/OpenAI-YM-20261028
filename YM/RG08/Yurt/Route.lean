import YM.RG08.Yurt.Levy
/-! # Offset contribution for actual centered mean & engineering factor.
Apply across all cutoffs. Analytical estimate h horizon. Pre block strengthening. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior Skiff Trickle Steam
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{G:Gauge}{n p d e i:ℕ}{D C T B τ η σ δ s:ℝ}{L:Side}

lemma prep0 (G:Gauge)(l h d e n:ℕ)(s C σ η δ:ℝ)(hη:0<η)(hh:0<σ)(hc:0≤C)(hs:0< s)(hd:h+1≤d)(hr:n≤l+e)(hδ:0≤δ)(hz:δ≤1)(ht:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2):∃ D:ℝ,0 ≤ D ∧ ∀ {Q T T₀ B V τ:ℝ}(L:Side)(o:Site L)(M:Carrier.Lines L)(N:Kernel G.ColorIndex (Loc G 1))(K:Kernel (Loc G 1) (Loc G 1))(F:GrainS (Ed G Cover))(f:Pearl)(y:Tape n (Ed G Cover)),Odd L.val→Tutor L s C M G h→Tutor L s C M G 0→Crest L M N K→0≤τ→τ≤ s→τ/(L.val:ℝ)≤δ→ η*unitStep L ≤ σ/2 →RowCost s L N Q →0≤Q→Calls l F→Permit d l F →0≤T→0≤T₀→0≤B→0≤V → Minored G h n (F e n) B →(∀ k≤l+e,Sings (stance _) d hh (F e k) T) →Sings (stance _) d hh (F e n) T₀→(∀ a<e,∀ k≤l+a,Sings (stance _) d hh (F a k) V) →
 let u:=unitStep L
 ; |sonic (F e n) (aisle u (ahead L o) f) (fun i=>tender K (lift o) τ (y i))| ≤ D*(B+T₀*u^(h+1)+(Q+C)^n*V)*beam d hη f:=by
 have ht': (n:ℝ)*δ≤σ/2:=(mul_le_mul_of_nonneg_right (by exact_mod_cast hr.trans (Nat.le_mul_of_pos_left (l+e) (by omega))) hδ).trans ht
 obtain ⟨A',hA,H⟩:= lunch G h d n s C σ η δ hs.le hc hh hη hd ht'
 obtain ⟨F,hF,H'⟩:= spark_band G l e n h σ δ hh hδ hz ht hr
 let P:=Real.exp (4*s); let D:=A'+ F * P^n * Real.exp (4*η)
 refine ⟨D,by unfold D P;positivity,?_⟩
 intro Q T T₀ B V τ L o M N K S f y ho hM hM₀ he hsτ hτ hτ' hη' hN hQ hS hW hT hT₀ hB hV hSg hEh htt hEl u
 let x:=aisle u (ahead L o) f; let X(i:Fin n):=Yurt.full G o M τ (y i); let Z(i:Fin n):=tender N (lift o) τ (y i)
 have hp(i): Bearing (stance _) h δ ((Q+C)*Real.exp (4*s)) (X i):=by
    have hv:=tender_bearing (p:=h) hsτ hτ (hM₀ [] (by simp)) (div_nonneg hc (by positivity)) hτ' o (y i)
    simp only [List.length_nil,zero_add,pow_one] at hv
    apply hv.up (mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le)
    exact (div_le_self hc (Nat.one_le_cast.mpr L.property)).trans (le_add_of_nonneg_left hQ)
 have hx(i): Bearing (stance _) h δ ((Q+C)*Real.exp (4*s)) (Z i):= (tender_bearing hsτ hτ hN hQ hτ' o _).up (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc) (Real.exp_pos _).le)
 have h₀:= (H' X Z _ hp hx S d V T x hS hW hV hT hEl hEh).1; rw [prod_const,card_univ,Fintype.card_fin] at h₀
 have h₁:= H L o M (S e n) f y ho hM hsτ hτ hτ' hη' ((hW.price _ _).1) htt hT₀ hSg hB
 change |sonic _ x _| ≤ D*(B+T₀*u^(h+1)+(Q+C)^n*V)*beam d hη f
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
 have hz2:=mul_le_mul_of_nonneg_right ha' (show 0≤(B+T₀*u^(h+1))*β by positivity)
 change F*((Q+C)^n * P^n)*V*(β*b)+_≤_
 change F*((Q+C)^n * P^n)*V*(β*b)+A'*(B+T₀*u^(h+1))*β≤D*(B+T₀*u^(h+1)+(Q+C)^n*V)*β
 nlinarith only [hz1,hz2]
theorem trains0 (G:Gauge)(l h d e n:ℕ)(s C σ η δ:ℝ)(hη:0<η)(hh:0<σ)(hc:0≤C)(hs:0< s)(hd:h+1≤d)(hr:n≤l+e)(hδ:0≤δ)(hz:δ≤1)(ht:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hη':2*η ≤ s):∃ D:ℝ,0 ≤ D ∧ ∀ {Q T T₀ B V:ℝ}(L:Side)(o:Site L)(M:Carrier.Lines L)(N:Kernel G.ColorIndex (Loc G 1))(K:Kernel (Loc G 1) (Loc G 1))(F:GrainS (Ed G Cover)),Odd L.val→Tutor L s C M G h→Crest L M N K→(2*η)/(L.val:ℝ)≤δ→ η*unitStep L≤σ/2 → RowCost s L N Q →0≤Q→Calls l F→ Permit d l F →0≤T→0≤T₀→0≤B→0≤V → Minored G h n (F e n) B →(∀ k≤l+e,Sings (stance _) d hh (F e k) T) →Sings (stance _) d hh (F e n) T₀→(∀ a<e,∀ k≤l+a,Sings (stance _) d hh (F a k) V) →
 let u:=unitStep L
 ; Sings (stance _) d hη (ferry K (F e n) u (ahead L o) (lift o)) (D*(B+T₀*u^(h+1)+(Q+C)^n*V)):=by
 obtain ⟨D,hD,H⟩:=prep0 G l h d e n s C σ η δ hη hh hc hs hd hr hδ hz ht
 refine ⟨D*rate (Loc G 1) η ^ n,mul_nonneg hD (pow_nonneg (rate_nn ..) _),?_⟩
 intro Q T T₀ B V L o M N K F ho hu hP hq hm hN hQ he hW hT hT₀ hB hV hZ h₀ htt h₁ u
 let R:= (B+T₀*u^(h+1)+(Q+C)^n*V)
 have hr:0≤D*R:=by unfold R; have hu:0≤u:=(unitStep_pos L).le; positivity
 have hv(f y):= H L o M N K F f y ho hu (fun w hw=>hu w (by omega)) hP (show 0≤2*η by positivity) hη' hq hm hN hQ he hW hT hT₀ hB hV hZ h₀ htt h₁
 simp_rw [ferry_spin] at hv
 exact (show (D*rate (Loc G 1) η ^ n)*R=D*R*rate (Loc G 1) η ^ n from by ring).symm ▸ have_sings _ hη hr hv
lemma soar0 (G:Gauge)(l h d e n:ℕ)(s C σ η δ:ℝ)(hη:0<η)(hh:0<σ)(hc:0≤C)(hs:0< s)(hd:h+1≤d)(hr:n≤l+e)(hδ:0≤δ)(hz:δ≤1)(ht:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hη':2*η ≤ s):∃ D:ℝ,0 ≤ D ∧ ∀ {Q T T₀ B V:ℝ}(P:Patch)(K:KernelChoices)(b:Bed)(M:Carrier.Lines P.L)(N:Kernel G.ColorIndex (Loc G 1))(F:GrainS (Ed G Cover)),Odd P.L.val→Tutor P.L s C M G h→Crest P.L M N (Cell.plotted P K G b)→(2*η)/(P.L.val:ℝ)≤δ→ η*(unitStep P.L)≤σ/2→RowCost s P.L N Q →0≤Q→Calls l F→ Permit d l F →0≤T→0≤T₀→0≤B→0≤V → Minored G h n (F e n) B →(∀ k≤l+e,Sings (stance _) d hh (F e k) T) →Sings (stance _) d hh (F e n) T₀→(∀ a<e,∀ k≤l+a,Sings (stance _) d hh (F a k) V) →
 Sings (stance _) d hη (forecast P K b F h e n) (D*T₀*unitStep P.L+D*(P.L.val:ℝ)^h*((Q+C)^n*V+B)):=by
 obtain ⟨D,hD,H⟩:=trains0 G l h d e n s C σ η δ hη hh hc hs hd hr hδ hz ht hη'
 refine ⟨D,hD,?_⟩
 intro Q T T₀ B V P K b M N F ho hM hE hN hI hw hQ hW hP hT hT₀ hB hV hS he htt hm
 have hc':=unitStep_pos P.L
 let u:=unitStep P.L;let a:ℝ:=P.L.val; have ha:0<a:=by unfold a; positivity
 let R:=D*(B+T₀*u^(h+1)+(Q+C)^n*V)
 have Hx(o): Sings (stance _) d hη (spun P K b F o e n) R:=by
    rw [←fabled];exact H P.L o M N _ _ ho hM hE hN hI hw hQ hW hP hT hT₀ hB hV hS he htt hm
 have hu:a^h * (T₀*u^(h+1))=T₀*unitStep P.L:=by
    change a^h * (T₀*a⁻¹ ^ (h+1))=T₀*a⁻¹;rw [pow_succ,inv_pow];field_simp
 have hh:a^h*R=D*T₀*unitStep P.L+D*(P.L.val:ℝ)^h*((Q+C)^n*V+B):=by unfold R;unfold a at hu ⊢; linear_combination D * hu
 exact hh ▸ grouped P K b F hη _ (by unfold R u;positivity) Hx
end YM.RG08.Yurt
