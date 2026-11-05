import YM.RG08.Creek.Loans
/-! # Post charges on explicit chain. Provision *before block size*. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {X:Chain} {G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}
section before
variable {κ:KernelChoices}{P:KPrices κ}{Q:Lending G κ}
variable {h:1/2≤R}{hD:d+1≤D} (T:Signals P Q E τ H Ω h hD)(I:Type)[Fintype I]
-- chosen prior to L and roots of narrative. extra exponential $2$ each step, AND T.w supports primary.
abbrev secretT (j:ℕ) : ℝ:= ((2:ℝ)*(parPort I τ:ℝ)^(windows τ E))⁻¹*T.wi j
lemma secret_t (j:ℕ): 0< secretT T I j:= mul_pos (inv_pos.mpr (mul_pos (by norm_num) (pow_pos (port_pos ..) _))) (T.pos j)
lemma secret_b (j:ℕ): advanceFee I τ (2 * secretT T I j) (windows τ E)=T.wi j:= by
    unfold advanceFee secretT; have hp : (parPort I τ:ℝ) ≠ 0:=(port_pos I τ).ne'; field_simp
lemma secret_l (j: ℕ): 2*secretT T I j ≤ T.wi j:= by rw [← secret_b T I j]; simpa only [advanceFee,pow_zero,one_mul] using advance_v I (mul_nonneg (show (0:ℝ)≤2 by norm_num) ((secret_t T I j).le)) (Nat.zero_le (windows τ E)) (t:=τ)
lemma windGate : ∃ U:ℕ→ℕ, ∀ i j:ℕ,∀ f:Flight j i, U j≤ f.L.val → T.wi i ≤ f.L.val * secretT T I j:= by
    choose p hP using fun i j=> exists_nat_gt ((T.wi i)/(secretT T I j))
    refine ⟨fun i=>max (p i i) (p (i-1) i),fun i j f hf=>?_⟩
    have hh: p i j ≤ f.L.val:= by
       by_cases h:i=j; · subst j; exact (le_max_left ..).trans hf
       have hx:j-1=i:=by have ht:= f.narrow; have hp:=f.mono;omega
       dsimp only at hf; rw [hx] at hf; exact (le_max_right ..).trans hf
    exact (div_le_iff₀ (secret_t T I _)).1 ((hP i j).le.trans (Nat.cast_le.mpr hh))
end before
variable {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1 ≤ D}{T:Signals P Q E τ H Ω h hD}
variable {I J:Type} [Fintype I][DecidableEq I]{u:J→Windows}
open Wings

def Ripple (T:Signals P Q E τ H Ω h hD)(u:J→ Windows)(I:Type)[Fintype I]:Prop:= ∀ x:Launch u, T.wi (X.J x.i) ≤ ((X.S.block x.i).val:ℝ)*secretT T I (X.J (x.i+1))
lemma ripens {T:Signals P Q E τ H Ω h hD} (h:∀ x:Launch u, (windGate T I).choose (X.J (x.i+1)) ≤ ((X.S.block x.i).val)): Ripple T u I := fun x=> (windGate T I).choose_spec _ _ (X.flight 0 x.i) (h x)

abbrev scoreW (T:Signals P Q E τ H Ω h hD)(I:Type)[Fintype I](i:ℕ):= secretT T I (X.J i)
lemma wind_inv (he:Enabled T u)(I:Type)[Fintype I] : Weighed (Launch.farY X) (fun i:Launch u=>(scoreW T I i.i)⁻¹):= by simp_rw [scoreW, secretT,mul_inv_rev,inv_inv]; exact he.costs.times (Weighed.constant _ (mul_nonneg (by norm_num) (by positivity)))
abbrev rallyW (L:Side)(e:ℕ):ℝ:= (L.val:ℝ)^e /(Fintype.card (Site L):ℝ)
abbrev vaneW (X:Chain)(a:I→ℕ)(i:ℕ)(p:I):= rallyW (X.S.block i) (a p)
lemma wheel_cash (he: Tights T S ν D' u)(b:I→ℕ)(p:I): Weighed (menu X) (fun i:Wings u 1=> ‖vaneW X b i.i p‖) := by
   have hp:Weighed (menu X) (fun t: Wings u 1=> (↑(X.S.block t.i).val:ℝ)):=he.operator.crop
   refine (hp.powers (b p)).mono (fun i=> norm_nonneg _) (fun i=>?_); unfold vaneW rallyW; dsimp only; rw [Real.norm_of_nonneg (by positivity)]; exact div_le_self (by positivity) (Nat.one_le_cast.mpr (Fintype.card_pos))
lemma seasonal (h:Tights T S ν D' u) (k:Wings u 1) : Climate (heights X ν D' k) := ⟨h.fair k, authentic h.hv ν D' _ k.N⟩
-- primitive with reserve. output at 2X, needed support use
lemma seasonal_bill (hC:Tights T S ν D' u)(hk:Ripple T u I)(b:I→ℕ):
    ∃ A:Wings u 1→ℝ, Weighed (menu X) A ∧ ∀ (i:Wings u 1)(F:Layouts I G D R)(p:Head I)(a:I→ℕ), Sense a F →(∀ t, vanes a t+E≤τ)→ Crease p →Fest (scoreW T I (i.i+1)) E 1 p F →Fest (2*scoreW T I i.i) E (A i) p (creekT (heights X ν D' i) a (vaneW X b i.i) F):= by
   apply creek_univ hC.operator (fun i=> mul_pos (show (0:ℝ)<2 by norm_num) (secret_t ..)) (fun i=> (secret_b ..).trans_le (tick_t T _).1) _ (fun i=> (secret_b ..).trans_le (hk i.toLaunch)) (wheel_cash hC b) h
   simpa only [Wings.menu,scoreW,secretT,mul_inv_rev] using! (show Weighed (menu X (r:=1) (u:=u)) (fun i=>(scoreW T I i.i)⁻¹*(2:ℝ)⁻¹) from  ((wind_inv hC.he I).transfer toLaunch).times (Weighed.constant _ (show 0≤(2:ℝ)⁻¹ by norm_num)))
end YM.RG08.Creek
