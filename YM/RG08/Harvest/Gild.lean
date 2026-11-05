import YM.RG08.Harvest.Fire
/-!
# Charges before and after evaluating full product center test
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Harvest
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings PowerSeries Taste Plot Plot.High MeasureTheory Finset
open scoped BigOperators Topology Real ContDiff Classical
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l N:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{p:List M}{a z:M→ℕ}{φ:M→J→ Profile D}{C B:J→ℝ}{q s:M→ J→ℝ}{W:J→ℕ}{hw:∀ i,Optic (b i) (W i)}
section furl
variable {A : ℝ}{U V:Rest→ Tale G}
lemma rip_bill (hP:1/2 ≤ R)(he:Via G k V)(hp:∀ i:Rest, cis E 1 (V i n r) A): cis E 1 (rip V hP D n r) A:= by
   let Q b i:= tailP E 1 b*‖V i n r b‖; let v:=rip V hP D n r
   have hQ b: Integrable (Q b) abide := Continuous.integrable_of_hasCompactSupport (continuous_const.mul ((generated he ..).norm)) ((isClosed_tsupport _).isCompact)
   have hh b : tailP E 1 b * ‖v b‖ ≤ ∫ i,Q b i ∂abide:= by
       unfold Q; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (holding (D:=D) (generated he n r b) hP|>.2) (zero_le_one.trans (tailp zero_le_one b))
   let t b:=tailP E 1 b*‖v b‖; have ht b : 0≤ t b:= mul_nonneg (zero_le_one.trans (tailp zero_le_one b)) (norm_nonneg _)
   have hS (s:Finset (Beads (Loc G 1) r)): ∑ b∈s,t b ≤ A:= by
      apply le_trans (sum_le_sum (fun i _=> hh i)); rw [← integral_finsetSum _ (fun i _=>hQ i)]
      refine (integral_mono (integrable_finsetSum s (fun b _=> hQ b)) (g:=fun i:Rest=> A) (integrable_const A) (fun i=>?_)).trans_eq (by simp)
      dsimp only; apply le_trans (Summable.sum_le_tsum s (fun j _=> (hp i).1 j) (hp i).2.1) ((hp i).2.2)
   exact ⟨ht,summable_of_sum_le ht hS, Real.tsum_le_of_sum_le ht hS⟩
lemma moonless (h:Via G k U)(hp:Via G k V): Via G k (U-V):= by rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact Via.plus _ _ h (hp.scale _)
lemma ripping_L (h:1/2≤R)(hp:Via G τ U)(hv:Via G τ V): rip (U-V) h D=rip U h D-rip V h D:= eq_sub_of_add_eq (by rw [← ripping h (moonless hp hv) hv, sub_add_cancel])
variable {V U:J→ Rest→ Tale G}{y η δ:J→ℝ}
lemma pane (h:1/2≤R)(hp:∀ i,Via G τ (U i))(hx:Audience y)(hh:0≤δ)(he:Card k (y∘Prod.fst) (δ∘Prod.fst) (fun i:J×Rest=> U i.1 i.2 n r) 1): Card k y δ (fun i=> rip (U i) h D n r) 1 := by
   obtain ⟨A,⟨B,z,hB,H⟩,hV⟩:=he.money; -- need 0≤δ
   refine ⟨fun i=>B*y i ^z, (Weighed.constant y hB).times (Weighed.power y hx z),fun i=> rip_bill h (hp i) (fun j=> Ink.raise (hV (i,j)) (mul_le_mul_of_nonneg_right (H (i,j)|>.2) (hh i)))⟩
lemma pane_d (h:1/2≤R)(hp:∀ i,Via G τ (U i))(ht:∀ i,Via G τ (V i))(hx:Audience y)(hh:0 ≤ δ)(hη:0 ≤ η)(he:Drum k (y∘Prod.fst) (η∘Prod.fst) (δ∘Prod.fst) (fun i:J×Rest=>U i.1 i.2 n r) (fun i=>V i.1 i.2 n r) 1): Drum k y η δ (fun i=>rip (U i) h D n r) (fun i=>rip (V i) h D n r) 1:= by
   refine ⟨pane h hp hx hh he.first, pane h ht hx hh he.second,?_⟩
   rw [show _-_=(fun i=>rip (U i-V i) h D n r) from funext fun i=>?_]; · exact pane h (fun i=>moonless (hp i) (ht i)) hx (fun i=>mul_nonneg (hη i) (hh i)) he.funds
   rw [Pi.sub_apply,ripping_L h (hp i) (ht i)]; rfl
end furl
section energy
lemma arc_bound (k i x): size (arcT X k i ((spanP X k i) • (x:Rest).val))≤4:= by
   let s:=spanP X k i; have hp:0 < s:=spanP_pos ..; let t:=arcT X k i (s • x.val)
   have ht j : (t j).natAbs ≤1:= by
      have he : |x.val j| ≤ 1/2:= x.property j; have ⟨h1,h2⟩:= inBlock X k i (s•x.val) j; change -(1/2:ℝ) < (s*x.val j)/s-t j at h1; change s*x.val j/s - t j≤ _ at h2
      rw [mul_div_cancel_left₀ _ hp.ne'] at h1 h2
      exact_mod_cast (show ((t j).natAbs:ℝ) ≤ 1 from by rw [← Plot.signed_norm,Real.norm_eq_abs]; apply abs_le.mpr; obtain ⟨hA,hB⟩:= abs_le.mp he; constructor <;> linarith)
   exact (Finset.sum_le_sum (s:=univ) (fun j _=> ht j)).trans_eq (by simp [Axis])
lemma inbounds {U V:I→ Tale G}{X:I→ Cover}{y B C:I→ℝ}(hz:∀ i,size (X i) ≤ 4)(hp:Audience y)(he:Drum k y B C (fun i=> Town.season (-(X i)) (U i) n r) (fun i=> Town.season (-(X i)) (V i) n r) 1): Drum k y B C (fun i=> U i n r) (fun i=>V i n r) 1:= by
   have hv := roam_enough (z:=X) (k:=k) (b:=0) he (η:=1) zero_le_one le_rfl ?_ hp -- name V coll
   · convert hv using 1 <;> (
       ext1 i; rw [show ∀ V:I→Tale G,roam (X i) (Town.season (-X i) (V i) n r) = V i n r from ?_]; intro v; have he:= season_c (X i) (- X i) (V:=v i); rw [add_neg_cancel] at he; exact (congr_fun (congr_fun he n) r).trans (funext fun j=> congr_arg (v i n r) (funext fun k=>by change shiftedBy (-0) j k=j k; simp [shiftedBy])))
   exact (Weighed.constant y (show 0 ≤ (4:ℝ) by norm_num)).mono (fun i=>mul_nonneg zero_le_one (Nat.cast_nonneg _)) (fun i=>by simp only [Pi.one_apply,one_mul]; exact_mod_cast hz i)
end energy
end YM.RG08.Harvest
