import YM.RG08.Plot.Wave
/-!
# Budgets through UV wing on all finite profile geometry caps
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings High
open scoped BigOperators Topology Real ContDiff Classical
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{z a:M→ℕ}{p:List M} {U V: J→ M→ ℕ→ BoardU D R G}{s q :M→ J→ℝ}{C B:J→ℝ}{φ:M→J→Profile D}{x:J→ E4}
variable [Fintype M]
section calls
local notation "♭" => High.glass X (n:=0)
local notation "♯" => High.defect X (n:=0)
local notation "♠" => fun i : High b 0=> -arcT X i.K i.i (x i.z)
lemma extend_ (he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q)(hp:Mats p (fun i=> Dial.fee X (b i)) C B s φ)(hm:loadᵣ z p ≤ τ)(hA:∀ i∈p,z i ≤τ)(hδ:p.Nodup)(hd:∀ i,i∈p)(hv:Pines A u)(hE:e≤E)(h0:1≤ l) (x:J→E4):
    let V' (N:J→ℕ)(U:J→M→ℕ→BoardU D R G)(i:High b 0):= ∑ j∈Ico i.i (N i.z),Town.season (-arcT X i.K i.i (x i.z)) (crystal X ν D' i.K (N i.z) (x i.z) p z a (preR b φ i) (U i.z) j i.i)
    Drum k ♭ ♯ (fun i=> accrues (q*s) p i.z * material X i ^l) (fun i=> V' (fun j=>(b j).N) U i e r) (fun i=> V' (fun j=>(b j).M) V i e r) (material X) := by
   intro V'; let P (U:J→M→ℕ→BoardU D R G)(b:J→Dial u)(N:J→ℕ)(i:High b 0) j:= Town.season (-arcT X i.K i.i (x i.z)) (crystal X ν D' i.K (N i.z) (x i.z) p z a (preR b φ i) (U i.z) j i.i) e r
   let N i:=(b i).N; let M i:=(b i).M
   let U':=P U b N; let T':=P V b M; let w := accrues (q*s) p; have hz:0≤w:=pow_pr fun i hi j=> mul_nonneg (hP.hint _ hi _) (hp.zero _ hi _)
   have hr:= stemsG (N:=U') (M:=T') (w:=w) h0 (Births he hP hp hm hA hδ hd hv hE x) hz
   let B:= Births he hP.bothM (p:=p) (show Mats p (fun i=> Dial.fee X (rightT b i)) _ _ _ _ from hp) hm hA hδ hd hv hE x (r:=r)
   let C i:= ∑ j∈Ico (N i.z) (M (High.z (b:=b) (n:=0) i)),T' i j; let W i:= ∑ j∈Ico i.i (N (High.z (b:=b) (n:=0) i)), T' i j
   let g (i:High b 0):= w i.z * material X i^l
   have hC : Card k ♭ (♯ *g) C (material X):= by
      refine fore (w:=w) h0 T' (fun i=>P V (rightT b) M i.main i.j) B.first ?_ hz
      intro i j ht v he h1 h2
      unfold T' P; change _=Town.season (-arcT X (b v.main.z).K v.main.i (x v.main.z)) (crystal X ν D' (b v.main.z).K _ _ _ _ _ (fun j=>φ j v.main.z) _ _ _) e r; rw [h1,h2,he]
   have hz':(fun i=> V' M V i e r)=W+C:= by
      funext i; unfold V'; rw [Finset.sum_apply,Finset.sum_apply]; exact (Finset.sum_Ico_consecutive (T' i) i.scope (b i.z).ripe).symm
   rw [show (fun i=> V' (fun j=> (b j).M) V i e r)=_ from hz',show (fun i=> V' N U i e r)= _ from (funext fun i=>by simp [V',Finset.sum_apply]; rfl:(fun i=> V' N U i e r)=(fun i=>∑ j∈Ico i.i (b i.z).N,U' i j))]
   have hg:0 ≤ material X (n:=0) (b:=b):= fun i=>spanP_pos ..|>.le
   refine ⟨hr.first,?_,?_⟩
   · exact (hr.second).more (U:=W) (hC.raise (fun i=> mul_le_of_le_one_left (mul_nonneg (hz i.z) (pow_nonneg (hg _) l)) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr (age_scale_mono _ (appr i).cut)))))) hg (glint X b 0)
   rw [sub_add_eq_sub_sub]; exact Card.less hr.funds hC hg (glint X b 0)
lemma gather (he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q)(hp:Mats p (fun i=> Dial.fee X (b i)) C B s φ)(hm:loadᵣ z p ≤τ)(hA:∀ i∈p,z i ≤τ)(hδ:p.Nodup)(hd:∀ i,i∈p)(hv:Pines A u)(hE:e≤E)(h0:1≤l)(x:J→E4):
   let W (N:J→ℕ)(V:J→M→ℕ→BoardU D R G)(i:High b 0):= Town.season (-arcT X i.K i.i (x i.z)) (waveProduct X ν D' i.K (N i.z) (x i.z) p z a (preR b φ i) (V i.z) i.i)
   Drum k ♭ ♯ ((fun i=> accrues (q*s) p i.z)/material X^loadᵣ a p) (fun i:High b 0=> W (fun j=>(b j).N) U i e r) (fun i=> W (fun j=>(b j).M) V i e r) (material X) := by
   intro W; let y:= accrues (q*s) p; let Q := Merry he hP hp hE x (r:=r)
   have H:= extend_ he hP hp hm hA hδ hd hv hE h0 x (r:=r)
   let p' i := y (High.z (b:=b) (n:=0) i) /material X i ^loadᵣ a p; have hq:0≤ p':= fun i=> div_nonneg (pow_pr (q':=q*s) (fun i hi j=>mul_nonneg (hP.hint i hi _) (hp.zero i hi _)) _) (pow_nonneg (spanP_pos ..|>.le) _)
   have ht(i: High b 0): (accrues (q*s) p i.z)*material X i^l ≤ p' i:= by
     have hb':= oneP X (b:=b) i; have hY : 0< material X i:= spanP_pos ..
     have hr :0 ≤ y i.z:= pow_pr (q':=q*s) (fun i hi j=> mul_nonneg (hP.hint _ hi _) (hp.zero _ hi _)) _
     unfold p'; apply (le_div_iff₀ (pow_pos hY _)).2; rw [mul_assoc]; exact mul_le_of_le_one_right hr (mul_le_one₀ (pow_le_one₀ hY.le hb') (pow_nonneg hY.le _) (pow_le_one₀ hY.le hb'))
   have hm':= Plot.Drum.loosen (w:=p') H ht (fun i=>(gain_pos ..).le)
   have h1 i:= serve (x:=x i.z) (φ:=preR b φ i) (hP.main i.z) (High.heap (b:=b) (n:=0) i) i.scope; have h2 i:=serve (x:=x i.z) (φ:=preR b φ i) (hP.side i.z) (High.heap (b:=b) (n:=0) i) (i.scope.trans ((b i.z).ripe))
   dsimp only [W]
   simp_rw [show ∀ i:High b 0,waveProduct X ν D' i.K (b i.z).N (x i.z) p z a (preR b φ i) (U i.z) i.i=_ from h1,show ∀ i:High b 0,waveProduct X ν D' i.K (b i.z).M (x i.z) p z a (preR b φ i) (V i.z) i.i=_ from h2]
   have hs {F V:Tale G}(x:Cover): Town.season x (F+V)=Town.season x F+ Town.season x V:=rfl
   simp_rw [hs, season_group, Pi.add_apply]; exact Q.more hm' (fun i=>(spanP_pos ..).le) (glint X b 0)
end calls
end YM.RG08.Plot
