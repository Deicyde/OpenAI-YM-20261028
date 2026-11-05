import YM.RG08.Harvest.Vein
/-!
# Real-continuous top motion paid exactly
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Harvest
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings PowerSeries Taste Plot Plot.High
open scoped BigOperators Topology Real ContDiff Classical
variable {I W:Type}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l N:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
section style
variable [TopologicalSpace W][CompactSpace W]{p:ℝ}
lemma map_gate (f:W→ E4)(hf: Continuous f)(g:Profile D) (X:Chain)(k i:ℕ)(h:0≤R): ∃ s:Finset Cover,∀ x,blush g X k i (f x) R⊆ s:= by
   obtain ⟨z,hz⟩:= (Metric.isBounded_iff_subset_closedBall 0).mp ((isCompact_range hf).isBounded); obtain ⟨B,hB,hQ⟩:= spatialComing g.val g.property
   let Z:=spanP X k i; have hZ:0 < Z:=spanP_pos ..; have he x : ‖f x‖≤ z:= by simpa using hz (Set.mem_range_self x)
   -- center root rounding
   let m:=Nat.ceil (z/Z+1); let n' := circleP B R Z
   have hp x (v:Axis) : ((arcT X k i (f x) v):ℤ).natAbs≤m:= by
     obtain ⟨hG,hH⟩:= inBlock X k i (f x) v
     let t := arcT X k i (f x); have hv: |f x v/Z| ≤ z/Z:= by rw [abs_div,abs_of_pos hZ]; exact div_le_div_of_nonneg_right ((PiLp.norm_apply_le ..).trans (he x)) hZ.le
     obtain ⟨ha,hb⟩:= abs_le.mp hv
     apply Nat.cast_le (α:=ℝ)|>.mp; refine le_trans ?_ (Nat.le_ceil _); rw [← signed_norm,Real.norm_eq_abs]; apply abs_le.mpr; unfold Z at *; constructor <;> linarith
   refine ⟨box (n'+m),fun x i hi=>?_⟩ -- i shadow
   rw [box_test]; constructor <;> (intro v; have hw:=hp x v; have he:= extent_p hQ (blush_v.mp hi) v; rw [Pi.sub_apply] at he; dsimp only [m,n',Z] at *; omega)
variable {U V:Tale G}{x:W→ E4}{B:ℕ→BoardU D R G}
lemma collectivity (g:Profile D)(X:Chain)(k n:ℕ)(h:0≤ R)(hx:Continuous x)(he:∀ (z: Cover),Via G d (fun i=> unitA X t k n g.val (x i) (B n) z)) : Via G d (fun i:W=> collect X t k n g (x i) (B n)):= by
   obtain ⟨v,hv⟩:= map_gate x hx g X k n h
   rw [show (fun i=>collect X t k n g (x i) (B n))=(fun i=>∑ t'∈v,stemU X t k n g.val (x i) (B n) t') from ?_]  
   · exact Via.sum v (F:=fun z i=>stemU X t k n g.val (x i) (B n) z) fun i _=> Via.moves (he i) i
   exact funext fun i=> Finset.sum_subset (hv i) fun j hj ht=> by unfold stemU; rw [Plot.owed g ht]; rfl
lemma power_top (U:Native (Letter F))(K N:ℕ)(X':Chain) (b:ℕ)(hp:Ω.Sound H)(hc:Bid.pop Ω)(g:Profile D)(hx:Continuous x): Via G d (fun j:W => marchFi X K (x j) d g (fun n=>Plot.masters X ν D' T N K n U) N):= by
   refine collectivity g X K N (B:=fun n=>Plot.masters X ν D' T N K n U) (le_trans (by norm_num : (0:ℝ)≤1/2) h) hx (?_ : ∀ v, Via G d (fun i=> unitA X d K N g.val (x i) (Plot.masters X ν D' T N K N U) v))
   intro v
   simp only [masters,step_top]; exact Via.scale (tariff d (spanP X K N)) ( book_incomes H Ω hp hc _ h g.val x hx (0:E4) v _ _)
end style
section result
variable {J M:Type}{u:I→Windows}{b:J→ Dial u}{A:M→ℕ}{p:List M}
variable {hT:∀ i, A i+1≤ D} {K:∀ i,Labels.Frame G (A i)}{Φ:∀ i,SectionData (K i)} {V:∀ i:M, Signals P Q E τ H (Φ i) h (hT i)}
lemma top_bill (φ:M→J→Profile D)(U:∀ i:M,J→ Native (Letter (K i)))(p:List M){B:J→ℕ}(he:∀ i, Optic (b i) (B i))(j:J) (hp:Tights T S ν D' u)(hh:∀ i∈ p,Tights (V i) S ν D' u) [TopologicalSpace W][CompactSpace W](x:W→E4)(hx:Continuous x): Via G (loadᵣ A p) (fun i=> field_at X ν D' b (deckR X ν D' V U b) p A A φ (fun _=>x i) j (B j)) := by
   let N:=(b j).N; have hv:B j≤N:=(he j).2.trans (b j|>.main)
   refine preserve_dust (F:=fun i=> marchFull X (b j).K (x i) p A (fun i=>φ i j) (deckR X ν D' V U b j) N) ?_ hv (fun i hi hz=> hp.fair ⟨⟨(b j).a,i,(he j|>.1).trans hi⟩,N,(b j).M,hz,(b j).ripe⟩)
   exact Via.service (a:=A) (u:=p) (fun i hi=> power_top (T:=V i) (U i j) ((b j).K) N X (B j) (hh i hi|>.sound) (hh i hi|>.pop) (φ i j) hx)
end result
end YM.RG08.Harvest
