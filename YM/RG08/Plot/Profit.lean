import YM.RG08.Plot.Carousel
/-!
# Propagation of mother path flags through annulus ages. Natural Λ fee.
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
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{z a:M→ℕ}{p:List M} {U V: J→ M→ ℕ→ BoardU D R G}{s q :M→ J→ℝ}{C B:J→ℝ}{φ:M→J→Profile D}{x:J→ E4}
abbrev hostB (b:J→Dial u)(z:High b 1) := z.lowT.waitP
structure Heatline (b:J→Dial u) where
   main : High b 0
   j:ℕ
   older: main.i≤ j
   roof: j < (b main.z).N
namespace Heatline
def warm (w: Heatline b): High b 1:=⟨w.main.z,w.j,w.main.heap.trans w.older,w.roof⟩
def baseL (w:Heatline b): Wall (hostB b) 0:=⟨w.warm,w.main.i,w.main.heap,w.older⟩
lemma dress (t:Heatline b): t.warm.z=t.main.z:=rfl
lemma book (s:Heatline b) : s.baseL.i=s.main.i:=rfl
lemma high_fee (X:Chain)(s:Heatline b): wallY X s.baseL=s.warm.glass X:= spend X s.warm.lowT
end Heatline
lemma cardB {Y α J:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]{A:J→Rooted Y α r}{v x y:J→ℝ} (h:Card (k+j) y v A x)(hp:0≤x): Card k y v A x:= by obtain ⟨B,hB,H⟩:=h.money; exact ⟨_,hB,fun i=> Ink.shrink (H i) (zero_le_one.trans (tailp (hp i))) (fun v=> pow_le_pow_right₀ (by have he:=hp i; change 1≤1+x i*girth v; exact le_add_of_nonneg_right (mul_nonneg he (by positivity))) (Nat.le_add_right ..))⟩
variable [Fintype M]
section sums
lemma Births (he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q)(hp:Mats p (fun i=> Dial.fee X (b i)) C B s φ)(hm:loadᵣ z p ≤ τ)(hA:∀ i∈p,z i ≤τ)(hδ:p.Nodup)(hd:∀ i,i∈p)(hv:Pines A u)(hE:e≤E)(x:J→E4):
    let P (N:J→ℕ)(V:J→M→ℕ→BoardU D R G)(c:Heatline b):= let t:=c.main; Town.season (-arcT X t.K t.i (x t.z)) (crystal X ν D' t.K (N t.z) (x t.z) p z a (preR b φ t) (V t.z) c.j t.i)
    Drum k (fun t=>glass X t.warm) (fun t=>defect X t.warm) (fun t=> accrues (q*s) p t.main.z * (material X t.warm)^l) (fun i=> P (fun j=>(b j).N) U i e r) (fun i=>P (fun j=>(b j).M) V i e r) (fun t=>material X t.main) := by
   intro P
   let p' (t:High b 1):= accrues (q*s) p t.z*(material X t)^l
   have ht(i):0 ≤ p' i:= mul_nonneg (pow_pr (q':=q*s) (fun i hi j=>mul_nonneg (hP.hint i hi _) (hp.zero i hi _)) _) (pow_nonneg (spanP_pos ..).le _)
   have hM(i)(hi : i≤E)(r):=site_birth he hP hp hm hA hδ hd hi x (r:=r)
   let C (i:High b 1):= extraD X ν D' i.K (b i.z).N (x i.z) p z a (preR b φ i) (U i.z) i.i
   let B (i:High b 1):= extraD X ν D' i.K (b i.z).M (x i.z) p z a (preR b φ i) (V i.z) i.i
   have hX i: Stone (loadᵣ z p) (C i):= innate (hP.main _) i.heap i.scope ..
   have hV i: Stone (loadᵣ z p) (B i):= innate (hP.side _) i.heap (lt_of_lt_of_le i.scope (b i.z).ripe) ..
   let c (i: High b 1):= hostB b i; let F' (i:High b 1):= x i.z
   have hv' := rowing he hv (stairsP X c High.K) (p:=p') (q:=defect X) (fun i=> le_of_eq (joust X i.a.lowT)) hX hV hm ht (fun i=>(gain_pos ..).le) (he':=fun i hi r=>?_) e hE r (x:=F') (b:=High.K) -- note Arbor positional
   · have hV := hv'.1.mold Heatline.baseL
     convert hV using 1 <;> first | rfl |(funext i; first|exact (Heatline.high_fee X i).symm|exact Eq.symm (scale_u X i.main))
   convert hM _ hi r using 1 <;> first| rfl| (funext i; first| exact spend X i.lowT|exact scale_u X i.lowT)
-- independent terminal contribution (pre-Wick)
lemma Merry (he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+j) E p z a U V q)(hp:Mats p (fun i=> Dial.fee X (b i)) C B s φ)(hE:e≤E)(x:J→E4) :
    let P (U:J→M→ℕ→BoardU D R G) (i:High b 0):= Town.season (-arcT X i.K i.i (x i.z)) (marchFull X i.K (x i.z) p a (preR b φ i) (U i.z) i.i)
    Drum k (glass X) (defect X) ((fun i=> accrues (q*s) p i.z) / material X ^ loadᵣ a p) (fun i=> P U i e r) (fun i=> P V i e r) (material X) := by
  intro W
  let M₀ j (i:High b 0):= φ j i.z; let M':= material X (b:=b) (n:=0)
  let p' j (i:High b 0):= (q*s) j i.z / (M' i)^(a j)
  have hh:0 ≤ R:=le_trans (by norm_num : (0:ℝ)≤1/2) h
  let F (U:J→M→ℕ→BoardU D R G) (j:M) (i:High b 0):= burned (a j) i.K i.i (M₀ j i) X (x i.z) (U i.z j i.i) -- M name
  have hg := MatFill (b:=b) 0 hp
  have hz j (hj:j∈p) n (hn:n≤E) r: Drum k (glass X) (defect X) (p' j) (fun i=>F U j i n r) (fun i=>F V j i n r) M':= by
     have hQ:= hP.prior j hj n hn r
     exact profile_s (x:=fun i=>x i.z) (a:=High.K) (ℓ:=High.i) hh (glint X b 0) (fun i=>hP.hint _ hj i.z) (fun i=>(gain_pos ..).le) (hg.spanH) (hg.space j hj) ⟨cardB hQ.first zero_le_one,cardB hQ.second zero_le_one,cardB hQ.funds zero_le_one⟩ (hg.zero j hj) (hg.mass j hj) (oneP X) (n:=a j)
  have h1 (i: High b 0): W U i= castF (fun j=>F U j i) p:= space_for (A:=z) (U:=fun j=> marchFi X i.K (x i.z) (a j) _ _ i.i) _ (fun j hj=> costs_f (hP.main _) j hj _ i.heap i.scope _ _)
  have h2 (i: High b 0): W V i=castF (fun j=> F V j i) p := space_for (A:=z) (U:=fun j=> marchFi X i.K (x i.z) (a j) _ _ i.i) _ (fun j hj=> costs_f (hP.side _) j hj _ i.heap (i.scope.trans ((b i.z).ripe)) _ _)
  simp_rw [h1,h2]; convert ledger_s (glint X b 0) (fun i=> (spanP_pos ..|>.le)) (fun i=> (gain_pos ..|>.le)) hz e hE r using 1
  funext i; rw [show (fun t:High b 0=> accrues (q*s) p t.z)= accrues (fun i=>(q*s) i ∘ High.z) p from (accrues_pull (v:=High.z (b:=b) (n:=0)) p (q*s) i.z).symm]; rw [← accrued_wP,← accrued_div]; rfl
end sums
end YM.RG08.Plot
