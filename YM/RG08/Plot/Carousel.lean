import YM.RG08.Plot.Flares
/-! # Assembled tested fees. As high or low as needed on measurement+ segment -/
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
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E E' e r d τ D j t l:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{z a:M→ℕ}{p:List M} {U V: J→ M→ ℕ→ BoardU D R G}{s q :M→ J→ℝ}{C B:J→ℝ}{φ:M→J→Profile D}{x:J→ E4}
-- pol costs on inputs with supports. top master normalization can use independent residuals.
structure Fleece (T:Signals P Q E τ H Ω h hD)(b:J→Dial u)(ν:G.ColorIndex)(D':ChartRatio G)
   (k E':ℕ)(p:List M)(z a:M→ℕ)(U V : J→ M→ℕ→ BoardU D R G)(q :M→ J→ℝ) : Prop where
  main : ∀ i:J,Scenes X ν D' (b i).K (b i).N p z a (U i)
  side : ∀ i:J,Scenes X ν D' (b i).K (b i).M p z a (V i)
  hint : ∀ j∈p,0≤q j
  prior : ∀ i∈p,∀ j≤ E',∀ r, Drum k (glass X) (defect X) (fun t=>q i t.z) (fun t:High b 0=> U t.z i t.i j r) (fun t=>V t.z i t.i j r) 1
  assets : ∀ i∈p,∀ j≤E',∀ r, Card k (glass X) (fun t=>q i t.z) (fun t:High (rightT b) 0=> V t.z i t.i j r) 1
lemma Fleece.bothM (hp: Fleece T b ν D' k E' p z a U V q): Fleece T (rightT b) ν D' k E' p z a V V q:=⟨hp.side,hp.side,hp.hint,fun i hi j hj r=>Drum.home (hp.assets i hi j hj r),hp.assets⟩ -- E'
section saving
variable [Fintype M]
local notation "Γ" => heights (u:=u) X ν D'
local notation "⊖" => fun i : High b 1=> shrinkP X i.K i.i (x i.z)
lemma MatFill (n:ℕ)(hp:Mats p (fun i=> Dial.fee X (b i)) C B s φ): Mats p (glass X (b:=b) (n:=n)) (fun i=> C i.z) (fun i=> B i.z) (fun j i=> s j i.z) (fun j i=> φ j i.z):= ⟨(here_bill X).sway (glint X b n) (hp.spanH.transfer High.z), (here_bill X).sway (glint X b n) (hp.bill.transfer High.z),fun j hj t=>hp.zero j hj _,fun i hi j=>hp.space i hi _,fun i hi j=> hp.mass i hi j.z,fun i hi j hj t=> hp.split i hi j hj _⟩
-- preserve read and input norms trans-poly
abbrev preR (b:J→Dial u) (φ:M→J→Profile D)(t:High b n):= fun j=>φ j t.z
local notation "⚡" => preR b φ
lemma site_birth (he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q)(hp:Mats p (fun i=>Dial.fee X (b i)) C B s φ)(hm:loadᵣ z p ≤ τ)(hA: ∀ i∈p,z i ≤τ)(hδ:p.Nodup)(hd:∀ i,i∈p)(hE : e ≤E)(x:J→E4) :
   Drum k (glass X) (defect X) (fun i=> accrues (q*s) p i.z * (material X i)^l) (fun i:High b 1=> Town.season (-arcT X i.K i.i (x i.z)) (extraD X ν D' i.K (b i.z).N (x i.z) p z a (⚡ i) (U i.z) i.i) e r) (fun i=> Town.season (-arcT X i.K i.i (x i.z)) (extraD X ν D' i.K (b i.z).M (x i.z) p z a (⚡ i) (V i.z) i.i) e r) (material X):= by
   let E' j i:=U i.z j (High.i (b:=b) (n:=1) i+1); let F' j i:= V i.z j (High.i (b:=b) (n:=1) i+1)
   let s₀(t:High b 1):= Γ t.appr; let s₁(t:High b 1):=Γ t.appr.wingR
   let H:= loadᵣ a p; let w := material X (b:=b) (n:=1); let v(t:High b 1):= spanP X t.K (t.i+1)
   let L i:=((X.S.block (High.i (b:=b) (n:=1) i)).val:ℝ)
   simp only [fun (i: High b 1)=> drift_moves
             (x:=x i.z) (φ:=⚡ i) (hP.main i.z) i.heap (show i.i < (b i.z).N from i.scope),fun (i:High b 1)=> drift_moves (x:=x i.z) (φ:=⚡ i) (hP.side _) i.heap (show i.i < (b i.z).M from i.scope.trans ((b i.z).ripe))]
   have ht j : LensP j E τ (glass X) (defect X) _ s₀ s₁:= drum_w (kitchen he j) High.appr
   let p' j (i:High b 1):= q j i.z; let b' j (i:High b 1):= s j i.z
   apply Drum.cheap (p:=L^H) _ ((ht 0).pay.powers H)
   have hM:=Accum (a:=High.K) (ℓ:=High.i) (P:=s₀) (Q:=s₁) (U:=E') (V:=F') (MatFill 1 hp) h hδ hd hm hA (fun j hj i=> (hP.main _).heads j hj (i.i+1) (i.heap.trans (Nat.le_succ _)) i.scope) (fun j hj i=>(hP.side _).heads j hj (i.i+1) (i.heap.trans (Nat.le_succ _)) (i.scope.trans ((b i.z).ripe))) (b:=H+l) (ht (k+(H+l))) (ht (H+l)) (ht k) (fun i=> authentic he.hv ν D' i.i (b i.z).N) (fun i=> authentic he.hv ν D' i.i (b i.z).M) (t':=p') (fun i hi v=>hP.hint i hi v.z) (fun j hj n hn k=> helms he (hP.hint j hj) (V:=fun t:High b 0=>V t.z j t.i n k) (hP.prior j hj n hn k)) (oneP X) hE (fun i=>x i.z) (h:=a) (r:=r) -- name conflicts K refs and a
   convert hM using 1
   rotate_left; all_goals try rfl
   funext i
   have hx : w i=v i * L i:= (spanP_tick X i.K i.i).symm; have he:0<v i:= spanP_pos ..; have hC: accrues (fun j (i:High b 1)=> q j i.z * s j i.z) p i= accrues (q*s) p i.z:= congr_fun (accrues_pull p (q*s) i.z High.z) i
   change L i ^ H* (accrues (q*s) p i.z* (w i)^l)= accrues _ p i /v i^H * w i^(H+l)
   rw [← hC,hx]; change _=accrues (fun j (i:High b 1)=> q j i.z*s j i.z) p i/(v i)^H*(v i*L i)^(H+l); rw [pow_add, mul_pow]; field_simp; rw [mul_pow]; ring
end saving
end YM.RG08.Plot
