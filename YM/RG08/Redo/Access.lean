import YM.RG08.Redo.Scaling
/-! # One-paid public calendar on the actual thermal witness. Years unlimited. -/
noncomputable section
namespace YM.RG08.Redo
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open PhysicalNext PhysicalNext.Repeat Extraction Org Table Spec UVExtension MergeProof Next.Free Function Jetty Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow April Yurt Filter
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {O X:Type}(G:Gauge)(hg:G.Simple)(Z:ChartRatio G)(k:RG.KernelChoices)
local notation "T0"=> RG08.Supplies.stone
local notation "V"=> Next.Foundations.hol G

/-- strengthen supply AGAIN so exact same H and Label while allowing further conjunction. -/
theorem join (hZ:LocalRatio Z)(hk:∀ P:Patch,P.Branches k G)
    (N:Supply.Sheet G→MapPrices→MapPrices→ℕ→ℕ)(D:Supply.Sheet G→MapPrices→MapPrices→(ℕ→ℕ)→ℕ→ℝ):
    ∃ (C:Family G)(f:Extraction.Order)(T:YM.Table C.book)
        (F:Spec.Final C f T)(L:EveryPhase.Almanac F), C.Makes∧Spec.Calibrated C∧ C.path.levels.clock.kernel=k∧ UVExtension.Oasis.Floral (hG:=hg) C∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T∧ (∀ d u:ℕ, ∀ᶠ n:ℕ in atTop,∀ (r:ℕ)(v:Fin r→ C.book.Token),(∀ i,(v i).1≤ d)→∃ g,Poppy.Margins C r n u v g)∧EveryPhase.Completed F L ∧∃ (s:Supply.Sheet G)(P X:MapPrices)(H:Horizon C.path.levels),
      Legato.ExtraGates (fun s p=>N s p X) (fun s p=>D s p X) C s P H ∧ Aura.licensed C.path.levels H ∧ Yamen.Scheme C H (Case.actualPay s P) X Z ∧ OpenDoor C.path.levels (Case.actualPay s P) X ∧ OpenBook C.path.levels (Case.actualPay s P) X:=by
 let n(s:Supply.Sheet G)(P X i):=max (rail G s.kernel (Case.actualPay s P) X i) (N s P X i);let v(s:Supply.Sheet G)(P X f i):=max (after G s.kernel (Case.actualPay s P) X f i) (D s P X f i)
 obtain ⟨C,f,T,F,L,hm,hs,hK,hg',hu,hp,hc,s,P,X,H,-,-,h,he,hS⟩:=June.holdem G hg Z hZ k hk n v
 obtain ⟨h1,h2⟩:=paydays (a:=C) (B:=X) (fun i=> (le_max_left ..).trans (h.cluster i)) h.kernel (P:=P) (fun i=> (le_max_left ..).trans (h.payment i))
 exact ⟨C,f,T,F,L,hm,hs,hK,hg',hu,hp,hc,s,P,X,H,{h with cluster:=fun i=>(le_max_right ..).trans (h.cluster i),payment:=fun i=>(le_max_right ..).trans (h.payment i)},he,hS,h1,h2⟩

variable {G Z}
variable {a:Levels G}{F:Horizon a}{P B:MapPrices}{E:ℕ}
variable {f:Yamen.Audience a E→ℕ}(h:OpenDoor a P B)(hv:OpenBook a P B)
local notation "W"=> Yamen.feast f
local notation "D0"=> turnstile W
local notation "V0"=> Mason.kiosk W
local notation "N"=>snack G a.clock.kernel P
local notation "M"=>reef G a.clock.kernel P B
local notation "R₀"=>Mason.Run W
local notation "H₀"=> Haven W
lemma stay(i:ℕ):a.clock.J i≤a.clock.J (i+1):=a.fits.mono (by omega)
abbrev toll(i:R₀):=receipt G a.clock.kernel P B (T0 a i.m)
include hg hv
lemma till:(V0).Good fun i:H₀=>receipt G a.clock.kernel P B (T0 a i.m):=by
 let p(i:H₀):=receipt G a.clock.kernel P B (T0 a i.m)
 change (W).Poly (Mason.wide p);refine ⟨1+G.slopeConstant,1,(by linarith [G.slopeConstant_pos hg]),fun x i hi=>?_⟩
 have ht:= (hv i).trans (Flat.universeClock a hg x.measure i)
 rw [Mason.wide,dif_pos hi,pow_one,Yamen.clocked];exact ⟨zero_le_one.trans ((invoiced G a.clock.kernel P B (T0 a i)).title),ht⟩
lemma reach:(D0).Good (toll (f:=f) (P:=P) (B:=B)):= lowString.golf _ (till hg hv)
omit hg hv
variable (R:Cup)
include h
lemma noted {m:ℕ}(ht:R.E≤a.clock.J m):(cover G a.clock.kernel P B R (a.clock.J (m+1)) (a.clock.J m) ⟨Yamen.stepN m,a.clock.adm _,ht⟩).threshold ≤ (a.S.block m).val:=(admit_cup _ _ _ _ _ _).trans (h m) -- name rail_cup?
omit h
include hg hv
lemma snackLife:(D0).Good fun i:R₀=> (N (a.clock.J (i.m+1)) (a.clock.J i.m)).C (T0 a i.m):=(D0).hale (toll (P:=P) (B:=B)) _ (reach hg hv) (fun _=>Beverage.held _ _) (fun i=>(invoiced G a.clock.kernel P B (T0 a i.m)).costs _ (stay (a:=a) i.m))
lemma inverseLife {f:Yamen.Audience a R.E→ℕ}:(Mason.kiosk (Yamen.feast f)).Good fun i:Haven (Yamen.feast f)=> (M R.E (a.clock.J i.m))⁻¹:= (Mason.kiosk (Yamen.feast f)).hale (fun i=>receipt G a.clock.kernel P B (T0 a i.m)) _ (till hg hv) (fun _=>inv_nonneg.mpr (reef_life ..).le) (fun i=> (invoiced G a.clock.kernel P B (T0 a i.m)).film _ _ ((Yamen.listed f).walls i|>.trans (stay _)) (stay _))
omit hg hv in
lemma notedR {f:Yamen.Audience a R.E→ℕ}(i:Mason.Run (Yamen.feast f)):Note R (a.clock.J (i.m+1)) (a.clock.J i.m):=⟨Yamen.stepN i.m,a.clock.adm _,(Yamen.listed f).walls (Pier.low i)⟩
lemma stockLife {l e n:ℕ}{f:Yamen.Audience a R.E→ℕ}(hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e): (Mason.turnstile (Yamen.feast f)).Good fun i:Mason.Run (Yamen.feast f)=>stock G a.clock.kernel P B R (a.clock.J (i.m+1)) (a.clock.J i.m) l e n (notedR R i) hl he hn:= by
 apply (Mason.turnstile (Yamen.feast f)).hale _ _ (reach hg hv)
 · exact fun i=>(stock_use G a.clock.kernel P B R (notedR R i) hl he hn).1
 intro i
 exact (invoiced G a.clock.kernel P B (T0 a i.m)).est R _ (notedR R i) _ _ _ hl he hn
end YM.RG08.Redo
