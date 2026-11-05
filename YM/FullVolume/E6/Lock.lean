import YM.FullVolume.E6.Draught
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
def Mirror (K H : ℕ→Epoch Λ) : Prop:= ∀ J: Ultrafilter ℕ,(J:Filter ℕ)≤ atTop→Finish J K H
-- common shape along tests. Φ notation p.Kindstation worn. spunky proof both.
variable {Υ:ℕ→ Draft F G} {V:ℕ→ Config G c}
lemma frozen {α:Type}[Fintype α](Z:ℕ→α)(J:Ultrafilter ℕ):∃ p:α,∀ᶠ i in (J:Filter ℕ), Z i=p:=by
     by_contra! hu; have h i : ∀ᶠ x in (J:Filter ℕ), Z x≠i := hu i; obtain ⟨x,hx⟩:= (eventually_all.mpr h).exists; exact hx (Z x) rfl
variable {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
namespace Draft
abbrev amendment (Z: Draft F G)(y:F.Slice G): Draft F G:= {Z with Y:=y}
lemma frozen_budget (Y:F.Slice G)(hz:∀ n,(Υ n).Paid Q o x)(hv:∀ n,(Υ n).χ=χ):∃ (Z: Draft F G), Z.Paid Q o x∧ Z.χ=χ∧ (∀ᶠ i in (J:Filter ℕ), amendment (Υ i) Y=Z):=by
    obtain ⟨⟨k,e⟩,hk⟩:= Lim.frozen (fun i=> ((Υ i).store,(Υ i).k)) J
    refine ⟨⟨Y,k,e,χ,x,o.K⟩,⟨rfl,rfl⟩,rfl,hk.mono fun n h=>?_⟩
    have hb:= congr_arg Prod.fst h; have he:=congr_arg Prod.snd h
    change (Υ n).store=k at hb; change (Υ n).k=e at he
    dsimp only [amendment]; rw [hb,he,hv n,(hz n).1, (hz n).2]
include I R
variable (hz:Z.Paid Q o x)(hχ:Z.χ=χ)(h:Finish J K H)(hf:∀ᶠ i in (J:Filter ℕ), Z.Viable (V i))
set_option quotPrecheck false
local notation "D"=> fun n=> Z.paints (K n) (V n)
local notation "D'"=>fun n=> Z.paints (H n) (V n)
include hz hχ h hf
lemma takes (w:Air f G): Glints J (fun n=> cups (D n) (K n|>.beta) w) (fun n=> cups (D' n) (H n|>.beta) w):=by
    have ha:= Draft.haloV (J:=J) (j:=j) (R 0|>.N.position.le) V
    let A n:=D n; let V' n (_:ℝ):=V n
    have hK:Frill J j (0:ℝ) (fun n _=> kickback (D n) (K n).beta w) (fun n _=> kickback (D' n) (H n).beta w):= Draft.restart I (fun i=> hχ.symm ▸ (R i).fleets.bills) hz h ha hf w
    have hv:= Draft.relate (U:=V') I hz h (scaleG ha) hf
    have he : ∀ᶠ i in (J:Filter ℕ), Allow (D i|>.relating) (along (G:=G) S) _ _ _ _:= hf.mono fun n hi=> Rotator.suspected _ (((I n).laws.data.localP F (D n) hz.1 hz.2 hi).sails)
    have hu:= (lensP (u:=fun n (_:ℝ)=> kickback (D n) (K n).beta w) (w:=fun n (_:ℝ)=> kickback (D' n) (H n).beta w) he hv hK).1
    exact ((((Frill.bare (ticks I h)).via (Q:=fun x:ℝ=> x^Module.finrank ℝ (Air f G)) (contDiff_id.pow _)).times hu).crest)
include T
lemma decks (w:Air f G)(i:Molecule S): Glints J (fun n=> cups (D n) (K n).beta w • (D n).term (K n).kin Q.table W o.a (own i) Q.halo (kickback (D n) (K n).beta w) i) (fun n=>cups (D' n) (H n).beta w • (D' n).term (H n).kin Q.table W o.a (own i) Q.halo (kickback (D' n) (H n).beta w) i):=by
    have hu b:= Draft.mood (H₀:=I) T (j:=j) (fun i=> hχ.symm ▸ (R i).fleets.bills) hz h (R 0|>.N.position.le) V hf w b (own i)
    exact ((Frill.bare (takes I R hz hχ h hf w) (x:=(0:ℝ)) (n:=0)).times (Frill.pears i fun k _=> Frill.bare (hu k))).crest
omit I R hχ h hf T
-- force all X scales.I.P requiring0≤ deals. Instantiate.
variable (hP:∀ i,(Υ i).Paid Q o x)(hK:∀ i,(Υ i).χ=χ)(ht:∀ n,(Υ n).Viable (V n))(hW:Mirror K H)
local notation "Z₀"=> fun n=> (Υ n).paints (K n) (V n)
local notation "Z₁"=>fun n=> (Υ n).paints (H n) (V n)
omit hz in
include hP ht in
lemma loved : Spunky x o Z₀:=⟨fun i=>(hP i).1,fun i=>(hP i).2,ht⟩
omit hz
include I R hP hK ht
private lemma coned (h:Sweep K)(i:Molecule S): Peaking Z₀ (fun n=> (Z₀ n).body (K n).kin Q.table W o.a (own i) Q.halo i):=by
    obtain ⟨q,hq⟩:= coined M I R h; obtain ⟨C,hC⟩:= hq.silver.arbitrary.bound
    refine ⟨fun n=> (I n).integrated (Z₀ n) (hP n).1 (hP n).2 (ht n) _ i, ⟨∅,0,C,budget_nonneg (hC 0),fun n y z=> ?_⟩⟩; unfold body Coat.term; rw [pow_zero,mul_one,norm_prod]
    exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> hq.force n F ((Z₀ n).wrapY y) (hP n).1 (hP n).2 (hK n) (ht n) _ _ i)).trans (budget_single (hC n) i)
include hW T P'
lemma behold (h:Sweep K)(hy:Sweep H)(i:Molecule S): Tendsto
    (fun n=> (Z₀ n).attains (K n).kin Q.table W o.a (own i) Q.halo i- (Z₁ n).attains (H n).kin Q.table W o.a (own i) Q.halo i) atTop (𝓝 0):=by
    refine Peaking.stack I T (coned I R hP hK ht h i) (loved hP ht) (coned T P' hP hK ht hy i) (loved hP ht) ?_
    intro y w
    refine (tendsto_iff_ultrafilter ..).mpr fun J hj=> ?_
    obtain ⟨Z,hz,hχ,hY⟩:=frozen_budget (J:=J) y hP hK
    have hh: ∀ᶠ i in (J:Filter ℕ),Z.Viable (V i):= hY.mono fun i hi=> hi ▸ (show (amendment (Υ i) y).Viable (V i) from ht i)
    refine (decks I T R hz hχ (hW J hj) hh w i).shrank.congr' (hY.mono fun k hk=>?_)
    dsimp only [footZ]; rw [← hk]; rfl
end Draft
end YM.ConnectedActivityE6.Lim
