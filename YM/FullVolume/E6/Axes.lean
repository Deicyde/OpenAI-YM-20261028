import YM.FullVolume.E6.Seeds
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
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{φ:Filter ℕ} {J:Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W:ℝ}
    {o:Target.Order G W}{j:ℕ}{x μ C₀ : ℝ}{Λ: Era G S}
-- house includes seeds,fixed width. χ canonical
structure Draft (F:Forest S.ratio)(G:Gauge) where
    Y:F.Slice G -- fixed for proof. depends on Y integral. OK comparisons pointwise. In pricing use common.L.
    store:Stores S
    k:S.Choices
    χ:Chi
    x:ℝ
    width:ℝ
namespace Draft
variable {Υ : Draft F G} (Y:Epoch Λ)
abbrev paints (Z:Draft F G)(Y:Epoch Λ)(V:Config G c): Coat Y.tubes F:= ⟨Z.store,Z.x,Z.χ,Z.width,V,Z.k,Z.Y⟩
def Paid (p:Draft F G)(Q:ConnectedActivityE6.Target G P)(o:Target.Order G W)(x:ℝ):Prop:= p.x=x∧p.width=o.K
def Viable (d:Draft F G)(U: Config G c):Prop:=d.store.flags=RG.flags (Pressure.temp d.x) U
def pearl (p:Draft F G): Draft F G := {p with store:=⟨∅,∅,∅⟩}
-- blank. exact
lemma empties (p:Draft F G)(Y:Epoch Λ)(V:Config G c): (p.paints Y V).blank= p.pearl.paints Y 1:=rfl
variable {K H:ℕ→ Epoch Λ}{U V:ℕ→ E→ Config G c}{p:E}
private def hot (A: Draft F G) (s:Signed)(i:Spot c f) :Prop:=¬ Inside (s.act (lead S i)) A.store (6*radiusB A.x)
lemma plot (h:Finish φ K H) (he: Quincy φ j p U V)(Z:Draft F G): Buds φ j p (fun n y=> (Z.paints (K n) (U n y)).form) (fun n y=> (Z.paints (H n) (V n y)).form):=by
    intro i k
    by_cases hc:hot Z i.1.1 (spot S i.1.2)
    · have hp Z' (V:Config G c): (Z.paints (Λ:=Λ) Z' V).form i k= scale* stand (fun j=> orientedRow Z'.tubes (Pressure.Stores.till Z.x) j.1 j.2 V ((Z.paints Z' V).lens (sing k))) i:=by
          have H: (Z.paints Z' V).selected i.1.1 (spot S i.1.2) := hc
          dsimp only [Coat.form,Matrix.of_apply,stand, Coat.motion]; rw [if_pos H]
      simp_rw [hp]; apply (Frill.still _).times
      let x:=((Z.paints (K 0) 1).lens (sing k)); exact (h.frameZ he (Frill.still x) (Pressure.Stores.till Z.x) i.1.1 i.1.2).via (Q:=fun C:G.Color=> C i.2) ((EuclideanSpace.proj (𝕜:=ℝ) i.2).contDiff)
    have hx Z' (V:Config G c): (Z.paints (Λ:=Λ) Z' V).form i k=0:=by have H : ¬ (Z.paints Z' V).selected i.1.1 (spot S i.1.2):= hc; unfold Coat.form; dsimp only [stand,Coat.motion, Matrix.of_apply]; rw [if_neg H]; change _ * 0=0; rw [mul_zero]
    simp_rw [hx]; exact Frill.still _
lemma plume (h:Finish φ K H) (he: Quincy φ j p U V)(Z:Draft F G): Buds φ j p (fun n y=> (Z.paints (K n) (U n y)).plate) (fun n y=> (Z.paints (H n) (V n y)).plate):=by
    have hq:= plot h he Z; exact (hq.opp.pairs hq).append (fun i j=> Frill.still ((Z.paints (K 0) 1).sleepy i j))
section stable
variable {Z:Draft F G}
variable (H₀: ∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin) (hz:Z.Paid Q o x)
include hz
lemma licenses (Y:Epoch Λ) (H:Cash W x μ L Q o C₀ Y.tubes Y.kin) (V: Config G c) (hV:Z.Viable V): Allow (Z.paints Y V).plate (Census.along S) (Census.tubularPrice G L) o.eta o.gap o.ample:=(H.laws.data.localP F (Z.paints Y V) hz.1 hz.2 hV).sails.scale -- remove H₀
omit hz
variable (h:Finish φ K H)(he: Quincy φ j p U U)(ht:∀ᶠ i in φ, Z.Viable (U i p))
include H₀ hz ht h he
set_option quotPrecheck false
local notation "D" => fun n y=> (Z.paints (K n) (U n y))
local notation "D'" => fun n y=> (Z.paints (H n) (U n y))
lemma principals (i:Tubular f G) : ∀ᶠ n in φ,Allow (frames G S (radiusB Z.x)|>.principal ((D n p).plate) i) (Census.along S ∘ fun v=> v.val) (Census.tubularPrice G L) o.eta o.gap o.ample:= ht.mono fun n hn=> (licenses hz _ (H₀ n) (U n p) hn).sub (Embedding.subtype (fun x=>x∈ (frames G S (radiusB Z.x)).take i))
lemma standbys [φ.NeBot] : Buds φ j p (fun n y=>(D n y).kernelA) (fun n y=> (D' n y).kernelA):=by
    let M:=frames G S (radiusB Z.x); have hs:=plume h he Z; intro i k
    by_cases hh: i∈ M.take k
    · let g(A: Matrix (Tubular f G) _ ℝ):=M.principal A k
      have hg: Buds φ j p (fun n y=> g (D n y).plate) (fun n y=> g (D' n y).plate) := hs.below Subtype.val; let f(A: Matrix (Tubular f G) _ ℝ):= (g A)⁻¹ ⟨i,hh⟩ ⟨k,M.here k⟩
      refine ((hg.restoreP (principals H₀ hz h he ht k)) ⟨i,hh⟩ ⟨k,M.here k⟩).alter ?_ ?_
      exact Eventually.of_forall fun n=> Eventually.of_forall fun y=> (M.inside (D n y|>.plate) k ⟨i,hh⟩).symm
      exact Eventually.of_forall fun n=> Eventually.of_forall fun y=> (M.inside (D' n y|>.plate) k ⟨i,hh⟩).symm
    refine (Frill.still (0:ℝ)).alter (Eventually.of_forall fun n=>Eventually.of_forall fun y=> (M.outside _ _ _ hh).symm) (Eventually.of_forall fun n=>Eventually.of_forall fun y=> (M.outside _ _ _ hh).symm)
lemma relate [φ.NeBot] : Buds φ j p (fun n y=> (D n y).relating) (fun n y=> (D' n y).relating):=by
    have hq:=standbys H₀ hz h he ht; exact fun i k=> (Frill.still _).fee ((hq.append hq.opp) i k)
end stable
end Draft
end YM.ConnectedActivityE6.Lim
