import YM.UVExtension.Harvest.Barn
import YM.UVExtension.Poppy.Ginkgo
/-! REAL full-sequence convergence, even projection ties. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Poppy
open Finset Set Function Filter MeasureTheory Analysis Extraction Lattice Fallow Harvest
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{n p:ℕ}
/-! Limits stated by one real-trajectory kernel on these configurations (can fill padding however).
 Ceiling convention for Ink, plus actual multilinear interpolation Poppy.interpolate.
 Word acceptance for any order ≤k. Displaced backward/forward increments
 used even at projection ties; all lengths fixed integer step counts,
 normalized as in that constructor. On cover coordinates (including periodic
 extension). -/
structure Margins (C:Family G)(n p k:ℕ)(v: Fin n→ C.book.Token)(f:Points n→ℂ):Prop where
   tests (u:Test n)(h:suitable C.S p u): Integrable (fun z=> u z*f z)∧ Tendsto (fun i=> Order.smears C i p v u) atTop (𝓝 (u.applyTo f))
   grids : Meets (NoHit C.S p n) (Ink C.S (fun i=> lifted C i p v)) f
   halls (u:List (Stride n)): u.length ≤ k→ Meets (NoHit C.S p n) (fun i=> Poppy.interpolate (C.S.a i) (Poppy.strides (C.S.a i) (lifted C i p v) u)) (ivy f (u.map Stride.axis))
   plain (u:List (Axel n)): u.length ≤ k→ Meets (NoHit C.S p n) (Ink C.S fun i=> rake (C.S.a i) (lifted C i p v) u) (ivy f u)
   derivatives (u:List (Axel n)) (a:Axel n) (x:Points n): u.length<k→ x∈NoHit C.S p n→ HasDerivAt (fun t:ℝ=> ivy f u (x+t • Points.direction a.1 a.2)) (ivy f (a::u) x) 0
open Extraction.Order
lemma meshR {v: Fin n→ C.book.Token}{K: Points n→ℂ} (H : Meets (NoHit C.S p n) (Ink C.S (fun i=>lifted C i p v)) K) {t : Test n} (h : suitable C.S p t) {x : Points n}
    (he : x ∈ Cyclic C.S p n) :
    Tendsto (fun j => densityCell C (Order.full.mesh j) p v t x) atTop (𝓝 (t x * K x)) := by
  by_cases hx : x ∈ Fund C.S p n
  · simp_rw [stepped C _ p hx v t]
    let r (i) := address (C.S.a (Order.full.mesh i)) x
    have hi := chosen (S := C.S) x |>.comp Order.full.mesh.cofinal
    have hp : Tendsto (fun j => C.numeric (Order.full.mesh j) p v (bucket _ _ x)) atTop (𝓝 (K x)) :=
      visiting (Fallow.no_wrap C.S p n) H (fun i j hi=> ⟨timeAxis,he i j hi _⟩) (fun i=> address _ x) (chosen x)
    exact (t.continuous.continuousAt.tendsto.comp (show
      Tendsto (fun j => tag (C.S.a (Order.full.mesh j)) (r j)) atTop (𝓝 x) from hi)).mul hp
  have hw : t x = 0 := by
    by_contra hT
    have hu : x ∈ Inside C.S p n := h (subset_closure hT)
    exact hx (show ∀ i a, _ < x i a ∧ x i a ≤ _ from fun i a => ⟨(hu i a).1, (hu i a).2.le⟩)
  simp_rw [densityCell,stair,indicator_of_notMem hx, hw, zero_mul]; exact tendsto_const_nhds

theorem coveringR {v: Fin n→ C.book.Token}{K: Points n→ℂ} (Hp : Bound C Order.full) (H : Meets (NoHit C.S p n) (Ink C.S (fun i=>lifted C i p v)) K) {t : Test n} (h : suitable C.S p t) :
    Integrable (fun x : Points n => t x * K x) ∧
    Tendsto (fun j => smears C (Order.full.mesh j) p v t) atTop (𝓝 (t.applyTo fun x => K x)) := by
  classical
  obtain ⟨D, hD,Hb⟩ := Hp.cyclic n v p _ t.hasCompactSupport (readable C.S p t h)
  obtain ⟨R,H₁,H₂⟩ := testSup t
  let B := (Fund C.S p n).indicator (fun _ => R*D)
  have HI : Integrable B := (integrable_indicator_iff (full_box _ _ _).1).mpr
    (integrableOn_const (full_box _ _ _).2.ne)
  let F := fun j : ℕ => densityCell C (Order.full.mesh j) p v t
  have Hs (j) : AEStronglyMeasurable (F j) volume := (stair_int _).aestronglyMeasurable
  have hb : ∀ᶠ j : ℕ in atTop, ∀ x, ‖F j x‖ ≤ B x := by
    filter_upwards [Hb] with i hi x
    by_cases he : x ∈ Fund C.S p n
    · unfold F B; rw [stepped C _ p he, indicator_of_mem he]
      let a := address (C.S.a (Order.full.mesh i)) x
      let y := tag (C.S.a (Order.full.mesh i)) a
      change ‖t y * lifted C (Order.full.mesh i) p v a‖ ≤ _
      rcases eq_or_ne (t y) 0 with HT|HT
      · rw [HT,zero_mul,norm_zero]; exact mul_nonneg H₁ hD
      exact (norm_mul_le ..).trans (mul_le_mul (H₂ _) (hi a (subset_closure HT)) (norm_nonneg _) H₁)
    simp [F,B,densityCell,stair,he]
  have hg : ∀ᵐ x : Points n, Tendsto (fun j => F j x) atTop (𝓝 (t x * K x)) :=
    (almostCyclic C.S p n).mono fun _ hx => meshR H h hx
  constructor
  · refine HI.mono' (aestronglyMeasurable_of_tendsto_ae atTop Hs hg) ?_
    filter_upwards [hg] with x hx; exact le_of_tendsto hx.norm (hb.mono fun i hi => hi x)
  simp_rw [← exactSmear C]
  exact tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall Hs)
    (hb.mono fun i H => Eventually.of_forall H) HI hg

open RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof Mast
open MeasureTheory Push GridApprox
open scoped Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} {S:Uses Q hG} {v:Keys S} {C':ℕ→ℝ}{W:Bid.Worth}{R:Legato.Bandage Q C' W}
    {I t:ℕ→ℕ}{U:Cellar S t R}{V:Org.Bolt A}(h:Upland.Arc Q S V)(B:Harvest.Barn S R I U)
variable (z:Rose S)(he : Tendsto (fun i=>(v i p).val) atTop (𝓝 z.val))
local notation "F'"=> Cellar.yard v U
variable (w: Fin n→ (Hearth.roster U).Token) (k:ℕ) (hx:∀ i,∀ j:ℕ,(w i).1 ≤ j→ j ≤ (w i).1 + k+1→ Slicing (U.yard v) j p)
set_option quotPrecheck false
local notation "Y'"=> NoHit A.B.a.S p n
include B hx
lemma offers : Poppy.Shelf A.B.a.S (NoHit A.B.a.S p n) (fun i=> Extraction.lifted (U.yard v) i p w) (k+1):=by
   obtain ⟨hA,hB,hC⟩:= B.sponsors v; refine ⟨fun i hi M hK hm=>?_⟩
   exact Fallow.reaped hG (U.intakeV v) B.tithe hB hC p hA i w _ hm hK (fun i j h hp=>hx i j h (hp.trans (by omega)))
lemma grads : ∀ (K : Set (Points n)), K⊆NoHit A.B.a.S p n → IsCompact K → ∃ b:ℝ,0 ≤ b∧∀ᶠ i in atTop,Poppy.capping (A.B.a.S.a i) b (Extraction.lifted (U.yard v) i p w) K:=by
   intro K h hK; have he:= offers B w k hx
   choose b hb hB using fun i:Axel n=>he.fees [i] (by simp) _ h hK
   refine ⟨∑ i,b i,sum_nonneg (fun i _=>hb i),(eventually_all.mpr hB).mono fun n hn i x hx=>?_⟩
   exact (hn i x hx).trans (single_le_sum (fun i _=>hb i) (Finset.mem_univ _))
include h he
lemma blossoms : ∃ f,Poppy.Margins (U.yard v) n p k w f:=by
   let C:= F'; obtain ⟨hh,hP,hX⟩:= B.sponsors v
   have hm(f):= Vintage.YM.Extraction.Wcmain.projects C f (U.intakeV v) hX; let e0:=Extraction.Order.full
   let Z i:=Extraction.lifted C i p w; have ho:=Fallow.no_wrap A.B.a.S p n
   let l:= Finset.univ.sup (fun i=> t (w i).1)
   have hp(x)(hr:x∈ {x:Points n|∃ m,l ≤ m ∧ ∃ a:Fin n→ Cover,x=Extraction.tag (A.B.a.S.a m) a}∩ NoHit A.B.a.S p n): CauchySeq (fun j=> Ink A.B.a.S Z j x):=by
      obtain ⟨⟨m,hk,v',rfl⟩,h1⟩:= hr
      obtain ⟨b,hb⟩:= Hearth.food p h z he U I hP B.tithe m hX n w v' (Hearth.uniqueM _ _ _ _ _ h1) (fun i=> (Finset.le_sup (f:=fun i=>t (w i).1) (Finset.mem_univ _)).trans hk)
      refine Filter.Tendsto.cauchySeq (x:=b) (hb.congr' ?_); filter_upwards [eventually_ge_atTop m] with i hi; exact (Hearth.placeK C i m p n w v' hi).symm
   obtain ⟨y,hy⟩:= Extraction.growFrom ho (Poppy.tending A.B.a.S Z ho (grads B w k hx)) _ (Hearth.mounds A.B.a.S l n) hp
   refine ⟨y, ⟨fun u hu=>coveringR (C:=C) (v:=w) (Vintage.YM.Extraction.Around.size_done (U.intakeV v) ((hm _).book _ _)) hy hu, hy, fun u hu=>Poppy.uphol ho (stroke u ho (F:=Z) ?_), fun _ hi=> seasoning ho hy (offers B w k hx) _ hi,fun i a x hp=>?_⟩⟩
   · apply seasoning ho hy (offers B w k hx); simpa only [List.length_map]
   exact actually a ho hy (offers B w k hx) i hp x -- ∀ x
end YM.UVExtension.Poppy
