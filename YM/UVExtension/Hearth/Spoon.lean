import YM.UVExtension.Hearth.Table
import YM.UVExtension.Orchard.Vanilla
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Hearth
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory Push GridApprox Mast Steady
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
open Relay Mast.Cellar Steady Push GridApprox Accent Cells

variable {t:ℕ→ℕ}{S v R} (U:Cellar S t R) (K:ℕ→ℕ)(h:Scrim (U.yard v) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v))
    (hK: Stock.Tabs A.B.a) (J k:ℕ)(w:ℝ)(hw:0<w)(hz:Stock.Tabs.opens A.B.a 1 J m)
local notation "C0"=> yard v U
local notation "F"=> (C0|>.labels.level d)
local notation "K0"=> lensScope C0 d
local notation "o!"=> (0:Site ((C0).side k n))
local notation "T!"=> A.B.a.S

open Extraction OS RelayDifference
-- lift across registry J.Spectrum. retain rates eventually.M
-- Some metadata.No projection ties for **this stage only**. full.Separate all tests.
lemma mounds (P:Schedule)(J i:ℕ) : Dense {x:Points i|∃ k:ℕ,J≤ k∧∃ u:Fin i→ Cover, x=Extraction.tag (P.a k) u}:=by
   intro z; apply mem_closure_of_tendsto (chosen (S:=P) z); filter_upwards [eventually_ge_atTop J] with k hk; exact ⟨k,hk,_,rfl⟩
lemma uniqueM (S:Schedule)(k i n:ℕ)(u:Fin i→ Cover)(he: Extraction.tag (S.a k) u∈ Extraction.NoHit S n i) : Injective (wrap (S.side k n) ∘ u):=by
   intro i j h; by_contra hv; obtain ⟨r,hr,hR⟩:=Extraction.Gaps.some S n isCompact_singleton (Set.singleton_subset_iff.mpr he); have hx:=Extraction.Gaps.gridSeparation S _ rfl (hR _ (Set.mem_singleton _)) _ _ hv; rw [h] at hx; simpa [hr.not_ge] using hx
lemma placeK (C:Family G)(N k p i:ℕ)(v:Fin i→ C.book.Token)(u:Fin i→ Cover) (h:k≤N): (extendCut C N p).read (Extraction.tag (C.S.a k) u) v=C.numeric N p v (fun i=> location C.S k N p (u i)):=by
   let X:= Extraction.tag (C.S.a k) u
   let V:Fin i→ Site (C.S.side N p):=bucket N p X (S:=C.S)
   have he: V=fun i=> location C.S k N p (u i):=by
      funext i; let Z:= C.S.toDepth h p; let d:=Z.count.val; have hp:= C.S.embeds_scale Z
      have ht j : Extraction.address (C.S.a N) X i j= (d:ℤ)*u i j:=by
          change ⌈C.S.a k*(u i j:ℝ)/C.S.a N⌉=_; rw [show _ / _= (((d:ℤ)*u i j : ℤ):ℝ) from ?_, Int.ceil_intCast]; push_cast; rw [← hp]; have hu:=C.S.a_pos N; field_simp; exact mul_comm .. 
      unfold Cells.location; rw [dif_pos h]; change _= Z.embed _; rw [Z.embed_wrap]; exact congr_arg (wrap _) (funext fun j=> (ht j).trans (by simp [d,nsmul_eq_mul]))
   change C.numeric N p v V = _; rw [he]

include a h hv hK
lemma pottery (P':Extraction.Wcmain (yard v U))(I:ℕ)(u:Fin I→ (C0|>.book.Token)) : ∃ F':Points I →ℂ, Extraction.Meets (Extraction.Cyclic A.B.a.S n I) (fun i x=> (extendCut (C0) i n).read x u) F':=by
   let S:= C0; have hp:= intakeV v U; let f:= Extraction.Order.full
   have hD:= Vintage.YM.Extraction.Wcmain.projects S f hp P'
   have hG:= each_oscillates S f (Vintage.YM.Extraction.Difference.completed hp (hD.book _ _)) n I u
   let k:= Finset.univ.sup (fun i=> S.ref (u i).1)
   refine Extraction.growFrom (cyclicOpen S.S n I) hG _ (mounds S.S k I) ?_
   rintro x' ⟨⟨k',hk,w,rfl⟩,hY⟩
   have hv':Injective (wrap (S.side k' n) ∘ w):= uniqueM S.S k' I n w (fun i j h=> ⟨timeAxis,hY i j h _⟩)
   obtain ⟨b,hb⟩:=food n a x hv U K h hK k' P' I u w hv' (fun i=> (Finset.le_sup (f:=fun i=> S.ref (u i).1) (Finset.mem_univ _)).trans hk)
   apply Filter.Tendsto.cauchySeq (x:=b); exact hb.congr' ((eventually_ge_atTop k').mono fun j hj=> (placeK S j k' n I u w hj).symm)
omit hv
lemma setP (hU:Extraction.Wcmain (yard v U)) (hv:∀ n,∃ x:Rose S,Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val)) : ∃ P:ℕ→ Table (yard v U).book, Extraction.Order.full.Meshes (yard v U) P∧∀ p n (u:Fin n→ (yard v U).book.Token), Meets (Extraction.Cyclic A.B.a.S p n) (fun i x=> (extendCut (C0) i p).read x u) (fun x=> (P p).read x u):=by
   let S:= C0
   choose g hg using fun (n:ℕ)(w:Indices S.book)=>pottery n a (hv n).choose (hv n).choose_spec U K h hK hU w.1 (Extraction.stack w)
   let P p:= fitted (g p)
   have ht (p n) (u:Fin n→ S.book.Token) : Meets (Extraction.Cyclic A.B.a.S p n) (fun i x=> (extendCut S i p).read x u) (fun x=> (P p).read x u):=by
      refine components (P p) _ (Extraction.Cyclic A.B.a.S p) (fun z=> ?_) _ u
      simpa only [P, knobs] using (hg p z)
   refine ⟨P,⟨fun p u=> (ht p _ u).continuousOn,fun p n J hj hk t ε he=> ?_⟩,ht⟩
   filter_upwards [(ht p n t).uniform J hk hj ε he] with j hh u hu; have hx:= hh (Extraction.tag (S.S.a j) u) hu; change dist (lifted S j p t (Extraction.address (S.S.a j) (Extraction.tag (S.S.a j) u))) _ <ε at hx; rw [Extraction.address_matched (S.S.a_pos j),dist_eq_norm] at hx; exact hx
lemma slaked (hU:Extraction.Wcmain (yard v U)) (hv:∀ n,∃ x:Rose S,Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val)) : ∃ P:ℕ→Table (yard v U).book,Extraction.Order.full.Meshes (yard v U) P∧∀ n p (u:Fin n→ (C0).book.Token)(t':Test n), Extraction.suitable A.B.a.S p t' →
    Integrable (fun x=> t' x*(P p).read x u)∧ Tendsto (fun i=> Extraction.Order.smears C0 i p u t') atTop (𝓝 (t'.applyTo fun x=>(P p).read x u)):=by
   obtain ⟨P,hP,hL⟩:= setP a U K h hK hU hv; let f:=Extraction.Order.full
   have hx:= intakeV v U; have ht:= Vintage.YM.Extraction.Around.size_done hx ((Vintage.YM.Extraction.Wcmain.projects C0 f hx hU).book C0 f)
   refine ⟨P,hP, fun n p u t ht'=>f.intraperiod C0 ht hP ht' u⟩
end YM.UVExtension.Hearth
