import YM.TraceExtension.Margin.White
import YM.TraceExtension.Margin.Bevel
import YM.TraceExtension.Margin.Beans
import YM.TraceExtension.Terrace.Ell
import YM.TraceExtension.Terrace.Vapid
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Perfect Turret Weir Wicket Extra.Histories Next.Foundations Planned.AtomRegular.Foliage Planned.GuardedAtom Guard
open Extraction RG.Supply Zn Swift Fen
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{F:Frame G d}
-- calendar stage bill purchased once before shutters
lemma footprint_im (T:SectionData F): ∀ᶠ t:ℝ in atTop,∀ n:Side,T.footprint (0:Site n)⊆tempQ t:=by
    filter_upwards [eventually_all_finset T.stencil|>.2 (fun i _=> Work.E01.radiusB_tendsto.eventually_ge_atTop (size i))] with t ht n a ha
    obtain ⟨x,hx,rfl⟩:=mem_image.mp ha; rw[add_zero]; apply halo_spec.mpr; refine ⟨0,mem_singleton_self _,?_⟩; rw [separation_comm,separation,sub_zero]; exact le_trans (Next.Free.within_size ..) (Nat.le_trans (ht _ hx) (by unfold high; omega))
variable (K:Labels.Frames G) (L:∀ d,SectionData (K.level d))(H:Hol G)
def coupon(G:Gauge)(S:Stage):ℝ:=Next.Foundations.price G (max S.order S.power)
lemma coupon_nn(G:Gauge)(S:Stage):0 ≤ coupon G S:=by unfold coupon Next.Foundations.price; exact add_nonneg zero_le_one (sum_nonneg (fun i _=> le_max_left ..))
abbrev PurchaseR(C:SectionData F)(H:Hol G){n:Side}(R:Rep G n)(x:ℝ)(φ:Peat G n):Prop:= ∃ Z,AtomD C H R Z (filmR φ) (Weir.smoke x) (Shunt.grantS x) x ∧ Z.x= Triple H F x R φ
-- Atlas flight basis
structure Quilt (F:Frame G 5)(n:Side) where
    J : Dart G n
    B : Finset GreenA
    V : Finset ℕ
    U : Finset ℕ
    X : Axis → Coefficient F n
structure WorthB (K:Labels.Frames G)(L:∀ d, SectionData (K.level d))(H:Hol G)(S:Stage)(x:ℝ)(Λ:ℝ) {n:Side}(R:Rep G n)(Q:Quilt (K.level 5) n) : Prop where
    age: Age S x Λ R
    site : 20*(high x+rim x+10)< n.val
    film: Sight x R Q.J
    accurate (a:G.ColorIndex): |Loft.midPay a Q.J - Loft.landPay G| ≤ shock x
    sea : Scraps R x Q.J
    bases(M:Bool): Club R x (Plint G n M)
    cover : ∃ q v c, Wholesome R x Q.J q 48 (wheelQ x) S v Λ c
    ready : DawnU 48 R x Q.J Q.B Q.V Q.U
    boat(a:Axis): Combat (L 5) H R x Q.J Q.B Q.V Q.U 48 (wheelQ x) a (Q.X a)
    earnings (d:ℕ)(h:d≤5)(Φ: Peat G n): Cubc R x Φ → PurchaseR (L d) H R x Φ
structure StoreQ (K : Labels.Frames G)(L:∀ d,SectionData (K.level d))(H:Hol G)(S:Stage)(x:ℝ):Prop where
    sure : ∀ (Λ:ℝ)(n:Side)(R:Rep G n)(J:Dart G n), Age S x Λ R→ Sight x R J→ 20*(high x+rim x+10)< n.val→ (∀ a:G.ColorIndex, |Loft.midPay a J - Loft.landPay G| ≤ shock x) → Keeper R.p R.activities → (∀ d:ℕ,d≤5→ Push.Local.Readable H (L d) R.p n (coupon G S))→∃ W:Quilt (K.level 5) n,W.J=J∧WorthB K L H S x Λ R W
lemma taxes(G:Gauge) (S:Stage)(h:G.Simple) (K:Labels.Frames G)(L:∀ d,SectionData (K.level d))(H:Hol G): ∀ᶠ x:ℝ in atTop, StoreQ K L H S x:=by
    obtain ⟨C⟩:=collarSupply G S.order; obtain ⟨Z,D,hZ,hD,H'⟩:= Inspires G h S 48 60 (by omega) C; let c:=coupon G S; have hc:0≤ c:= coupon_nn ..
    filter_upwards [H',shred G S C,plonk G S C,eventually_ge_atTop (1:ℝ),trendH G S (K.level 5) (L 5) H 48 60 c hc,eventually_all.mpr fun d:Fin 6=> footprint_im (L d),eventually_all.mpr fun d:Fin 6=> trend S (H:=H) (L d) c hc] with x hx he hs hp' hN ht hg
    refine ⟨fun Λ n R J hv hx' hm h ha hB=>?_⟩
    have hA:20*(high x+10)<n.val:=by omega
    let q:= wheelQ x; have hq:1100 ≤ q:=by unfold q wheelQ towerH;omega
    have hT:= hx q hq le_rfl Λ n R J hx' hv hA; obtain ⟨A,hh⟩:= (Weir.dawn hT hp').exists; obtain ⟨P,hp⟩:=hh.exists; obtain ⟨U,hU⟩:=hp.exists
    choose X hX using fun a:Axis=> hN q hq le_rfl n Λ R J hT.base (hB 5 le_rfl) (show (L 5).footprint (0:Site n)⊆tempQ x from ht 5 n) hv hT.pay A P U a hU.1 (hU.2.2 a).1
    refine ⟨⟨J,A,P,U,X⟩,rfl,hv,hm,hx',h,he n Λ R J hv hx' hA,hs Λ n R hv hA,⟨_,_,_,hT⟩,hU,hX,fun d hd Φ h=>?_⟩
    exact hg (⟨d,by omega⟩:Fin 6) n Λ R hv ha (hB d hd) (ht (⟨d,by omega⟩:Fin 6) n) Φ h
end YM.Trace.Margin
