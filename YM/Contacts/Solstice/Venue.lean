import YM.Contacts.Solstice.Skies
import YM.MultipleContact.Tests
/-!
# Distributions in each illuminated patch

The integrals and finite sums have used all smooth tests on the permitted support domains. On an
open part of the domain this yields an ordinary continuous linear test map. We give also the global
extension in these positions (and when any fields are not being inspected for projection purposes).
Applies on the unselected hierarchy & every character's reader. Normalized tests implemented in
`Scaling` may have changing support and should be costed with the uniform budgets rather than
an arbitrary bound for these continuous linear maps.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory Distributions
variable {E X : Type} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X][NormedSpace ℝ X][IsScalarTower ℝ ℂ X][CompleteSpace X]

def unpack (U : Opens E) : 𝓓(U,ℂ) →ₗ[ℂ] SmoothTests E where
   toFun g := ⟨g, g.contDiff⟩
   map_add' _ _ := rfl
   map_smul' _ _:= rfl
omit [FiniteDimensional ℝ E] in
lemma converted {p : E→ℂ}{c : ℝ}{n : ℕ} : JetBounds n p c ↔ Jet n univ p c := ⟨fun h=>⟨h.1,fun i hi x _=> h.2 x i hi⟩, fun h=> ⟨h.pos,fun x i hi=> h.bounds i hi x (Set.mem_univ _)⟩⟩
-- descriptor continuous from Dust. Need pay only compact patch price.
variable [MeasureSpace E]
structure Charge (P : E→ SmoothTests E→ₗ[ℂ] X)(U : Opens E)(n : ℕ) : Prop where
   cost : ∀ K:Compacts E, (K:Set E) ⊆ U → ∃ C> (0:ℝ),∀ (p:SmoothTests E){m:ℝ}, tsupport p.val ⊆ K → Jet n univ p.val m → Dust (fun x=> P x p) (C*m)

namespace Charge
variable {P:E→ SmoothTests E→ₗ[ℂ] X}{U : Opens E}{n : ℕ} (R : Charge P U n)
include R
omit [FiniteDimensional ℝ E] [CompleteSpace X] [IsScalarTower ℝ ℂ X] [NormedSpace ℝ X] in -- depends via Charge?
lemma readable (p:𝓓(U,ℂ)) : Integrable (fun x=> P x (unpack U p)):= by
   let K: Compacts E:=⟨tsupport p,p.hasCompactSupport⟩; let c:ℝ:= (has_bound p n).choose; have hm : Jet n univ (unpack U p).val c:= converted.mp (has_bound p n).choose_spec;
   obtain ⟨C,hc,h⟩:= R.cost K p.tsupport_subset; exact (h _ (show tsupport (unpack U p).val⊆ K from Set.Subset.rfl) hm).integrated

def priceMap : 𝓓(U,ℂ) →ₗ[ℂ] X where
   toFun p:= ∫ x, P x (unpack U p)
   map_add' p q:= by simp_rw [map_add, integral_add (R.readable p) (R.readable q)]
   map_smul' a p:= by simp_rw [map_smul, integral_smul,RingHom.id_apply]
-- use in the entire ambient geometry

def record : 𝓓(U,ℂ) →L[ℂ] X:= ⟨R.priceMap, MultipleContact.cont_mk (j:=n) (fun K h=> by
    obtain ⟨C,hc,hC⟩:= R.cost K h; refine ⟨C,fun g t ht=> (hC (unpack U (TestFunction.ofSupportedIn h g)) (?_) (converted.mp ht)).holds⟩; exact g.tsupport_subset)⟩
omit [FiniteDimensional ℝ E] [CompleteSpace X] in
lemma recorded (p:𝓓(U,ℂ)) : R.record p= ∫ x, P x (unpack U p) := rfl
end Charge

variable [BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable {k : ℕ}{G: Gauge}{C: Family G}{F : Extraction.Order}{S: Table C.book}{Z: Final C F S}
variable {W I : Type}
variable {g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k} {Q : Pieces g}{d : Fin k→ℕ} {M : Devices Z.sector.derivatives}
local notation "GN" => Normal.Group k
-- any region derivative estimate for the entire kernel yields the same order globally.
def majorKernel (P:E→ₗᵢ[ℝ] Points k)(g : GN)(M : Devices Z.sector.derivatives)(t:Cells S d)(α : Viewers Z)(o : Points k)(s:ℝ)(x:E) : SmoothTests E→ₗ[ℂ] ℂ:= (readExpr M.basis (spectator Z α)).comp (Normal.under x (parcel ((waySystem P M o d t).full P s) (root g)))
omit [MeasureSpace E] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma major (P:E→ₗᵢ[ℝ] Points k)(g : GN)(M : Devices Z.sector.derivatives)(t:Cells S d)(α : Viewers Z)(o : Points k)(s:ℝ)(x:E)(f:SmoothTests E) : majorKernel P g M t α o s x f= kernel P g M t α o s f x:= rfl
lemma global_charge {o : Points k} (h : plane g ≤ LinearMap.range P.toLinearMap) (hp : Collapsed g o) (t : Cells S d) (α : Viewers Z){s B : ℝ} (hb : B∈ Ioc (0:ℝ) 1) (hz : B ≤ M.clearance (∑ i,d i+0)) (hh : 0<s ∧ 2*s ≤ B) (H : Services C F S): Charge (majorKernel P g M t α o s) ⊤ (totalTestOrder d g):= by
   constructor; intro K hK; obtain ⟨A,hA,hg⟩:= glues_total M H t α h hp K.isCompact hb hz hh; exact ⟨A,hA, fun i _ hm h=>hg i _ hm h⟩
variable {r : Route P Q I W}
def minorKernel (M : Devices Z.sector.derivatives)(r:Route P Q I W)(D : Reader E W X k Z.sector.derivatives)(T : W→ Cells S d)(f : Menu k)(w : W) (x : E) : SmoothTests E→ₗ[ℂ] X:= (D w x).comp (Normal.under x ((r.components M T w).election P (r.length w) f Q))

omit [MeasureSpace E] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X] [CompleteSpace X] in
lemma minor (r:Route P Q I W)(D : Reader E W X k Z.sector.derivatives)(T : W→ Cells S d)(f : Menu k)(w : W) (x : E)(p:SmoothTests E): minorKernel M r D T f w x p= r.windings M D T f w p x:= rfl
-- no assumption on constancy of frames when `w` is variable in `R`; use separately per reading
omit [MeasureSpace E] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ E] in
private lemma resized_charge {U : Set E} (A:E≃L[ℝ] E) (h : IsCompact U)(n : ℕ): ∃ C>(0:ℝ),∀ (g:SmoothTests E){c:ℝ},tsupport g.val⊆ U → Jet n univ g.val c→ Jet n univ (composed A g).val (C*c):=by
    let V:= A ⁻¹' U; obtain ⟨B,hB,hK⟩:= controls A.toContinuousLinearMap.contDiff (A.toHomeomorph.isCompact_preimage.mpr h : IsCompact V) n; refine ⟨(n.factorial:ℝ)*B^n,by have he:=zero_lt_one.trans_le hB; positivity,fun g c hc h'=> ?_⟩; apply ((hK.compose h' hB A.toContinuousLinearMap.contDiff (infSmooth g)).mono (le_of_eq (by ring))).recover ((support_comp (⇑A) A.continuous g.val).trans (Set.preimage_mono hc))

variable [Fintype I]
omit [IsScalarTower ℝ ℂ X] [NormedSpace ℝ X] in
lemma local_charge (v:Opens E)(w:W)(hv:(v:Set E)⊆ r.stage w)(H : Services C F S){T : W→ Cells S d} (hT : Given T)(hm : r.Authority M d)(f:Menu k) {D: Reader E W X k Z.sector.derivatives}{B:W→ℝ} (h : Loan Z M r B D): Charge (minorKernel M r D T f w) v (stairs d Q):= by
   constructor; intro K hK; obtain ⟨C,hC,hF⟩:= resized_charge (r.frame w) K.isCompact (stairs d Q); obtain ⟨γ,hγ,hε,hw⟩:= desired_budget 1 zero_lt_one Q; obtain ⟨A,hA,hA'⟩:= achieved M r T D H h hm hT hε; let X:=r.bag d B w (generosity Q γ); let P':= shadow Q f γ; have hX:0<X:= r.bag_pos w d (h.currency.pos w (Set.mem_univ _)); have hp:0<P':= Finset.prod_pos (f:= fun j=>kick f j γ) (fun i _=>kick_pos i f)
   exact ⟨A*C*X* P',by positivity,fun p m hv' hm=> (hA'.estimates f w p (hv'.trans (hK.trans hv)) (hF p hv' hm)).mono (le_of_eq (by unfold X P'; ring))⟩
end YM.Contacts.Solstice
