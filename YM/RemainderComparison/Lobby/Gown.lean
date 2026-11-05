import YM.RemainderComparison.Lobby.Torn

/-!
 # Structure Before-EXP closure. All tests align once. Masks identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lobby
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal WickReps
open Progress.DirectedRecipe
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {ι β I J:Type} {α:Type*} {c f:Side} [DecidableEq β] {Jm:Marker.Census β} {Y: Stars→Side}
variable (O:Manor G c ι α I) (P:BudgetPoint)(root:ι→Support c) {K : Set I} (k:ℕ)
variable (a:α)(Z:Set ι)(z:ι→Marker.Poly Jm)
open Mosaic Serif Manor Flues
variable (s:Finset I){r w D t:ℕ} {E a₀ b₀ e:ℝ}
variable (B : O.Basis s r)(Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (fa:α→∀ i:Stars, Offer G (Y i))
local notation "Vʼ" => ranging O P s B Q fa k D
local notation "Xʼ" => (mansion Q fa k : Manor G c ι α (Site c))
variable {root}
variable (V:Config G c) (T: Manor.Quarry O K J root r) (hv:2*w≤f.val)(g:α→J→ Config G f→ℝ)(u:J→ℝ)
local notation "Kʼ"=> vessel O T hv g u D
local notation "Vˮ" => blooming O P T hv g u D

lemma sector_sum {fQ:I→ Marker.Poly Jm} (ht: (walls O T)⊆ ((s:Set I)ᶜ))(hp:Summable fQ) :
     let X:= ((s:Set I) ∪ walls O T)
     (∑' i,fQ i) = ∑ i∈s,fQ i + ∑' i: walls O T,fQ i.val + ∑' i: ↥(Xᶜ),fQ i.val:=by
   intro X; let S: Set I:=↑s; let U:=walls O T
   have h : Disjoint S U:= Set.disjoint_left.mpr (fun _ ha he=>ht he ha)
   have hf := Summable.tsum_add_tsum_compl (f:=fQ) (s:=X) (hp.subtype X) (hp.subtype _)
   let φ:= fun i:S=> fQ i.val; let g:= fun i:U=> fQ i.val; let v i:=fQ (i:X).val
   let e:= Equiv.Set.union h
   suffices hz: (∑' i:X,v i)=∑ i∈s,fQ i+∑' i:U,fQ i.val by unfold v at hz; nth_rw 1 [← hf]; rw [hz]
   have hs : (∑ i: ↑s, fQ i.val)=∑ i∈s,fQ i:= sum_coe_sort ..
   have hU : v ∘ e.symm = Sum.elim φ g:=by funext i; cases i<;> rfl
   calc _ = ∑' i,v ((e.symm) i):= (e.symm.tsum_eq v).symm
        _ = (∑' i:S,φ i) + (∑' i:U,g i):=by change (∑' i,(v ∘ e.symm) i)= _; rw [hU]; exact (Summable.tsum_sum (f:=Sum.elim φ g) (hp.subtype S) (hp.subtype U))
        _ = _:= by rw [← hs,← tsum_fintype (L:=.unconditional _)]; rfl

-- Leaks reconstruction in any compressor.
local notation "Sʼ" => ((s:Set I)∪walls O T)
local notation "Aʼ"=> Vesuvius.Assembles Vʼ Vˮ
variable (F' : (Site c ⊕ J) ↪ ℕ)
local notation "Pu"=> Vesuvius.spring (Vesuvius.Assembles Vʼ Vˮ) F'
variable {η:β→ℝ} {p:ℕ} {u' u₀ v v₀ τ γ:ℝ}
local notation "Sa" => Vesuvius.books a Z z
lemma throne (hp : Expulsion O s P B Q D k fa γ u') (hf: Nimble O T P Kʼ (O.zephyr T P hv g u D) γ v)(hh:∀ i,0< Verse.load Z (T.sign i)) : Vesuvius.Works P root Z Aʼ γ u' v:=by
    have hp := hearth O P k Z s B Q fa (root:=root) hp; have hv := resonant O P Z T hv g u hh hf
    convert! Vesuvius.assembled P root Z _ _ hp hv using 1 <;> simp
lemma berth (hp : Expulsion O s P B Q D k fa γ u') (hf: Nimble O T P Kʼ (O.zephyr T P hv g u D) γ v)(hh:∀ i,0< Verse.load Z (T.sign i)) : (Vesuvius.spring (Aʼ) F').Rises P root ∧ (Vesuvius.spring (Aʼ) F').Treasures Z p P.B γ u' v:= Vesuvius.inflate _ _ p _ _ _ (throne O P k Z s B Q fa T hv g u hp hf hh)

-- Portion together: overhead externally true identity.
set_option maxHeartbeats 500000 in
lemma onceP (H:(Aʼ).Works P root Z γ u' v)(hγ:0 ≤ γ) (he: (walls O T)⊆ (s:Set I)ᶜ)(hS:∀ i∈s,O.marks i=0) (hZ:Serif.Chorus Jm η Z z p)
    (hb:Summable (O.paint P Z z a V))(hd: Summable ((Kʼ).paint P Z z a V)) :
    ∑' i,O.paint P Z z a V i= (Complex.ofReal (∑ x:Site c,O.sector a s B x 1)) • (1:Marker.Poly Jm)+
       (∑' i, (Xʼ).paint P Z z a V i)+(∑' i,(Kʼ).paint P Z z a V i)+Manor.basin O P ((↑s∪walls O T)ᶜ) Z z a V+
          (∑' i,(Vesuvius.spring Aʼ F').plume Z z a V i):=by
    obtain ⟨h,hA⟩:=Vesuvius.plastic P root p a Z z Aʼ F' H hγ hZ V
    have hg: Summable (Sa Vʼ V):= show Summable (fun i=> Sa Aʼ V (Sum.inl i)) from hA.comp_injective Sum.inl_injective
    have hG: Summable (Sa Vˮ V):= show Summable (fun i=> Sa Aʼ V (Sum.inr i)) from hA.comp_injective Sum.inr_injective
    have ht:= sector_sum O s T he (fQ:=O.paint P Z z a V) hb
    dsimp only at ht; let p':= Sum.elim (Sa Vʼ V) (Sa Vˮ V); have hu: Sa Aʼ V=p':= by funext i;cases i<;>rfl
    have hv': (∑' i,p' i)=(∑ i:Site c,Sa Vʼ V i)+ (∑' i: J,Sa Vˮ V i):= by rw [←tsum_fintype (L:=.unconditional (Site c))]; exact Summable.tsum_sum (f:=p') hg hG
    have hm := adepts (fQ:=O.paint P Z z a V) O T (hb.subtype (walls O T)); have hz (j):=sun_sum O P a Z z V T hv g u j D; simp_rw [hz] at hm
    rw [ht, Lobby.treeWard O P k a Z z s B Q fa V hS D, h.tsum_eq, hu, hv', ← hm.tsum_eq, Summable.tsum_add hd hG, tsum_fintype (L:=.unconditional (Site c))]; unfold Manor.basin; abel
lemma once (hp:Expulsion O s P B Q D k fa γ u')(hf: Nimble O T P Kʼ (O.zephyr T P hv g u D) γ v)
    (hh:∀ i,0< Verse.load Z (T.sign i))(hγ:0 ≤ γ) (he: (walls O T)⊆ (s:Set I)ᶜ)(hS:∀ i∈s,O.marks i=0) (hZ:Serif.Chorus Jm η Z z p)
    (hb:Summable (O.paint P Z z a V))(hd: Summable ((Kʼ).paint P Z z a V)) :
    ∑' i,O.paint P Z z a V i= (Complex.ofReal (∑ x:Site c,O.sector a s B x 1)) • (1:Marker.Poly Jm)+
       (∑' i, (Xʼ).paint P Z z a V i)+(∑' i,(Kʼ).paint P Z z a V i)+Manor.basin O P ((↑s∪walls O T)ᶜ) Z z a V+
          (∑' i,(Vesuvius.spring Aʼ F').plume Z z a V i):=by
    exact Lobby.onceP O P k a Z z s B Q fa V T hv g u F' (throne O P k Z s B Q fa T hv g u hp hf hh) hγ he hS hZ hb hd
end YM.RemainderComparison.Lobby
