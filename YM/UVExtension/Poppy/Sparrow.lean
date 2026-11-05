import YM.UVExtension.Poppy.Fountain
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Poppy
open Finset Set Function Filter MeasureTheory Analysis Extraction Lattice Fallow Harvest
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n p:ℕ}
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
-- Proof of uniform full real derivative bounds at any fixed period, even offset-dependent cuts.Slice minted.Once with readouts.
def Nutrition (U:Cellar S t R)(d H p:ℕ)(r:ℝ) := 0<r ∧ ∀ v:Keys S,(∀ᶠ i:ℕ in atTop,|(v i p).val|≤ r) → ∀ i:ℕ,i ≤ d+H→ Slicing (U.yard v) i p
variable {d:ℕ}{r:ℝ}(J:Nutrition U d (k+1) p r) (hu:∀ i, (w i).1 ≤ d)
lemma garnish {X:Type*}(x:X)(F:ℕ→ X→ ℝ→ Prop)(hm:∀ i x z z', z≤z' → F i x z→F i x z')(h:∀ v:ℕ→ X,∃ r:ℝ,∀ᶠ j:ℕ in atTop,F j (v j) r) : ∃ r:ℝ,∀ᶠ j:ℕ in atTop,∀ x,F j x r:=by
   by_contra he
   have hv (r:ℝ)(m:ℕ):∃ i:ℕ,m≤ i ∧ ∃ x,¬ F i x r:=by contrapose! he; exact ⟨r,eventually_atTop.mpr ⟨m,he⟩⟩
   choose k hk u hx using fun (i:ℕ)(m:ℕ)=>hv (i:ℝ) m
   let g(i:ℕ):ℕ:= Nat.rec (k 0 0) (fun n i=> k (n+1) (i+1)) i
   let b:= fun i=> g (i+1)
   have hz: StrictMono g:= strictMono_nat_of_lt_succ fun i=> show g i< k (i+1) (g i+1) from hk (i+1) _
   have hb:StrictMono b:= hz.comp (show StrictMono (fun (i:ℕ)=>i+1) from fun _ _ h=> by simp [h]); let v (i:ℕ):= if h:∃ j,b j=i then (fun j=> u (j+1) (g j+1)) (Classical.choose h) else x
   have hr(i):v (b i)=u (i+1) (g i+1):=by unfold v; rw [dif_pos (show ∃ j,b j=b i from ⟨i,rfl⟩),hb.injective (Classical.choose_spec (show ∃ j,b j=b i from ⟨i,rfl⟩))]
   obtain ⟨c,hc⟩:= h v; obtain ⟨i,hi,h'⟩:= ((hb.tendsto_atTop.eventually hc).and (tendsto_natCast_atTop_atTop.eventually_ge_atTop c)).exists
   rw [hr] at hi; exact hx (i+1) (g i+1) (hm _ _ _ _ (h'.trans (Nat.cast_le.mpr i.le_succ)) hi)

-- ALL fields actual cutoff sectors. roof even across Arc symbols. Consumers crop at all tests once supports fit.
def harbor (p N:ℕ)(z:Rose S)(w:Fin n→ (Hearth.roster U).Token) (x: Tabletop n):= Hearth.served N p U z n w (wrap (A.B.a.S.side N p) ∘ x) -- include U implicit
lemma anchoredW (v:Keys S) (N p:ℕ) (he:∀ i,t (w i).fst ≤ N): Extraction.lifted (U.yard v) N p w= harbor p N (v N p) w:= funext fun x=> Hearth.cordial N p U v n w he _
include h B
lemma nourishing (d H:ℕ): ∀ᶠ p in atTop, ∃ r,Nutrition U d H p r:=by
   let X:= Finset.range (d+H+1)
   filter_upwards [(eventually_all_finset X).mpr fun i _=> (B.ripe S R h i)] with p hp
   choose! r hr hX using hp
   let k:= X.inf' (show X.Nonempty from ⟨0, Finset.mem_range.mpr (by omega)⟩) r
   refine ⟨k,Finset.lt_inf'_iff .. |>.2 hr, fun v hv i hi=>?_⟩
   have he:i∈X:=Finset.mem_range.mpr (by omega); exact hX i he v (hv.mono fun n hn=> hn.trans (Finset.inf'_le _ he))
omit h
include hu J
lemma hectare {l:List (Axel n)} (hl:l.length≤ k+1) {Z:Set (Points n)}(he:IsCompact Z)(hp:Z⊆NoHit A.B.a.S p n) : ∃ C:ℝ,0 ≤ C ∧∀ᶠ N in atTop,∀ z:Rose S,|z.val| ≤ r→ ∀ o, Extraction.tag (A.B.a.S.a N) o∈Z→ ‖rake (A.B.a.S.a N) (harbor p N z w) l o‖ ≤ C:=by
   let D:= {z:Rose S // |z.val| ≤ r}; let f(i:ℕ)(z:D)(b:ℝ):Prop:= 0 ≤ b ∧∀ o,Extraction.tag (A.B.a.S.a i) o∈Z → ‖rake (A.B.a.S.a i) (harbor p i z.val w) l o‖≤b
   have hk(v:ℕ→D): ∃ b,∀ᶠ i in atTop,f i (v i) b:=by
      let V':Keys S:= fun j _=> (v j).val; have hp' := offers (p:=p) B w k (v:=V') ?_; swap
      · intro i j hK hx; exact J.2 V' (Eventually.of_forall fun j=>(v j).property) _ (by have h:=hu i; omega)
      obtain ⟨b,hb,hS⟩:= hp'.fees l hl Z hp he; refine ⟨b,?_⟩; filter_upwards [hS,eventually_all.mpr (fun i=>eventually_ge_atTop (t (w i).fst))] with i hi hT; rw [anchoredW w _ _ _ hT] at hi; exact ⟨hb,hi⟩
   let d:D:= ⟨rose0 S,by change |(0:ℝ)|≤_; simp [J.1.le]⟩
   obtain ⟨r,hr⟩:= garnish d f (fun i x y z h hx=>⟨hx.1.trans h,fun o ho=> (hx.2 _ ho).trans h⟩) hk
   obtain ⟨w,hw⟩:=hr.exists; exact ⟨r,(hw d).1,hr.mono fun i hi x hx=> (hi ⟨x,hx⟩).2⟩
include h he
lemma mature (hp: ∀ᶠ i in atTop,|(v i p).val| ≤ r) : ∃ f,Poppy.Margins (U.yard v) n p k w f:=by
   refine Poppy.blossoms h B z he w k ?_; intro i j _ hj; exact J.2 v hp j (by have h:= hu i; omega)
end YM.UVExtension.Poppy
