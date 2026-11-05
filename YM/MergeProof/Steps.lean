import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.FromWords
import YM.MergeProof.Dreams
import YM.MergeProof.Lakes
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Kitchen

/-!
Combine log and covered gas purchases with payout in *independent* leaves.
Adapted Mallow.Veranda, Charity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
local notation "X'"=> swing Q L μ R.beta x C

variable (hR:Plot M Y rA) {e d B:ℝ} {j k : ℕ} (hB: Bikes Q L μ x a e B j k)
set_option quotPrecheck false
--
local notation "p₀"=> fun i:Y.ThinP=> tune M Y rA 0 k i.val
local notation "p₁"=> fun i:Y.ThickP=> tune M Y rA 1 0 i.val
local notation "P₀"=> pledgeA L Q μ x B j k
local notation "P₁"=> Charity.daisD Q L μ x k
local notation "VQ" => pledgeQ L Q μ x B j k
local notation "E0" => Q.mark L μ x
local notation "ρ"=> sailUp Q L x

open Mallow Refrain Switch Letter
variable (U:Config G c) (X : Forest S.ratio) (hb:0 ≤ B)
local notation "Z" => ways rA
local notation "v" t:max u:max=> color M Y χ U (Z t u)
include hb hB hR χ
lemma sizes : Summable (bold M Y rA k) ∧ Summable (lace M Y rA k):=by
  constructor
  · refine Charity.everyoneN Y.library _ (fun i=>(fairs M Y χ rA hR i k).rocket) (bright M Y χ rA hR hB hb) ?_ hB.posts
    intro i hi; unfold bold at hi; split at hi
    next hn=> obtain ⟨j,hj⟩:=hn.2.1;exact Finset.Nonempty.mono (subset_biUnion_of_mem Y.bookFoot hj) (chapter_ne Y _)
    next=> exact (hi rfl).elim
  exact Charity.everyoneN (fun i=>Y.bookFoot (.inr i)) _ (fun i=>(fair M Y χ rA hR i k).rocket) (lucent M Y χ rA hR hB hb) (fun i _=> chapter_ne Y _) (add_nonneg hB.posts hB.allow.le)

lemma assembled (t : ℝ)(ht:t∈Set.Icc (0:ℝ) 1)(u:Finset ι) :
    let g:= color M Y χ U (ways rA t u); let LV:=Y.homesteadMill g
    HasSum (fun p=> overhead (prism T x χ o.K U X) R Q.table * LV * Y.canopyMill U g p) (S.push R.beta (buy M (Z t u) S) U)∧
      0<LV ∧ Real.exp (logSum Y.seam (Y.entriesMill g))=LV:=by
   intro pF LV; obtain ⟨hx,hv,hh⟩:=Palette.field M Y χ rA hR hB hb
   have hw : 0≤a+e:= add_nonneg hB.posts hB.allow.le
   have hp : Ready Y.smallAt (radiusB x) (fun i=> ‖Y.entriesMill pF i‖) (a+e) P₀ e ρ:=
     ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,fun _=>norm_nonneg _,AbsoluteSums.Labels.raise_prices _ _ (fun _=> norm_nonneg _) hx.2.2.2.2.2 (fun i=>Paid.tasting (aca M Y χ rA hR i k) U t ht u)⟩
   have he:= Y.threshold_logMill pF hp hw
   have hz: Summable (Y.depositsMill pF) := Summable.of_norm_bounded (Charity.everyoneN Y.largeAt _ (fun i=> Switch.Paid.rocket (ack M Y χ rA hR i)) hv (fun i _=>i.2.1) hw) (fun i=> Paid.tasting (ack M Y χ rA hR i) U t ht u)
   exact ⟨Y.convoyMill χ U pF X (fun i hi=> ⟨(springs M Y χ U i _ hi).1,(springs M Y χ U i _ hi).2.2⟩) (pushed M Y χ U (Z t u) X) hp hz hw, (by unfold LV; rw [← he.2]; exact Real.exp_pos _), he.2⟩

omit hb hB hR
variable {R':RG.Rep G f} (J : Cash W x μ L Q o C T R')(D:Match.Alliance J Y 1 0) (V:BudgetPoint)
variable (E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ)(hx: V.threshold=Pressure.temp x)
open Ovens Progress.DirectedRecipe

def shootK (r:ι→ℝ): Code G c:=stuff (Refrain.visa J D) (fun i U=> Y.smilesMill U (color M Y χ U r) i.val)
abbrev shoot (t:ℝ)(p:Finset ι): Code G c:= shootK M Y χ J D (Z t p)
local notation "VB"=> Refrain.read J D χ E t'
lemma at0 : shootK M Y χ J D (fun _=>0)= (VB).K:=by
  funext i V; by_cases he:i∈Set.range (Refrain.visa J D)
  · obtain ⟨y,rfl⟩:=he; unfold shootK; rw [stuffed,muted]; exact (Refrain.crowned J D χ V y).symm
  unfold shootK; rw [blank _ _ he]; change 0=Refrain.fuse J D χ (Refrain.badge J i) V; symm; by_contra hm; exact he (Refrain.resides J D χ V i hm)
include hx
lemma earned (θ : ι→ℝ) : (black VB (shootK M Y χ J D θ)).ForcedFamily V:=by
  let b:= shootK M Y χ J D θ; have he:=Refrain.qualified V J D χ E t' hx
  suffices h : ∀ i,Lattice.GaugeInvariant (b i)∧ Measurable (b i)∧ UsesFinal V.threshold ((Refrain.read J D χ E t').forced i|>.support) (b i) ∧ ∀ U,b i U≠0→ ((Refrain.read J D χ E t').forced i).eligible V.threshold U from ⟨fun i=> (h i).1,he.symtest,fun i=> (h i).2.1,he.meas_test,fun i=>(h i).2.2.1,he.reads_test,fun i=> (h i).2.2.2⟩
  intro i; by_cases hp:i ∈ Set.range (Refrain.visa J D); swap
  · unfold b shootK; rw [blank _ _ hp]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun _ h=>(h rfl).elim⟩
  obtain ⟨i,rfl⟩:=hp; have h := fun U=> smiling M Y χ θ U i.val; unfold b shootK; rw [stuffed]
  have hf:((Refrain.read J D χ E t').forced (Refrain.visa J D i)).support= Y.library i.val:= (Refrain.admitted J D i).1
  rw [hf,hx]; refine ⟨(h 1).2.2.1,(h 1).1,(h 1).2.1, fun U hu=>?_⟩
  unfold ForcedAddress.eligible; rw [hf,show ((Refrain.read J D χ E t').forced _).inventory=_ from (Refrain.admitted J D i).2,inter_comm]; refine ⟨((h U).2.2.2 hu).2.1.symm,?_⟩
  change Refrain.reserve J (Refrain.badge J (Refrain.visa J D i)) |>.extraTest U
  rw [Refrain.visited]; trivial

include hR hB hb
omit hx in
lemma ready (hZ:V.B=sx) : ∃ u' : ℕ→ℝ,(∀ i, Paid (fun U t u=> shoot M Y χ rA J D t u i U) (u' i)) ∧ Ac.Hit (fun i=> ((VB).forced i).support) V.B u' a (Real.exp (-E0)*(2*VQ)):=by
   let i:= Refrain.visa J D; let u':= fun a: Refrain.Leaf Y=> bold M Y rA k a.val
   refine ⟨stuff i u', fun z=> ?_,fun p=> ?_⟩
   · by_cases he:z∈Set.range i
     · obtain ⟨t,rfl⟩:=he; unfold i shoot shootK; simp_rw [stuffed]; exact fairs M Y χ rA hR t.val k
     unfold shoot shootK; simp_rw [blank _ _ he]; unfold i at he; simp_rw [blank _ _ he]; exact paidZero (U:=Config G c) (ι:=ι)
   refine transfer_budget i ?_ ?_ (budget_pull (fun i:Refrain.Leaf Y=>Subtype.val i) Subtype.val_injective (bright M Y χ rA hR hB hb p))
   · intro z; rw [stuffed,hZ]; dsimp only; simp_rw [show ((Refrain.read J D χ E t').forced (i z)).support=_ from (Refrain.admitted J D z).1]; rfl
   intro j hj; rw [blank _ _ hj]; split; rw [zero_mul]; rfl

lemma scored (w:Finset ι)(t₀:ℝ)(ht:t₀∈Set.Icc (0:ℝ) 1) : HasSum (fun i : Finset ℕ => overhead (prism T x χ o.K U X) R Q.table * Y.homesteadMill (Palette.color M Y χ U (ways rA t₀ w)) * (black (Refrain.read J D χ E t') (shoot M Y χ rA J D t₀ w)).gasOccurrence V i U) (S.push R.beta (buy M (ways rA t₀ w) S) U):=by
  have hh := (assembled M Y χ rA hR hB U X hb t₀ ht w).1; let XX:= prism T x χ o.K U X
  let t:= color M Y χ U (ways rA t₀ w); let c:= overhead XX R Q.table * Y.homesteadMill t
  let B := black (Refrain.read J D χ E t') (shootK M Y χ J D (ways rA t₀ w))
  let f (j:Finset ℕ):= c*B.gasOccurrence V j U; let g (w:Finset Y.Chainbook):= c* Y.canopyMill U t w; let F(z:Finset (Refrain.Leaf Y)):= z.map (Refrain.visa J D); let K(z:Finset (Refrain.Leaf Y)):=z.map (Embedding.subtype _)
  have hc(y):=smiling M Y χ (ways rA t₀ w) U y
  have hz w(hw:w∉ Set.range K):g w=0:=by
    by_contra hn; have he:=right_ne_zero_of_mul hn
    unfold Cash.canopyMill at he; split at he
    next hv=>
      apply hw; let P:= w.subtype (fun i:Y.Chainbook=> (Y.inventory i.1.toLeft).Nonempty)
      refine ⟨P,?_⟩; unfold K; ext i; constructor
      · intro hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp hi; exact mem_subtype.mp hj
      intro hi; let a:Refrain.Leaf Y:=⟨i,(hc i|>.2.2.2 (fun h=> he (prod_eq_zero hi h))).1⟩; exact mem_map_of_mem (Embedding.subtype _) (show a∈P from mem_subtype.mpr hi)
    next h=> exact he rfl
  have hr := ((show Injective K from map_injective _).hasSum_iff hz).2 (show HasSum g _ from hh)
  apply ((show Injective F from map_injective _).hasSum_iff (f:=f) ?_).1
  · refine hr.congr_fun fun i=>congr_arg (c*·) ?_
    have ht' : B.admissible V U (F i) ↔ ((K i:Set _) ).PairwiseDisjoint Y.library ∧ Y.eruptedPool U (K i):= Refrain.present V J D χ E t' U i hx
    have hp (z:Refrain.Leaf Y): B.K (Refrain.visa J D z) U= Y.smilesMill U t z.val:=by unfold B black; dsimp only; unfold shootK; rw [stuffed]
    unfold Activities.gasOccurrence Cash.canopyMill; by_cases h' : B.admissible V U (F i)
    · rw [if_pos h',show ∏j∈F i,B.K j U=∏ j∈K i,Y.smilesMill U t j from (by unfold F K; rw [prod_map, prod_map]; exact prod_congr rfl fun y _=>hp y)]
      split; · rfl
      next ht=> by_contra hm; obtain ⟨hx,hu⟩:=ht'.1 h'; exact ht ⟨⟨Refrain.parted Y hx,fun i hi=> (hc i|>.2.2.2 (fun h=> hm (prod_eq_zero hi h))).2.2,hx⟩,hu⟩
    rw [if_neg h',if_neg (fun hj=> h' (ht'.2 ⟨hj.1.disjoint,hj.2⟩))]
  intro i hi; unfold f Activities.gasOccurrence; split
  next=>
    by_contra hh; apply hi
    let e:=Refrain.visa J D; refine ⟨Finset.preimage i e e.injective.injOn,?_⟩
    unfold F; ext a; constructor
    · intro ha; obtain ⟨j,hj,rfl⟩:= Finset.mem_map.mp ha; exact Finset.mem_preimage.mp hj
    intro ha; by_cases hp:a∈ Set.range e
    · obtain ⟨j,rfl⟩:=hp; exact mem_map_of_mem e (Finset.mem_preimage.mpr ha)
    exact False.elim (right_ne_zero_of_mul hh (prod_eq_zero ha (by change stuff e (fun (i:Refrain.Leaf Y) U=>Y.smilesMill U (color M Y χ U (ways rA t₀ w)) i.val) a U=0; rw [blank _ _ hp]; rfl)))
  next=> rw [mul_zero]
lemma chorus (w:Finset ι)(t₀:ℝ)(ht:t₀∈Set.Icc (0:ℝ) 1) : overhead (prism T x χ o.K U X) R Q.table * Y.homesteadMill (Palette.color M Y χ U (ways rA t₀ w)) * (black (Refrain.read J D χ E t') (shoot M Y χ rA J D t₀ w)).gas V U= S.push R.beta (buy M (ways rA t₀ w) S) U:= by
   have hz:= scored M Y χ rA hR hB U X hb J D V E t' hx w t₀ ht; have hf:= hz.tsum_eq; rw [tsum_mul_left] at hf; exact hf
end YM.Merge.Palette
