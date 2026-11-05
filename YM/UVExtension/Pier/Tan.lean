import YM.MergeProof.Platter
import YM.UVExtension.Pier.Power
/-! # In-place packs on the dormant keys are analytic also under singleton
 disconnected root prices. Nothing here from turns around the torus.
 Glassing extraTests is scratch: prove exact in the given encoding. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open Planned.GuardedAtom Guard MergeProof
open Lamppost Rafter Copse
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {D Z:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z](T:Opening D Z)
variable {n:Side} (p:BudgetPoint) (d:ℕ) (X:Support n)
variable {G:Gauge}(A:Activities G n)
open Push.Local
set_option quotPrecheck false
local notation "ξ"=> p.supportExponent
local notation "P"=> Pack A X
local notation "q"=> Copse.worth d p.B ξ
local notation "a"=> p.B
lemma partsW (i:Pack A X): cover d p.B (X∪i.val.biUnion (Local.patch A)) ≤ cover d p.B X + ∑ j∈i.val,coverNumber p.B (Local.patch A j):=by
   suffices hf:∀ f:Finset ℕ, f⊆ i.val→ cover d p.B (X∪ f.biUnion (Local.patch A))≤ cover d p.B X+∑ j∈f,coverNumber p.B (Local.patch A j) from hf _ (Finset.Subset.refl _)
   intro f; induction f using Finset.induction_on with
   | empty => simp
   | insert k s hk ih=>
      intro hv; obtain ⟨x,hx,hA⟩:= Finset.not_disjoint_iff.mp (i.2.hits k (hv (Finset.mem_insert_self ..))); rw [Finset.biUnion_insert, Finset.union_left_comm,Finset.sum_insert hk,add_left_comm]
      exact (Copse.linked d a (Finset.mem_union_left _ hx) hA).trans (Nat.add_le_add_left (ih (Finset.insert_subset_iff.mp hv|>.2)) _)
lemma marg (i:Pack A X)(u t:ℕ→ℝ)(c:ℝ)(h:∀ i,0≤u i)(hc:0 ≤ c)(he:∀ j∈i.val,t j=p.mass (Local.patch A j) (u j)): q (X∪ i.val.biUnion (Local.patch A))*(c*∏ j∈i.val,u j)≤ q X*c* ∏ j∈i.val,t j :=by
    rw [Finset.prod_congr rfl he]; simp only [BudgetPoint.mass,Finset.prod_mul_distrib,← Real.exp_sum,← Finset.mul_sum]; unfold worth; rw [mul_mul_mul_comm (Real.exp _) c,← Real.exp_add,← mul_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast partsW p d X A i) p.exponent_pos.le)) (mul_nonneg hc (Finset.prod_nonneg fun j _=>h j))
variable {w c:ℝ}
lemma orient {u:ℕ→ℝ}(h:∀ i,0≤ u i)(hf:∀ y:Site n,SumBudget (fun i=> if y∈Local.patch A i then p.mass (Local.patch A i) (u i) else 0) w)(hc:0 ≤ c): SumBudget (fun i:Pack A X=> q (X∪ i.val.biUnion (Local.patch A))*(c*∏ j∈i.val,u j)) (q X*c*(Real.exp ((X.card:ℝ)*w)-1)) := by
   let y (i:ℕ):= if Disjoint X (Local.patch A i) then 0 else p.mass (Local.patch A i) (u i); have he: SumBudget y ((X.card:ℝ)*w):= sumBudget_meeting X (fun i=> (h i).trans (p.loMass _ _ (h i))) hf
   refine sumBudget_mono (sumBudget_mul_left (sumBudget_subtype (Packs A X) (sumBudget_exponential he)) (mul_nonneg (Real.exp_pos _|>.le) hc)) (fun i=> mul_nonneg (Real.exp_pos _).le (mul_nonneg hc (Finset.prod_nonneg fun j _=>h j))) ?_ le_rfl; intro i; dsimp only; rw [if_pos i.property.nonempty]; exact marg p d X A i u y c h hc (fun j hj=> if_neg (i.property.hits j hj))
local notation "C"=> Config G n
-- Want predict pack name and order repeated even when activity array changes over disk.
variable (s:Berths p A (fun _:Unit=>X))
local notation "R" => Letters A (fun _:Unit=>X)
private def glass (A:Activities G n): Activities G n:= { A with
    forced:=fun i=>{A.forced i with extraTest:=fun _=>True} }
private lemma works {v:ℝ} (h:A.Valid p w v): (glass A).Valid p w v:=by
    let K:=glass A; have ht:=h.forced; have he: K.ForcedFamily p:=⟨ht.sym,fun _ _ _=>Iff.rfl,ht.meas, fun _=> MeasurableSet.univ,ht.reads,fun _ _ _ _ _=>rfl,fun i U h=>⟨(ht.permit i U h).1,trivial⟩⟩
    refine ⟨⟨h.regular.smooth,h.regular.at_flat,h.regular.vanish⟩,he,fun s x=>?_,h.boundE,h.boundK⟩
    obtain ⟨m⟩:= h.moves s x; exact ⟨m.ep,m.kp,m.reg_site,m.reg_support,m.forced_support,m.forced_inventory,fun _ _=> Iff.rfl,m.valuesE,m.valuesK⟩
-- layout catches same index.Y both before and after glass
variable (B : Activities G n) (hk:B.forced=A.forced)
-- match labels.Only later holders.
private def duo : Pack B X ≃ Pack A X:= Equiv.subtypeEquiv (Equiv.refl _) (fun f=>by
    have h:Local.patch B=Local.patch A:=by unfold Local.patch;rw [hk]
    constructor <;> rintro ⟨hn,hS,hT⟩
    · exact ⟨hn,Eq.mp (congr_arg (fun Y=>(f:Set ℕ).PairwiseDisjoint Y) h) hS,fun i hi=> congr_arg (fun Y=>¬Disjoint X (Y i)) h ▸ hT i hi⟩
    exact ⟨hn,Eq.mp (congr_arg (fun Y=>(f:Set ℕ).PairwiseDisjoint Y) h.symm) hS,fun i hi=> congr_arg (fun Y:ℕ→Support n=>¬Disjoint X (Y i)) h.symm ▸ hT i hi⟩)
private def arms: Pack (glass B) X≃ Pack A X:= (Equiv.subtypeEquiv (Equiv.refl _) (show ∀ f,Packs (glass B) X f↔ Packs B X f from fun f=> ⟨fun h=> ⟨h.1,h.2,h.3⟩,fun h=>⟨h.1,h.2,h.3⟩⟩)).trans (duo X A B hk)
private def crossed : Letters (glass B) (fun _:Unit=> X) ≃ R:= Equiv.sigmaCongrRight fun _=>arms X A B hk
private lemma totals (x: Letters (glass B) (fun _:Unit=>X)): (crossed X A B hk x).total=x.total:= by
    have h: Local.patch (glass B)=Local.patch A:=by change Local.patch B=Local.patch A; unfold Local.patch; rw [hk]
    exact congr_arg (fun t:ℕ→Support n=> X∪ (x.2.val).biUnion t) h.symm
private lemma keeps (x: Letters (glass B) (fun _:Unit=>X)): (crossed X A B hk x).keeps=x.keeps:= by
    have h: flagsFor (glass B)=flagsFor A:= by change flagsFor B=flagsFor A; unfold flagsFor; rw [hk]
    exact congr_arg (fun t:ℕ→Support n=> (x.2.val).biUnion t) h.symm

-- Actual encoding. construct one pack family once (real & complex).
private def pots : Local.Slots (glass B) (fun _:Unit=>X) where
    label:=(crossed X A B hk).toEmbedding.trans s.label
    support x:= by change (B.forced (s.label (crossed X A B hk x))).support= _; rw [hk]; exact (s.support _).trans (totals X A B hk x)
    inventory x:=by change (B.forced (s.label (crossed X A B hk x))).inventory = _; rw [hk]; exact (s.inventory _).trans (keeps X A B hk x)
    allows _ _:= trivial

variable {v:ℝ} (h:B.Valid p v w)(F:Config G n →ℂ) (hf: Attaches p.threshold X F) (ho:(0:Site n)∈X)
-- recipe uses no analytic morph S; just a single fixed array
private def garnish (g:ℕ→ Config G n→ℂ) := Function.extend s.label (fun i:R=> fun U=> if i.total ∩ flags p.threshold U=i.keeps then F U*∏ j∈i.bundle,g j U else 0) 0
local notation "p0"=>garnish p X A s F (fun i x=> (B.K i x:ℂ))
set_option quotPrecheck false
local notation "Q"=> pots p X A s B hk
private lemma peek: p0 = (pots p X A s B hk).pack p.threshold (fun _:Unit=>F):=by
    let KP:= crossed X A B hk; funext i; by_cases hx:i∈Set.range (Q).label
    · obtain ⟨z,rfl⟩:=hx; have ht: ((glass B).forced ((Q).label z)).eligible p.threshold = fun U=> (KP z).total∩ flags p.threshold U= (KP z).keeps:=by
          funext U; apply propext
          change (_=_∧ True) ↔ _
          rw [(totals X A B hk z), (keeps X A B hk z), show ((glass B).forced ((Q).label z)).support=_ from (Q).support z, show ((glass B).forced ((Q).label z)).inventory = _ from (Q).inventory z]; simp
      rw [Slots.pack_label]; unfold garnish; change Function.extend _ _ _ (s.label (KP z))= _; rw [s.label.injective.extend_apply]; unfold Slots.payload; dsimp only; rw [ht]; funext U; dsimp only; split_ifs <;> rfl
    rw [Slots.pack_none _ _ _ _ hx]; unfold garnish; rw [extend_apply']; rfl; rintro ⟨s,h⟩; obtain ⟨z,rfl⟩:= KP.surjective s; exact hx ⟨z,h⟩
include ho hk h hf
lemma season : Local.ForceFormat p B 0 (p0) ∧ ∀ U:Config G n,HasSum (fun i=> Local.gasMark p B U i (p0)) (F U*(B.gas p U:ℂ)) :=by
   rw [peek p X A s B hk]; have hz:= works p B h; let Q':= Q; let t(u:Unit):= F; let g:= Q'.pack p.threshold t; have he:= Q'.forceFormat hz.forced (fun _=>ho) (fun _=>hf)
   refine ⟨⟨fun i U hU=>?_,he.carried, he.invariant, he.supported, he.borel⟩,fun U=>?_⟩
   · have hu: (B.forced i).support∩flags p.threshold U=(B.forced i).inventory:= (he.forcing i U hU).1; refine ⟨hu,?_⟩
     obtain ⟨x,hx⟩: ∃ x,Q'.label x=i:= by by_contra H; exact hU (congr_fun (Slots.pack_none Q' p.threshold t i H) U)
     subst i; rw [hk] at hu ⊢; exact s.pass _ _ hu
   have hp: ∑' i:Unit,F U= F U := by simp
   have hu := Q'.recover p U t (fun _=>hf) hz (Summable.of_finite); unfold t at hu; rw [hp] at hu; exact hu

omit h hf hk
variable (V:D→ Activities G n)(hc:∀ i,(V i).forced=A.forced)(hv:∀ x,‖F x‖≤ c)
omit ho
include hc hv
set_option quotPrecheck false
lemma cackle (hw:Stalk (Concert.bell A.forced a ξ) T (fun i j U=> ((V i).K j U:ℂ)) w) :∃ g:D→ ℕ→ Config G n→ℂ,Stalk (nose (G:=G) (Local.patch A) d a ξ) T g (q X*c*(Real.exp ((X.card:ℝ)*w)-1)) ∧∀ i, g i=garnish p X A s F (fun j x=>((V i).K j x:ℂ)):=by
   obtain ⟨f,hf,hT,h⟩:=hw.rises; let H z:= garnish p X A s F (f z); let e:= s.label; refine ⟨H ∘ T.call,⟨H,fun i k=>?_,fun _=>rfl,fun z hz=>?_⟩,fun i=>?_⟩
   · by_cases hx:i∈ range e
     · obtain ⟨i,rfl⟩:=hx; unfold H garnish; dsimp only [e]; simp_rw [s.label.injective.extend_apply]; split; · exact fun s v hs hv hh=> DifferentiableOn.const_mul (DifferentiableOn.fun_finsetProd (fun i _=> hf i k s v hs hv hh)) _
       exact bumps _ _ (differentiableOn_const _)
     have hp z:H z i=0:= extend_apply' _ _ _ hx; simp_rw [hp]; exact bumps _ _ (differentiableOn_const _)
   · obtain ⟨u,hu,hP⟩:= (h z hz).afloat; have hV:0≤ c:= (norm_nonneg _).trans (hv 1)
     let y i:= extend e (fun i:R=> c*∏ j∈i.bundle,u j) (0:ℕ→ℝ) i
     have h₁: ∀ i,0≤ u i:= fun i=> hu i|>.1
     refine ⟨y,fun i=>?_,fun _=>?_⟩
     · by_cases hx:i∈ range e
       · obtain ⟨i,rfl⟩:=hx; have he: y (e i)= _ := e.injective.extend_apply (fun i:R=> c*∏ j∈i.bundle,u j) (0:ℕ→ℝ) i; rw [show y _=_ from he]
         have hY:= mul_nonneg hV (Finset.prod_nonneg (s:=i.bundle) (fun j _=> h₁ j)); refine ⟨hY,fun U=>?_⟩
         unfold H garnish; change ‖Function.extend e _ (0 : ℕ → C→ℂ) (e i) U‖ ≤ _; rw [e.injective.extend_apply]; split; next h=>
           rw [norm_mul,norm_prod]; exact mul_le_mul (hv _) (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=> (hu _).2 _)) (Finset.prod_nonneg fun _ _=> norm_nonneg _) hV
         rw [norm_zero]; exact hY
       rw [show y i=0 from extend_apply' _ _ _ hx]; refine ⟨le_rfl,fun U=>?_⟩; rw [show H z i=0 from extend_apply' _ _ _ hx]; simp; rfl
     have hh(z): SumBudget (fun j=> if z∈ Local.patch A j then p.mass (Local.patch A j) (u j) else 0) w:= by simpa only [Local.patch,BudgetPoint.mass,Concert.bell,ite_mul,zero_mul] using hP z
     let f(i:Pack A X): R:= ⟨(),i⟩
     refine sumBudget_pass e _ (sumBudget_sigma («a»:=fun _:Unit=>q X*c*(Real.exp ((X.card:ℝ)*w)-1)) ?_ ?_) ?_
     · intro x; cases x; have he(i:R): Local.patch A (e i)= i.total:= s.support i; simp_rw [y,e.injective.extend_apply]; change SumBudget (fun i=>q (Local.patch A (e (f i)))*(c*∏ j∈i.val,u j)) _; simp_rw [he]; exact orient p d X A h₁ hh hV
     · have hh: 0≤ q X*c*(Real.exp ((X.card:ℝ)*w)-1):= budget_nonneg (orient p d X A h₁ hh hV); exact ⟨fun _=>hh,.of_finite,by simp⟩
     · intro i hi; rw [show y i=0 from extend_apply' _ _ _ hi, mul_zero]
   change garnish p X A s F (f _)=_; rw [hT]; rfl
include s hf ho
omit hc
-- packaged
lemma crate (V:D→ Activities G n)(he:∀ d,(V d).forced=A.forced)(hF:∀ i,(V i).Valid p v w)(hx:Stalk (Concert.bell A.forced a ξ) T (fun i j U=> ((V i).K j U:ℂ)) w): ∃ G':D→ ℕ→ Config G n→ℂ, Stalk (nose (G:=G) (Local.patch A) d a ξ) T G' (q X*c*(Real.exp ((X.card:ℝ)*w)-1)) ∧∀ i, Local.ForceFormat p (V i) 0 (G' i) ∧∀ U:Config G n,HasSum (fun j=>Local.gasMark p (V i) U j (G' i)) (F U*((V i).gas p U:ℂ)):=by
   obtain ⟨f,hg,H⟩:= cackle T p d X A s F V he hv hx; refine ⟨f,hg,fun i=>?_⟩; rw [H]; exact season p X A s (V i) (he i) (hF i) F hf ho
end YM.UVExtension.Pier
