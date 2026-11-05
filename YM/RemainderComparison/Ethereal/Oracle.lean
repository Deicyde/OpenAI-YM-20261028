import YM.RemainderComparison.Ethereal.Window
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Ethereal
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{p : BudgetPoint}
-- Scalar costs before changing.Some analytic model.E extra packets also inhabit these, with Hessian null.Normed.
open Lacuna Vowel PhysicalNext.Repeat
variable {I κ:Type} (V : Vowel G n I)(X : Vowel G n ℕ)(p:BudgetPoint)
variable {b u σ:ℝ}

section encoding
variable [Countable I]

def rekey (V:Vowel G n I)(f:ℕ≃I) : Vowel G n ℕ:= ⟨V.sign∘f,V.stanza∘f⟩
variable (f:ℕ≃ I)
local notation "Sʼ"=> rekey V f
omit [Countable I] in
lemma sprouts (hp:V.Pricings p σ b): Vowel.Pricings Sʼ p σ b:=by
   obtain ⟨u,h,hv⟩:= hp.marks
   exact ⟨⟨u ∘ f,fun i=> (h (f i)).2.1⟩, ⟨u∘ f,fun i=>h _,fun i=> Cost.equiv f (hv i)⟩⟩
omit [Countable I] in
lemma realizing (hp:V.Moves): Vowel.Moves Sʼ :=by
   constructor; intro s b; obtain ⟨g,hg⟩:=hp.continual s b
   let e:= (f.trans g).trans f.symm; refine ⟨e, fun i=> ?_⟩
   have he i : f (e i)=g (f i):= f.apply_symm_apply _
   exact ⟨(congr_arg V.sign (he i)).trans (hg (f i)).1, (congr_arg V.stanza (he i)).trans (hg (f i)).2⟩
omit [Countable I] in
lemma locking (hx:Normal V p) : Normal (rekey V f) p:= ⟨fun _=> hx.airy _,fun _=> hx.at_zero _,fun _=> hx.hc _,realizing V f hx.moves⟩
omit [Countable I] in
lemma lively (U: Config G n) : (Sʼ).overlay p U=V.overlay p U:=f.tsum_eq (fun i=> V.ray p i U)

-- pad E projections when optional atoms too sparse.Pointwise equality.Bridge facets

def spare (G:Gauge)(c:Side) : Vowel G c (Seat c × ℕ):=⟨Song.revolve (fun (_:ℕ)=> ⟨(0:Site c),{0},Finset.mem_singleton_self _⟩),0⟩
def bump : Vowel G n ℕ := rekey (Ethereal.ethic V (spare G n)) (numbering _)
local notation "Sˮ" => Ethereal.spare G n
local notation "Vʼ"=> Ethereal.bump V
lemma shadow (hx:V.Moves) (hp:V.Pricings p σ b): Vowel.Moves Vʼ∧ Vowel.Pricings (bump V) p σ b:=by
   have hl: Vowel.Moves (spare G n):=by
      constructor; intro s b; refine ⟨Song.whirl s b,fun i=>?_⟩
      have he:= Song.spirit (fun (_:ℕ)=>(⟨(0:Site n),{0},Finset.mem_singleton_self _⟩:RegularAddress n)) (fun (_:ℕ) (_:Config G n)=>0) s b i
      exact ⟨(Ethereal.lineTest he.1 he.2.1).symm,rfl⟩
   have ht : Vowel.Pricings Sˮ p σ 0 := ⟨⟨0,fun _=>le_rfl⟩,⟨fun _=>0,fun i=> ?_,fun i=> budget_of_sum (fun i=> by split<;>simp) (fun s=>by simp)⟩⟩
   · refine ⟨Ethereal.realizing _ _ (Ethereal.tilted V _ hx hl),?_⟩
     rw [← add_zero b]; exact Ethereal.sprouts _ p _ (Ethereal.stair V p _ hp ht)
   exact ⟨CouplingShape.reg_const _,Progress.DirectedRecipe.no_cost ..⟩
lemma pollen (h:V.Pricings p σ b)(he:0 ≤ σ) (U:Config G n): (Vʼ).overlay p U= V.overlay p U:=by
    rw [Ethereal.bump, lively]
    let f i:=(ethic V Sˮ).ray p i U; have hp: Summable (fun i=> f (.inl i)):= (accounted V p h he U).2.1.of_norm
    have hx (i): f (.inr i)=0:=by
       change masked p.threshold ((Sˮ).sign i).support _ U= _; by_cases hi: Healthy p.threshold ((Sˮ).sign i).support U; · rw [masked_eq _ _ _ _ hi]; rfl
       exact masked_ne _ _ _ _ hi
    have hv :=Summable.tsum_sum (f:=f) hp (show Summable (fun i=> f (.inr i)) from summable_zero.congr (fun i=> (hx i).symm)); change (∑' i,f i)= _; rw [hv]; simp_rw [hx,tsum_zero,add_zero]; rfl
end encoding
end YM.RemainderComparison.Ethereal
