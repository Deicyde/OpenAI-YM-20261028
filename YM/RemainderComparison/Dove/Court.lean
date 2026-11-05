import YM.RemainderComparison.Dove.Pier
/-! # Add real tag bus. Doesn't require W increasing occupancy AFTER calendar; track exact retain/ac/
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Dove
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Geo Lacuna Ethereal Animals
open Extra.Iteration WilsonStartup PhysicalNext.Repeat Song Meadow
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{α:Type}{f:Side}
variable (R : Rep G f)(A:α→RegularAddress f)(g:ℕ≃ ℕ ⊕ α)

def junk (P : Activities G f) := Sum.elim P.reg A
def fair (P :Activities G f) : Activities G f:= { P with reg :=junk A P ∘ g,E:=Sum.elim P.E 0 ∘ g}
def arcadia := {R with activities := Dove.fair A g R.activities}
local notation "P"=> Dove.arcadia R A g
local notation "X"=> R.activities
set_option quotPrecheck false
local notation "Y" => (P).activities
local notation "τ"=> R.p
local notation "q"=> R.p.threshold
abbrev left (n:ℕ):=g.symm (Sum.inl n)
abbrev right (i:α):=g.symm (Sum.inr i)
lemma plots (i :α) : (Y).reg (Dove.right g i)=A i∧ (Y).E (Dove.right g i)=0 :=by
    unfold Dove.arcadia Dove.fair; simp [Function.comp_apply,right,junk]
lemma also (i:ℕ): (Y).reg (Dove.left g i)=(X).reg i∧ (Y).E (Dove.left g i)=(X).E i:=by unfold Dove.arcadia Dove.fair; simp [Function.comp_apply,Dove.left,junk]
variable {δ w σ C Λ:ℝ}

lemma earthed (h:R.Lawful σ C Λ δ w): Activities.RegularFamily (Y) (τ) ∧ (Y).EBound (τ) δ:=by
    obtain ⟨v,h_f,hV⟩:= h.labels.boundE; let l := Sum.elim v (fun (_:α)=> (0:ℝ)); let f:= l ∘ g

    have hv (i:ℕ) : let X':=(Y).reg i; let F:=(Y).E i
                     R.p.Regular X'.support F ∧ F 1=0 ∧ (Nonwrapping X'.support X'.site→∀ U V,IsAffineDirection X'.site U → IsAffineDirection X'.site V → logHessian F U V=0) ∧ R.p.supBounds X'.site X'.support F (f i):=by
        unfold arcadia fair junk; simp only [Function.comp_apply]; change _∧ _ ∧ _ ∧ R.p.supBounds _ _ _ (l (g i)) -- edit
        cases g i with
        | inl i=>exact ⟨h.labels.regular.smooth _,h.labels.regular.at_flat _,h.labels.regular.vanish _, h_f _⟩
        | inr i=> exact ⟨CouplingShape.reg_const _,rfl,fun _ a b _ _=>by
                      change logHessian (G:=G) (fun (_:Config G _)=>0) _ _ = _; unfold logHessian; rw [iteratedFDeriv_succ_const]; rfl ,Progress.DirectedRecipe.no_cost ..⟩ -- compile
    refine ⟨⟨fun _=>(hv _).1, fun _=>(hv _).2.1,fun i=>(hv _).2.2.1⟩,f,fun _=>(hv _).2.2.2, fun j=>?_⟩
    have ht:SumBudget (fun i:ℕ⊕α=> if (junk A (X) i).site=j then R.p.mass (junk A (X) i).support (l i) else 0) (δ+0) := Cost.sum (hV j) ?_
    · rw [add_zero] at ht; exact Cost.equiv g ht
    simpa only [junk,Sum.elim_inr, l, BudgetPoint.mass,mul_zero,ite_self] using! (show SumBudget (fun i:α=> (0:ℝ)) 0 from (by simp [SumBudget,summable_zero]))
variable (s:Signed)(b:Site f)(e:Equiv.Perm α)(π:R.activities.Moves s b)(h:∀ i,A (e i)=Song.line (A i) (s,b))
local notation "ψ" => (Equiv.sumCongr π.ep e)
local notation "θ" => ((g.trans ψ).trans g.symm)
include h
def portal : (Y).Moves s b:=by
    have hp (i:ℕ): (Y).reg (θ i) = Song.line ((Y).reg i) (s,b) ∧ ∀ V, (Y).E (θ i) V=(Y).E i (pull s b V):=by
       unfold arcadia fair; simp only [Function.comp_apply]; rw [show g (θ i)= ψ (g i) from g.apply_symm_apply _]; cases g i with
       | inl i=>exact ⟨(lineTest (π.reg_site i) (π.reg_support i)).symm, π.valuesE i⟩
       | inr i=>exact ⟨h i,fun _=>rfl⟩
    exact ⟨θ,π.kp,fun i=>congr_arg _ (hp i).1,fun i=>congr_arg _ (hp i).1,π.forced_support,π.forced_inventory,π.forced_tests,fun i=>(hp i).2,π.valuesK⟩
lemma epic (i:α): (portal R A g s b e π h).ep (right g i)=right g (e i):=by
   change θ (right g i)=_; unfold Dove.right; simp
omit h
variable (U:Config G f)
lemma binds (hz:R.Lawful σ C Λ δ w)(h:∀ s b,∃ e:Equiv.Perm α,∀ i,A (e i)=Song.line (A i) (s,b)): Rep.Lawful (P) σ C Λ δ w:= ⟨hz.paths,(earthed R A g hz).1, (by obtain ⟨a,b,c,d,e,z,f'⟩:= hz.labels.forced; exact ⟨a,b,c,d,e,z,f'⟩),(fun s b=>by obtain ⟨i,he⟩:=h s b; obtain ⟨π⟩:=hz.labels.moves s b; exact ⟨Dove.portal R A g s b i π he⟩),(earthed R A g hz).2,hz.labels.boundK⟩
lemma maths : (P).exponent U=R.exponent U∧ Rep.eval P= R.eval:=by
    have he (u:Config G f):(Y).additive R.p u=(X).additive R.p u:=by
       unfold Activities.additive
       let e':= Dove.left g
       let G i:= (Y).regularOccurrence R.p i u
       have he: Injective e' := g.symm.injective.comp Sum.inl_injective
       refine Progress.DirectedRecipe.transferred_sum (g:=fun i=> (X).regularOccurrence R.p i u) ⟨e',he⟩ ?_ ?_
       · intro i; change (Y).regularOccurrence R.p (left g i) u=_; unfold Activities.regularOccurrence; rw [show (Y).reg _ = (X).reg i from (also R A g i).1, show (Y).E _ = (X).E i from (also R A g i).2]
       intro i hi; cases he:g i with
       | inl i' => exact False.elim (hi ⟨i', (g.injective (by  rw [he]; exact g.apply_symm_apply _))⟩)
       | inr j=>
         rw [show i= Dove.right g j from (g.injective (he.trans (g.apply_symm_apply _).symm))]; unfold Activities.regularOccurrence; rw [(plots R A g j).2]; simp [masked]

    have ht(u:Config G f):(P).exponent u=R.exponent u:=by unfold Rep.exponent; rw [show (P).p=R.p from rfl,he]; rfl
    exact ⟨ht U, funext fun i=>congr_arg (·*_ ) (congr_arg Real.exp (ht i))⟩
end YM.RemainderComparison.Dove
