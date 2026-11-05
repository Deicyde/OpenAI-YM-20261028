import YM.RG08.Line.Financing

/-!
# The flat Gaussian line as a priced analytic stencil in cell coordinates
-/
noncomputable section
namespace YM.RG08.Line
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk
open scoped Matrix BigOperators Topology Classical
set_option autoImplicit false
variable {G : Gauge} {c f : Side}

def cellLine (P : Patch)(K : KernelChoices)(G:Gauge) (b:Bed)(n:Side) : Matrix (Co n (Co P.L (Loc G 1))) (Co n (Co P.L (Loc G 1))) ℝ:=
 let S:=habitat P K n
 let y:= unitSplit G S 1
 let z:= clothe G S
 let Q:= repackM y z (project G S (green S))
 Q*(parcelLine G P K b).acts n* Matrix.transpose Q

def NativeLine (S:StepData c f)(G:Gauge)(b:Bed):= let Q:=project G S (green S); Q*meal G S b * Q.transpose

lemma native_paid (P:Patch)(K:KernelChoices)(G:Gauge)(b:Bed)(n:Side) : let S:=habitat P K n; let Y:=unitSplit G S 1; cellLine P K G b n = repackM Y Y (NativeLine S G b):= by
  intro S Y
  let Z:=clothe G S
  rw [NativeLine,repack_multiply Y Z Y, repack_multiply Y Z Z, repack_rotate]
  have hA (A: Funds (Co n (ParcelG G P.L))): repackM Z Z (repackM Z.symm Z.symm A)=A := by ext; simp [repackM]
  erw [hA]; rfl

lemma covariance_of_meal (P:Patch)(K:KernelChoices)(G:Gauge)(b:Bed)(n:Side){u : Clip}{η D:ℝ}(hs:Floor b u (n*P.L) η D)(h:P.Branches K G)
    (he : ∀ t, meal G (habitat P K n) b * knobs (habitat P K n) b G t=1) :
    let S:=habitat P K n
    let M:=NativeLine S G b
    (∀ x,onTree (green S) (M *ᵥ x)) ∧ (∀ x,onTree (green S) x → M*ᵥ (linePrecision G S b *ᵥ x)=x) ∧ M.transpose=M := by
  intro S M
  let t:S.Choices:= Classical.choice inferInstance
  let W:= postroom S t (inch S.patch.L) (G:=G)
  have hW : IsUnit (W*spreadM (G:=G) S).det:=
    Eq.symm (Stationary.fired S t (show S.patch.Branches S.kernel G from h)) ▸ fund_det (grenade_safe _ (inch_pos _))
  exact inverse_tree (green S) _ W (he t) hW hs

lemma covariance_of_general {P:Patch}{K:KernelChoices}(G:Gauge)(b:Bed)(n m:Side)(hc:m.val=n.val*P.L.val)
    {u ε D}(hs:Floor b u m ε D)(h:P.Branches K G)(he : ∀ t, meal G (StepData.mk P K hc) b * knobs (StepData.mk P K hc) b G t=1): let S:=StepData.mk P K hc
    let M:= NativeLine S G b
    (∀ x,onTree (green S) (M *ᵥ x)) ∧ (∀ x,onTree (green S) x → M*ᵥ (linePrecision G S b *ᵥ x)=x) ∧ M.transpose=M := by
  have hh : m=n*P.L:= Subtype.ext hc
  subst m
  exact covariance_of_meal P K _ _ _ hs h he

-- chosen at width 1 (so can feed any of these smaller widths)
def fare (P:Patch)(K:KernelChoices)(G:Gauge):ℝ:= Classical.choose (stencil_projection P K G 1 zero_le_one)
def sailsK (P:Patch)(K:KernelChoices)(G:Gauge) := Classical.choose (Classical.choose_spec (stencil_projection P K G 1 zero_le_one))
lemma sails_receipt (P:Patch)(K:KernelChoices)(G:Gauge) : Tagged 1 (fare P K G) (sailsK P K G) (fun n=> let S:= habitat P K n; repackM (unitSplit G S 1) (clothe G S) (project G S (green S))):= Classical.choose_spec (Classical.choose_spec (stencil_projection P K G 1 zero_le_one))

def warm (P:Patch)(K:KernelChoices)(G:Gauge)(b:Bed) := Pert.Bulk.bind (Pert.Bulk.bind (sailsK P K G) (plain (parcelLine G P K b))) (Function.swap (sailsK P K G))

/-- Pre-block strip, post-block cost, usable on the cell-side convention at every compatible side
including across varying *period* and *cutoff*. Integral Wick contractions read the whole inverse
from the tree slice (zero-padded on trunks); no averaging of trees or signed choices in this formal
rule. Not an estimate on tilted sectors. -/
theorem preheat (G:Gauge)(K:KernelChoices)(Q:MapPrices)(j:ℕ): ∃ η : ℝ,0<η ∧ η ≤ 1 ∧ ∃ post : Side→ℝ,(∀ i,0≤post i) ∧ ∀ P:Patch, P.Branches K G → P.J=j → ∀ b:Bed,b.metric.strip (Q.α j) (Q.Ω j) → ∀ u D,
    (∀ n,Floor b u n (Q.η j) D) →
    Tagged η (post P.L) (warm P K G b) (cellLine P K G b) ∧
    ∀ (n m : Side) (hc:m.val=n.val*P.L.val), let S:= (StepData.mk P K hc : StepData n m); let M:= NativeLine S G b;
     (∀ x,onTree (green S) (M *ᵥ x)) ∧ (∀ x,onTree (green S) x → M*ᵥ (linePrecision G S b *ᵥ x)=x) ∧ M.transpose=M := by
  let ω:=min 1 (Q.α j)
  let Ω:=max 0 (Q.Ω j)
  have hv : 0<ω := lt_min zero_lt_one (Q.alpha_pos j)
  have hs:ω≤1:=min_le_left ..
  obtain ⟨v,C,h,h₁,hC,H⟩:= meal_price G K j (Q.η j) Ω ω (Q.eta_pos j) hv hs (le_max_left ..)
  let q (P : Patch) := Fintype.card (ParcelG G P.L)*( (Fintype.card (ParcelG G P.L) :ℝ)*(fare P K G*(C*(P.L.val:ℝ)^2))*fare P K G )
  have hQ (P:Patch) : 0 ≤ q P:= by have ht := (sails_receipt P K G).pos; unfold q; positivity
  let post (L : Side):= if he: ∃ P:Patch,P.J=j ∧ P.L=L then q he.choose else 0
  refine ⟨v,h,h₁.trans hs,post,fun i=> by unfold post; split; exact hQ _; rfl,fun P hP hJ b hb u D hD=>?_⟩
  obtain ⟨a,A⟩:= H P hJ hP b (show b.metric.strip (inch P.L*ω) Ω from fun i k=> (hb i k).mono ((mul_le_of_le_one_left hv.le (inch_le _)).trans (min_le_right ..)) (le_max_right ..)) u D hD
  have he: ∃ T:Patch,T.J=j ∧ T.L=P.L := ⟨P,hJ,rfl⟩
  have hF: P=he.choose := by
    obtain ⟨e,f⟩:=Classical.choose_spec he
    -- use cases patches
    have ex (P Q : Patch)(he:P.J=Q.J)(hh:P.L=Q.L):P=Q:=by cases P; cases Q; simp_all
    exact ex _ _ (hJ.trans e.symm) f.symm
  rw [show post P.L=q he.choose from dif_pos he,← hF]
  have ht:= (sails_receipt P K G).mono (h₁.trans hs) le_rfl
  exact ⟨(ht.mul (Tagged.ticket _ a (by positivity)) h.le).mul (ht.rear h.le) h.le,fun n m hc=> covariance_of_general G b n m hc (hD m) hP (A n m hc)⟩
end YM.RG08.Line
