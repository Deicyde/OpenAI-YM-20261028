import YM.RG08.Tack.Plain
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Articles
import YM.RG08.Cell.Basis

/-!
# Actual branch local atoms, packing fine slots into coarse-aperture cells
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Tack
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid
open AnalyticNext.QuarticMatch.Radius
open Articles Model
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius NNReal

variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}

abbrev Head (P:Patch)(G:Gauge) := (Co P.L (Loc G 1)) ⊕ (Loc G 1)
abbrev Epic (P:Patch)(G:Gauge)(c:Side) := Cove c (Head P G)

def lowSlot (S:StepData c f)(x:Lines G f 1) :Epic S.patch G c:=
 let v:=splitCo S.ratio _ x; (v.1,Sum.inl v.2)
def highSlot (S:StepData c f)(x:Lines G c 1):Epic S.patch G c:=(x.1, Sum.inr x.2)

def low (S:StepData c f):Cellar (Epic S.patch G c)→L[ℝ] Dir G f:= (arm G f 1).toContinuousLinearMap ∘L (ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (lowSlot S i)))
def high (S:StepData c f):Cellar (Epic S.patch G c)→L[ℝ] Dir G c:= (arm G c 1).toContinuousLinearMap ∘L (ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj (highSlot S i)))
lemma low_book (w:Cellar (Epic S.patch G c))(x:Lines G f 1):low S w (x.1,x.2.1) x.2.2=w (lowSlot S x):=rfl
lemma high_book(w:Cellar (Epic S.patch G c))(x:Lines G c 1):high S w (x.1,x.2.1) x.2.2=w (highSlot S x):=rfl

abbrev AnyHead (P:Patch)(G:Gauge) := Lines G (Model.native P) 1 ⊕ G.ColorIndex

def fetch0 (P:Patch):Cellar (AnyHead P G)→L[ℝ]Dir G (Model.native P):=
 (arm G _ 1).toContinuousLinearMap ∘L ContinuousLinearMap.pi (fun i:Lines G (Model.native P) 1=> if (lift i.1)∈Model.atEase P then ContinuousLinearMap.proj (Sum.inl i) else 0)

def vase (G:Gauge):(G.ColorIndex→ℝ) ≃L[ℝ] G.Color:=
 LinearEquiv.toContinuousLinearEquiv { toFun:=WithLp.toLp 2, invFun:=WithLp.ofLp,left_inv _:=rfl,right_inv _:=rfl,map_add' _ _:=rfl,map_smul' _ _:=rfl }

def fetch1 (P:Patch) :Cellar (AnyHead P G)→L[ℝ] G.Color:= (vase G).toContinuousLinearMap ∘L ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (Sum.inr i))

-- Patch tags of dummy evaluation used only here, fixed even across smaller periods

def mold (P:Patch)(K:KernelChoices)(G:Gauge)(k:(habitat P K (marker P)).Choices)(i:Axis): Still (AnyHead P G):=fun y=>Articles.noise (habitat P K (marker P)) k (0,i) (fetch1 P y, fetch0 P y)
lemma mold_pace (h:P.Branches K G)(k:(habitat P K (marker P)).Choices)(i:Axis):
    Pace (mold P K G k i) := by
 let A := (fetch1 P (G := G)).prod (fetch0 P (G := G))
 have hn : ContDiffAt ℝ ω (Articles.noise (habitat P K (marker P)) k (0,i) (G := G)) (A 0) := by
   rw [map_zero]
   exact Articles.noise_smooth (habitat P K (marker P)) k (0,i) h
 exact hn.comp 0 A.contDiff.contDiffAt

-- the indices outside the atlas can wrap any way: `noiseAt` ignores them from inception.

def slink (P:Patch)(i:Axis): AnyHead P G→Market (Head P G) := Sum.elim
 (fun j=> let x:=lift j.1;(rent P.L x, Sum.inl (wrap P.L x,j.2)))
 (fun j=>(0,Sum.inr (coord i,j)))
private lemma fetch0_book (P : Patch) (w : Cellar (AnyHead P G))
    (v : Site (Model.native P)) (j : TypeFace 1) (l : G.ColorIndex) :
    fetch0 P w (v,j) l = if lift v ∈ Model.atEase P then w (Sum.inl (v,j,l)) else 0 := by
 change (if lift v ∈ Model.atEase P then ContinuousLinearMap.proj (Sum.inl (v,j,l))
   else (0 : Cellar (AnyHead P G) →L[ℝ] ℝ)) w = _
 split_ifs <;> rfl

private lemma pick_book (q : Site c) (w : Dir G f)
    (v : Site (Model.native S.patch)) (j : TypeFace 1) (l : G.ColorIndex) :
    Model.pick S q w (v,j) l =
      if lift v ∈ Model.atEase S.patch then w (wrap f (lift v) + S.ratio.embed q, j) l else 0 := by
 rw [Model.pick, ContinuousLinearMap.pi_apply]
 by_cases he : lift v ∈ Model.atEase S.patch
 · rw [if_pos he, if_pos he]
   rfl
 · rw [if_neg he, if_neg he]
   rfl

lemma imitation (i:Axis)(w:Cellar (Epic S.patch G c))(q:Site c):
    (fetch1 S.patch (roll (glance q (slink S.patch i)) w): G.Color) = high S w (q,coord i) ∧
    fetch0 S.patch (roll (glance q (slink S.patch i)) w)=Model.pick S q (low S w) :=by
 constructor
 · ext l
   change w _ = _
   simp only [slink, Sum.elim_inr, map_zero, zero_add]
   rfl
 ext ⟨v,j⟩ l
 rw [fetch0_book, pick_book]
 by_cases he : lift v ∈ Model.atEase S.patch
 · rw [if_pos he, if_pos he, low_book (S := S) w (wrap f (lift v) + S.ratio.embed q, j, l)]
   change w (wrap c (rent S.patch.L (lift v)) + q, Sum.inl (wrap S.patch.L (lift v),j,l)) =
     w (lowSlot S (wrap f (lift v) + S.ratio.embed q, j, l))
   simp only [lowSlot, pack_street, add_comm q]
 · rw [if_neg he, if_neg he]

def steward (P:Patch)(K:KernelChoices) (_G:Gauge):(habitat P K (marker P)).Choices:=(fun _=> (P.center,1),fun _=>P.center)

def guard (h:P.Branches K G):Articles.Sheds G P K:=Articles.sets (habitat P K (marker P)) (steward P K G) h

lemma when (h:S.patch.Branches S.kernel G)(t:S.Choices)(i:Axis)(q:Site c):
 (fun w:Cellar (Epic S.patch G c)=> S.kernel.penalty * G.price (G.lieExp (high S w (q,coord i)) * (S.prediction (represent (low S w)) t (q,i))⁻¹))=ᶠ[𝓝 0]
 (mold S.patch S.kernel G (guard h).tag i ∘ roll (glance q (slink S.patch i))):=by
 let P:=guard h
 have he : ∀ᶠ w:Cellar (Epic S.patch G c) in 𝓝 0,‖low S w‖≤P.b:= ((low S (G:=G)).continuous.norm.continuousAt.eventually (p:=fun v=> v<P.b) (gt_mem_nhds (by simp only [map_zero,norm_zero]; exact P.pos))).mono fun _ hv=>le_of_lt hv
 filter_upwards [he] with x hx
 rw [comp_apply, mold, (imitation (S:=S) i x q).2,(imitation (S:=S) i x q).1]
 exact (Articles.issued S h t P (q,i) (high S x (q,coord i),low S x) hx).2.2
 end YM.RG08.Tack
