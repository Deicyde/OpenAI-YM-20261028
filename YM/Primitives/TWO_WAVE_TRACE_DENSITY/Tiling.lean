import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Boards
import YM.Push.FREE_RESOLVENT.SharedCells
import YM.Push.STATIONARY_UNIFORM.Paths




/-!
# One admissible repeated forest on **all** qualifying periods

Use E thermal_match at this forest; as allowed by the stationary change-of-tree
and tag theorem, not imposing repetitions on actual samples. Includes every
active bond in the counting metric. No integrating over independent tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave.RealSlice
open Lattice RG Precision Tree Bid FreeResolvent FreeResolvent.Lifted
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Push.Uniform
open scoped BigOperators Topology Classical

variable {G : Gauge} (P : Patch) (K : KernelChoices) {n m : Side}

lemma enough (hx:Larger (G:=G) (dock P K n)) : 3≤n.val := by
  have he:=hx.2.1
  change 100*(P.radius+4*P.L.val) ≤ n.val * P.L.val at he
  have hh:=P.L.pos
  by_contra! ht; have := Nat.mul_le_mul_right P.L.val (Nat.le_of_lt ht); omega
lemma dock_larger (h : P.Branches K G) : ∃ d:ℕ,∀ c:Side,d≤c.val→ Larger (G:=G) (dock P K c) := by
  refine ⟨2+100*Pressure.macroR P,fun n he=>⟨h,?_,?_⟩⟩
  · change 100*Pressure.macroR P ≤ n.val*P.L.val
    exact (show 100*Pressure.macroR P ≤ n.val by omega).trans (Nat.le_mul_of_pos_right _ P.L.pos)
  omega

abbrev three:Side:=⟨3,by decide⟩
-- reuse the same choice from reference torus root 0 (reference itself
-- needn't be `Larger`, only 3 and odd patch side).
def model : Forest (dock P K three).ratio:=Classical.choice (select _ (show Odd P.L.val from P.odd_side))
def trees (n : Side): Forest (dock P K n).ratio:=
    rebuild (model P K) (fun _ => 0) (Nat.le_refl 3)

-- residue offset & true type
abbrev Idx (P : Patch):= Site P.L × Axis
def keep (i : Idx P) : Prop:= ((shores P three).assemble (0,i.1),i.2) ∉ (model P K).trunks

def Resident := {i:Idx P// keep P K i}
instance instFintypeResident : Fintype (Resident P K) := inferInstanceAs (Fintype (Subtype _))
-- need Fintype public, noncomputable instance on NEW type (def not abbrev)

abbrev Coarse (G:Gauge):= Exterior.TypeFace 1 × G.ColorIndex
abbrev Vertical (G:Gauge)(P:Patch)(K:KernelChoices):= Resident P K × G.ColorIndex

lemma reserve (hn:3≤n.val) (x:Site n) (i:Idx P):
    ((shores P n).assemble (x,i.1),i.2) ∉ (trees P K n).trunks ↔ keep P K i:=
    (rebuild_at (model P K) (t:=fun _=> (0:Site three)) (h':=(rfl: (below P n).val=n.val*P.L.val)) x (Nat.le_refl 3) hn i.1 i.2).not.symm

lemma at_here (hn:3≤n.val)(x : Edge (Site (below P n))):
    x∉(trees P K n).trunks↔ keep P K ((shores P n).residue x.1,x.2):=by
  rcases x with ⟨x,i⟩; obtain ⟨⟨x,r⟩,rfl⟩:=(shores P n).assemble_bijective.2 x; dsimp only; rw [Ratio.assemble_res]; exact reserve P K hn x (r,i)

/-- resident is occupied even if its entry vanishes for particular W. -/
def freeBond {n:Side}(hn:3≤n.val) : Leaf n (Resident P K)≃(trees P K n).Free where
  toFun i:= ⟨((shores P n).assemble (i.1,i.2.val.1),i.2.val.2),(reserve P K hn i.1 i.2.val).2 i.2.property⟩
  invFun i:= ((shores P n).parent i.val.1,⟨((shores P n).residue i.val.1,i.val.2),(at_here P K hn i.val).1 i.property⟩)
  left_inv x:=by apply Prod.ext; exact (Ratio.assemble_parent ..); exact Subtype.ext (Prod.ext (Ratio.assemble_res ..) rfl)
  right_inv x:=Subtype.ext (Prod.ext ((shores P n).unpack_at _) rfl)


def outsider (G:Gauge)(n:Side): Leaf n (Coarse G)≃Primary n G:=(Equiv.prodAssoc _ _ _).symm

def insider (G:Gauge)(hn:3≤n.val):Leaf n (Vertical G P K)≃Key (trees P K n) G:= ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr (freeBond P K hn) (Equiv.refl _)))

-- all joint uniform estimate entries

def mapper (G:Gauge)(hn:3≤n.val):Leaf n ((Coarse G)⊕(Vertical G P K))≃Joint (trees P K n) G where
  toFun i:= Sum.elim (fun a=> .inl (outsider G n (i.1,a))) (fun b=> .inr (insider P K G hn (i.1,b))) i.2
  invFun := Sum.elim (fun a=>lead _ ((outsider G n).symm a)) (fun b=> TwoWave.peg _ ((insider P K G hn).symm b))
  left_inv v:=by rcases v with ⟨x,a|b⟩ <;> simp [lead,TwoWave.peg,TwoWave.up]
  right_inv v:=by rcases v with (a|b) <;> simp [lead,TwoWave.peg,TwoWave.up]


def redesk {α β:Type} [Fintype α][Fintype β](e:α≃β) : (α→ℝ)≃L[ℝ]β→ℝ := LinearEquiv.toContinuousLinearEquiv {
    toFun v:=v ∘ e.symm
    invFun v:=v ∘ e
    left_inv v:=funext fun i=>by simp only [comp_apply,e.symm_apply_apply]
    right_inv v:=funext fun i=>by simp only [comp_apply,e.apply_symm_apply]
    map_add' _ _:=rfl
    map_smul' _ _:=rfl }
lemma desk_spot {α β:Type}[Fintype α][Fintype β](e:α≃β)(i:α): redesk e (spot i)=bolt (e i):=by
  ext1 v; change spot i (e.symm v)=bolt (e i) v
  simp [spot,bolt,Pi.single_apply,Equiv.symm_apply_eq]

-- physical maps

def surfaceIn (G:Gauge)(n:Side): Board (Coarse G) n ℝ ≃L[ℝ] Bid.Dir G n:=(redesk (outsider G n)).trans (tint G _)
def surfaceCell (G:Gauge)(hn:3≤n.val): Board (Vertical G P K) n ℝ ≃L[ℝ] AxisChart G (trees P K n):=(redesk (insider P K G hn)).trans (tint G _)



lemma surface_frame (G:Gauge)(hn:3≤n.val)(i:Leaf n (Vertical G P K)) :
    surfaceCell P K G hn (spot i)=Precision.frame (trees P K n) (insider P K G hn i):=by
  unfold surfaceCell; rw [ContinuousLinearEquiv.trans_apply,desk_spot,glyph]
end YM.Primitives.TwoWave.RealSlice
