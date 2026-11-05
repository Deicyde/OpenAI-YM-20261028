import YM.PhysicalNext.ORDERED_AFFINE_2B.Frco
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymRows
import YM.Push.RELAY_MARK.Lim


/-!
# Full-window & propagation kernel rotation actually used in `Operates`

Includes the temporary identity completion to full Thing-key comparison
of the paired log and ratio letters. Not reselecting Q after permuting
orientation rows to construct a new C or mean. The structural formulas
hold for functions at any V (with branch/path as indicated), even the
fixed-sector extensions of the affine terms. For REAL differentiability
or for differentiating the *selected* sector use the Fees separately,
no claim of gyrating through thresholds. Avoid principal compression
where it's not the compared expression. Flat summands use a different
warp on links than actual ones (coarse gauge turned V vs identity flat
reference). Don't amalgamate before framing!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.SymWhole
open Function Filter Set Lattice RG Wilson Precision Tree Pressure Pressure.Tube Stores Exterior
open Next Next.SectorChange AnalyticBridge.GaussianFieldAlignment
open Push.SectorMeasure Oriented Orthogonal Tensor Whole Matrix Footprint.Padded
open Further Further.CurvedGaussianJets Tracks AnalyticBridge.Covariance Terrain
open Completion SymRows
open SectorTools.ActualScalar (noHole)
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "RTable" I => Gaussian.Table I
local notation "RPrice" => Next.SectorChange.Prices

section warp
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β)
  (O : ColorOrtho G α) (A B : RTable (β × G.ColorIndex))
omit [Fintype β] in
lemma weave_one : warp O e (1:RTable (β×G.ColorIndex)) = 1 := by
  unfold warp dressed; rw [show submatrix 1 (addr e G.ColorIndex) (addr e G.ColorIndex) = (1:RTable (α×G.ColorIndex)) by ext; simp [Matrix.one_apply]]
  rw [Matrix.mul_one]; exact priced_reverse O
omit [Fintype β] [DecidableEq β] in
lemma weave_add : warp O e (A+B) = warp O e A + warp O e B := by
  unfold warp dressed; rw [submatrix_add,Pi.add_apply,Pi.add_apply,Matrix.mul_add,Matrix.add_mul]
omit [Fintype β] [DecidableEq β] in
lemma weave_sub : warp O e (A-B) = warp O e A - warp O e B := by
  unfold warp dressed; rw [submatrix_sub,Pi.sub_apply,Pi.sub_apply,Matrix.mul_sub,Matrix.sub_mul]
omit [Fintype β] [DecidableEq β] in
lemma weave_scale (t : ℝ) : warp O e (t • A)= t • warp O e A := by unfold warp dressed; rw [submatrix_smul,Pi.smul_apply,Pi.smul_apply,Matrix.mul_smul,Matrix.smul_mul]
omit [DecidableEq β] in
lemma weave_times : warp O e (A*B)=warp O e A * warp O e B := by
  unfold warp dressed; let u := addr e G.ColorIndex; rw [← submatrix_mul_equiv A B u u u]
  let X := prices O; let C := A.submatrix u u; let D := B.submatrix u u
  change X*(C*D)*Xᵀ=X*C*Xᵀ*(X*D*Xᵀ)
  calc
    _ = X*C*((Xᵀ*X)*D)*Xᵀ := by rw [priced_orth,Matrix.one_mul,Matrix.mul_assoc X C D]
    _ = _ := by simp only [Matrix.mul_assoc]
omit [Fintype β] [DecidableEq β] in
lemma weave_trans : warp O e Aᵀ=(warp O e A)ᵀ := by unfold warp; rw [transpose_dressed, transpose_submatrix]
omit [Fintype β] in
lemma weave_shift (u : ℝ) : warp O e (CurvedGaussianJets.shifted A u) = CurvedGaussianJets.shifted (warp O e A) u := by unfold CurvedGaussianJets.shifted; rw [weave_add,weave_scale,weave_one]
end warp

variable {x : ℝ} {A A' : Stores S} {F F' : Forest S.ratio}
variable (L : Box x A A' F F') (O : ColorOrtho G (Bond f))

abbrev spin := warp O L.edges
abbrev heap := Orthogonal.move O L.edges

variable (T : Tube G S) (k k' : S.Choices) (V V' : Config G c)

lemma trawl_move (z : Thing G f → ℝ) : Frco.trawl (G:=G) x A' F' (heap L O z)=funds L O (Frco.trawl (G:=G) x A F z) := by
  apply tape.injective; funext i
  change tape (G:=G) (heap L O z) i.val.val = tape _ i; unfold heap funds; rw [move_tape,move_tape]
  change _=O i.val.val (tape (G:=G) z (L.onKey i).val.val); rw [L.atK]

lemma active_move (i : Bond f) : onStage A F x (L.edges i) ↔ onStage A' F' x i := by
  rw [acts_here,acts_here,← L.onKey.exists_congr_right]; simp_rw [L.atK,L.edges.injective.eq_iff]
lemma tape_on (z : RPrice G (Active A x F)) (i : Active A x F) : tape (G:=G) (widen x A F z) i.val.val=tape (G:=G) z i := by
  ext j; rw [tape_ap,tape_ap]; exact widen_at x A F z (.inl (i,j))
lemma tape_off (z : RPrice G (Active A x F)) (i : Bond f) (hi : ¬ onStage A F x i) : tape (G:=G) (widen x A F z) i=0 := by
  ext j; rw [tape_ap]; exact widen_cost x A F z (i,j) hi
lemma widen_move (z : RPrice G (Active A x F)) : widen x A' F' (funds L O z) = heap L O (widen x A F z) := by
  apply tape.injective; funext i; unfold heap; rw [move_tape]; by_cases he : onStage A' F' x i
  · obtain ⟨i,rfl⟩ := (acts_here A' F').mp he; rw [tape_on,← L.atK,tape_on]; exact move_tape ..
  rw [tape_off _ _ he, tape_off _ _ (fun h=> he ((active_move L i).mp h)),map_zero]

private lemma insert_gen {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (R : α ⊕ β ≃ γ) (z : γ → ℝ) (M : Gaussian.Table α) : let a:=z ∘ (⇑R) ∘ Sum.inl
    Joint.place R (Completion.wide M 1) *ᵥ z=z+(Sum.elim (M *ᵥ a-a) (fun _=>0)) ∘ ⇑R.symm := by
  intro a; let C:= Completion.wide M (1:Gaussian.Table β); unfold Joint.place
  rw [Matrix.submatrix_mulVec_equiv,wide_move,Matrix.one_mulVec]
  funext i; obtain ⟨(i|i),rfl⟩ := R.surjective i <;> simp only [Function.comp_apply,Equiv.symm_apply_apply,Pi.add_apply]
  · change (M *ᵥ a) i = a i + ((M *ᵥ a) i-a i); ring
  exact (add_zero _).symm

lemma put_acts (z : Thing G f → ℝ) (M : RTable (Active A x F × G.ColorIndex)) :
    identityPut x A F M *ᵥ z = z + widen x A F (M *ᵥ (Frco.trawl x A F z) - Frco.trawl x A F z) :=
  insert_gen (Completion.sorted A F) z M

lemma sub_funds (z y : RPrice G (Active A x F)) : funds L O z-funds L O y=funds L O (z-y) := by
  exact (Matrix.mulVec_sub (prices (onBond O)) (z ∘ addr L.onKey _) (y ∘ addr L.onKey _)).symm
lemma bills (M : RTable (Active A x F × G.ColorIndex)) (y : Thing G f→ℝ) :
    identityPut x A' F' (offer L O M) *ᵥ (heap L O y) = heap L O (identityPut x A F M *ᵥ y) := by
  have h1:=put_acts (A:=A') (F:=F') (x:=x) (heap L O y) (offer L O M)
  rw [h1,trawl_move L O]
  have he := warp_mv (onBond (x:=x) (F:=F') (A:=A') O) L.onKey M (Frco.trawl x A F y)
  change offer L O M *ᵥ (funds L O _) = funds L O _ at he
  rw [he,sub_funds,widen_move,put_acts (x:=x) (A:=A)]
  exact (Matrix.mulVec_add (prices O) (y ∘ addr L.edges _) ((widen x A F _ : Thing G f→ℝ) ∘ addr L.edges _)).symm

lemma put_moving (M : RTable (Active A x F × G.ColorIndex)) :
    identityPut x A' F' (offer L O M)=spin L O (identityPut x A F M) := by
  apply warp_of O L.edges
  intro z y
  have he := bills L O M y; change heap L O z ⬝ᵥ (identityPut x A' F' (offer L O M) *ᵥ heap L O y) = _; rw [he]; exact move_dot O L.edges z _

lemma charter_in (h : Equivalent (x:=x) T V V' k k' L.onKey (onBond O)) :
    charter T x A' F' k' V'=spin L O (charter T x A F k V) := by rw [plinth,plinth]; unfold Fixed.precision; rw [h.same]; exact put_moving ..

variable (hx : 120 ≤ radiusB x)

lemma probes_in (u : ℝ) (h : Equivalent (x:=x) T V V' k k' L.onKey (onBond O)) : let W:= windows S G x hx
    W.column (charter T x A' F' k' V') u = spin L O (W.column (charter T x A F k V) u) := by
  intro W; rw [column,column]; unfold lookPi
  let Z (i : Bond f) : Set (Bond f):={j | meeting S x i j}
  have he : unitWin S x (G:=G)=together G.ColorIndex Z := rfl
  rw [show scanA T A' F' k' x V'=spin L O (charter T x A F k V) from charter_in L O T k k' V V' h]
    -- do not rewrite inner 1
  let P:= charter T x A F k V
  have hg : spin L O P + u • (1:RTable (Thing G f)) = spin L O (P + u • 1) :=
    (weave_shift _ O P u).symm
  rw [hg]
  rw [he]; apply warp_per; intro i; ext j; exact L.pane i.1 j.1

structure Route (M M' : RTable (Thing G f)) : Prop where
  wall : M'=spin L O M
  probed (u : ℝ) : (windows S G x hx).column M' u=spin L O ((windows S G x hx).column M u)
lemma routes (h : Equivalent (x:=x) T V V' k k' L.onKey (onBond O)) :
    Route L O hx (charter T x A F k V) (charter T x A' F' k' V') :=
  ⟨charter_in L O T k k' V V' h,fun u=> probes_in L O T k k' V V' hx u h⟩

namespace Route
variable {M M' : RTable (Thing G f)} {L O hx} (h : Route L O hx M M')
include h



end Route

section transform
open Channels Locations Gauges

/-- even the ghost rows of the flat ledger transform, BUT with a separate kernel action. -/
def each (s : Signed) (b : Site c) (V : Config G c) (S : StepData c f) : Bool → ColorOrtho G (Bond f) := fun j=> if j then fiber s b V S else fiber s b (1:Config G c) S

lemma turn_stack (s : Signed) (b : Site c) {v E Q : ℝ} (hT : T.up.Bounds T.high v E Q) (h : S.patch.Branches S.kernel G) (j : Bool) :
    Route (calendar x A F s b) (each s b V S j) hx (Whole.stack T x A F k j V) (Whole.stack T x (Locations.book s b A) (Locations.forest s b F) (Channels.ticket s b k) j (pull s b V)) := by
  rcases j with j|j
  · have hz := turned_cov s b (1:Config G c) k T x h noHole F hT
    let P := calendar x (noHole (S:=S)) F s b
    let O := fiber s b (1:Config G c) S
    have hu := routes P O T k (Channels.ticket s b k) 1 _ hx hz
    have hw : Locations.book s b (noHole (S:=S))=noHole := by unfold Locations.book; simp [noHole]
    have hy : pull s b (1:Config G c) = 1 := by funext i; rw [read_back]; split <;> simp
    refine ⟨?_,?_⟩
    · have hp := hu.wall; simp only [hw,hy] at hp; exact hp
    intro u; have hp := hu.probed u; simp only [hw,hy] at hp; exact hp
  exact routes (calendar x A F s b) _ T k _ V _ hx (turned_cov s b V k T x h A F hT)

def steady (G : Gauge) (f : Side) : ColorOrtho G (Bond f) := fun _=> LinearIsometry.id
def crest (S : StepData c f) (p : Site c → G.El) : Bool → ColorOrtho G (Bond f) := fun j=> if j then rotating (constantGauge p S.ratio) else steady G f
lemma moves_still (A : RTable (Thing G f)) : A=warp (steady G f) (Equiv.refl _) A := by
  apply warp_of; intro a b
  have he (a : RPrice G (Bond f)) : Orthogonal.move (steady G f) (Equiv.refl _) a=a := tape.injective (funext fun i => move_tape ..)
  rw [he,he]
lemma gauge_stack (p : Site c → G.El) {v E Q : ℝ} (hT : T.up.Bounds T.high v E Q) (h : S.patch.Branches S.kernel G) (j : Bool) :
    Route (room x A F) (crest S p j) hx (Whole.stack T x A F k j V) (Whole.stack T x A F k j (Lattice.gauge p V)) := by
  rcases j with j|j
  · exact ⟨moves_still _,fun u=> moves_still _⟩
  exact routes (room x A F) _ T k k V (Lattice.gauge p V) hx (gauge_cov T p V k x A F h hT)
end transform
end YM.PhysicalNext.OrderedAffine2B.SymWhole
