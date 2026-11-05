import YM.RemainderComparison.Breeze.Sonar

/-! # Combine unnormalised analytic input answer into same density's
 registered residual. This is realignment, not cancellation of labels.
 Before extracting the new affine kinetic response & scalar. Keep explicit
 ordered slots.E Stamp & all anchors. Permit consumers to use original leg
 in subtraction/identification instead of fragile arithmetic identities.
 Append after oath.
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
variable {G:Gauge} {ι β I J:Type} {α:Type*} {c f:Side} [DecidableEq β] {Jm:Marker.Census β}
variable (O:Manor G c ι α I) (T:Manor G c ι α J) (P:BudgetPoint)
variable (s:Set I)(U:Set J)
variable (a:α)(Z:Set ι)(z:ι→Marker.Poly Jm)
open Mosaic Serif Manor

def signed : Manor G c ι α J:= {T with solvent:=fun u i=> - T.solvent u i}
local notation "Sʼ"=> signed T
lemma deuce (V:Config G c)(i:J) : Manor.wet Sʼ P a i V= - T.wet P a i V:=by
   unfold signed wet; dsimp only; split; rfl
   next=>
    change masked P.threshold (T.halls i) _ V = _
    by_cases hp: Healthy P.threshold (T.halls i) V
    · rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp]; rfl
    rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,neg_zero]

variable {u v σ:ℝ} {root:ι→Support c}
lemma tagTeam {i:J} (h:T.Sees P root i) : Manor.Sees Sʼ P root i:=by
   refine ⟨fun a=>?_,fun a j hj V hv=>?_ ,fun a hp V=> congr_arg (-·) (h.stall a hp V)⟩
   · have hp:= CouplingShape.reg_scale (-1) (h.angle a); rw [neg_one_smul] at hp; exact hp
   apply h.travels a j hj V; intro ht; apply hv; rw [deuce,ht,neg_zero]
lemma sealSign {i:J}{y:Site c} (hp:P.supBounds y (T.halls i) (T.solvent a i) u): P.supBounds y (Sʼ|>.halls i) ((signed T).solvent a i) u:=by
    have hv:= CouplingShape.sup_scale (-1) hp; simp only [abs_neg,abs_one,one_mul, neg_one_smul] at hv; exact hv
lemma spinalize (hv:T.Spinal U root P σ v): Manor.Spinal Sʼ U root P σ v:=by
   obtain ⟨f,h,hF,hV⟩:=hv.grants; exact ⟨f,h,fun i hi=> ⟨tagTeam T P (hF i hi|>.1),fun a x hx=> sealSign T P a ((hF i hi).2 a x hx)⟩,hV⟩
lemma templarySign (hv:T.Templary U root P σ v): Manor.Templary Sʼ U root P σ v:=by
   obtain ⟨f,h,hF,hV⟩:=hv.grants; exact ⟨f,h,fun i hi=> ⟨tagTeam T P (hF i hi|>.1),fun a=> sealSign T P a ((hF i hi).2 a)⟩,hV⟩

def unison : Manor G c ι α (I⊕J):=
    ⟨Sum.elim O.rooms T.rooms,fun a=>Sum.elim (O.solvent a) (T.solvent a),Sum.elim O.marks T.marks,Sum.elim O.total T.total⟩
local notation "Σʼ" => unison O T

def switch (s:Set I)(t:Set J): Set (I⊕J):={i| i.elim (fun i=>i∈s) (fun i=>i∈t)}
lemma sumPays (hp: T.Spinal U root P σ v) (hf:O.Spinal s root P σ u): Manor.Spinal Σʼ (switch s U) root P σ (u+v):=by
   obtain ⟨f,hf,hH,hV⟩:=hp.grants; -- reorder
   rename_i he -- edit
   obtain ⟨g,hg,hG,hS⟩:=he.grants
   refine ⟨Sum.elim g f,fun i=>?_ ,fun i hi=>?_,?_⟩
   · rcases i with i|i; exact hg i; exact hf i
   · rcases i with i|i
     · obtain ⟨hu,hh⟩:=hG i hi; exact ⟨⟨hu.angle,hu.travels,hu.stall⟩,hh⟩
     obtain ⟨hu,hh⟩:=hH i hi; exact ⟨⟨hu.angle,hu.travels,hu.stall⟩,hh⟩
   have hz:(Σʼ).halls= Sum.elim O.halls T.halls :=funext fun i=>by cases i<;> rfl
   rw [hz]; exact Labels.together O.halls T.halls P.B hS hV
lemma sumAnch (hp: T.Templary U root P σ v) (hf:O.Templary s root P σ u): Manor.Templary Σʼ (switch s U) root P σ (u+v):=by
   obtain ⟨g,hg,hG,hS⟩:=hf.grants; obtain ⟨f,hf,hH,hV⟩:=hp.grants; refine ⟨Sum.elim g f,fun i=>?_ ,fun i hi=>?_,fun i=>budget_of_sum (fun j=>?_) (fun j=> ?_)⟩
   · rcases i with i|i; exact hg i; exact hf i
   · rcases i with i|i
     · obtain ⟨hu,hh⟩:=hG i hi; exact ⟨⟨hu.angle,hu.travels,hu.stall⟩,hh⟩
     obtain ⟨hu,hh⟩:=hH i hi; exact ⟨⟨hu.angle,hu.travels,hu.stall⟩,hh⟩
   · rcases j with j|j; exact (hS i).1 j; exact (hV i).1 j
   rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]; exact add_le_add (budget_sum (hS i) _) (budget_sum (hV i) _)

-- Subspace

def peel : Manor G c ι α s:= ⟨fun i=>O.rooms i.val,fun a i=> O.solvent a i.val,fun i=>O.marks i.val,fun i=>O.total i.val⟩
local notation "ν" => peel O s
lemma peeled {p:Set I}{K:Set s}(hf: O.Spinal p root P σ v)(h:∀ i∈K, i.val∈p) : Manor.Spinal ν K root P σ v:=by
   obtain ⟨g,hg,hG,hB⟩:=hf.grants; refine ⟨fun j=>g j.val,fun i=>hg _, fun i hi=>?_,fun i=> budget_pull (fun i:s=>i.val) Subtype.val_injective (hB i)⟩; obtain ⟨hu,hh⟩:=hG i.val (h i hi); exact ⟨⟨hu.angle,hu.travels,hu.stall⟩,hh⟩
lemma templaryPeel {p:Set I}{K:Set s}(hf: O.Templary p root P σ v)(h:∀ i∈K, i.val∈p) : Manor.Templary ν K root P σ v:=by
   obtain ⟨g,hg,hG,hB⟩:=hf.grants; refine ⟨fun j=>g j.val,fun i=>hg _, fun i hi=>?_,fun i=> budget_pull (fun i:s=>i.val) Subtype.val_injective (hB i)⟩; obtain ⟨hu,hh⟩:=hG i.val (h i hi); exact ⟨⟨hu.angle,hu.travels,hu.stall⟩,hh⟩

def mural : Manor G c ι α (s⊕J):= unison (peel O s) (signed T)
local notation "μ"=> mural O T s
lemma unionAt (V:Config G c) (hs:Summable (fun i:s=>O.paint P Z z a V i.val)) (he:Summable (T.paint P Z z a V)) : O.basin P s Z z a V=(∑' i,T.paint P Z z a V i)+(∑' i,(μ).paint P Z z a V i):=by
   let f:= (μ).paint P Z z a V
   have hp i: f (Sum.inr i)= - T.paint P Z z a V i:=by
      unfold f; change (Sʼ).paint P Z z a V i= _; unfold Manor.paint; rw [deuce,Complex.ofReal_neg, neg_smul]; rfl
   have hg: Summable (fun i=> f (Sum.inr i)):=by simp_rw [hp]; exact he.neg
   change _= _+ ∑' i,f i
   rw [Summable.tsum_sum (f:=f) hs hg]; simp_rw [hp]; rw [tsum_neg,add_left_comm,add_neg_cancel,add_zero]; rfl
-- switch preparers
lemma Univ (v:Manor G c ι α I) (V:Config G c) : Manor.basin v P Set.univ Z z a V= ∑' i,v.paint P Z z a V i:= (Equiv.Set.univ I).tsum_eq _
lemma standing' (v:Manor G c ι α I) (V:Config G c){k:ℕ}{uFIX:ℝ}{u:β→ℝ} (hp: v.Templary Set.univ root P σ uFIX)(hσ:0≤ σ)(hZ: Chorus Jm u Z z k) : Summable (v.paint P Z z a V):= ((Equiv.Set.univ I).summable_iff).mp (standing a V Z z hp hZ hσ)
end YM.RemainderComparison.Lobby
