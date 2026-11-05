import YM.ProjectorNext.PROJECTOR_CALIBRATION.Filters
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Shrink
import YM.Work.B14

/-! # Choose filter panels stage-by-stage -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Labels Maxwell Work Function Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {d : ℕ}

namespace Split
variable (S : Split G d)

def N (k : Level d) := LinearMap.id (R:=ℝ) (M:=Taylor G k.val) - S.Q k

def U : Module.End ℝ (Snap G d) := LinearMap.pi fun k => (S.Q k).comp (LinearMap.proj k)

lemma comm (A : Snap G d) (u : G.El) : S.U (Cast u A) = Cast u (S.U A) := funext fun _ => S.natural ..

lemma N_comm (k : Level d) (u : G.El) (A : Taylor G k.val) : S.N k (Taylor.paint u A) = Taylor.paint u (S.N k A) := by
  simp [N,S.natural]

/-- Q yields genuine shell arguments degree-by-degree. Used even on
inhomogeneous equation labels, reading at arbitrary scaled data. -/
lemma constrained (A : Snap G d) :
    ∃ X : TaylorTower G, expand d (S.U A) = fun i => gaugeJet (X i) := by
  let X (i : ℕ) (hi : i<d-1) : Shell G i :=
    ⟨takeCurl (S.Q ⟨i,hi⟩ (A ⟨i,hi⟩)), (shell_iff _).1 (S.hits ..)⟩
  refine ⟨fun i => if h : i<d-1 then X i h else 0,?_⟩
  funext i; unfold expand
  split
  · rename_i h; dsimp only; rw [dif_pos h]
    apply Maxwell.potential.injective
    apply Subtype.ext
    exact (match_leg (X i h)).symm
  · rename_i h; dsimp only; rw [dif_neg h, map_zero]
end Split

def cutSpace (G : Gauge) (k : Level d) : Submodule ℝ (Snap G d) where
  carrier := {x | ∀ i, k < i → x i = 0}
  zero_mem' i _ := rfl
  add_mem' := by rintro a b ha hb i hi; change a i+b i = 0; rw [ha i hi,hb i hi,add_zero]
  smul_mem' := by rintro t a ha i hi; change t • a i=0; rw [ha i hi, smul_zero]

def cutTurn (k : Level d) (u : G.El) : Module.End ℝ (cutSpace G k) :=
    ((castAction u).comp (cutSpace G k).subtype).codRestrict _ (by
      intro A l hl; change Taylor.paint u (A.val l) = 0; rw [A.property l hl, map_zero])

/- Existence of a finite panel suffices to recover a specific linear
readout. Include proof for partial observations; G03 handled total. -/
private lemma finite_panel {I X V Z : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup Z] [Module ℝ Z]
    (T : I → X →ₗ[ℝ] V) (N : X →ₗ[ℝ] Z) (h : ∀ x : X, (∀ i, T i x=0) → N x=0) :
    ∃ J : Finset I, LinearMap.ker (LinearMap.pi fun i : J => T i.val) ≤ LinearMap.ker N := by
  classical
  let K (J : Finset I) : Submodule ℝ X := ⨅ i : J, LinearMap.ker (T i.val)
  let R (J : Finset I) := Module.finrank ℝ (K J)
  obtain ⟨n,⟨J,rfl⟩,hmin⟩ := wellFounded_lt.has_min (Set.range R) (Set.range_nonempty R)
  refine ⟨J,fun x hx => h x fun i => ?_⟩
  have hJ : x ∈ K J := (Submodule.mem_iInf _).mpr fun j => congr_fun (show (fun i : J => T i.val x) = 0 from hx) j
  have he : K (insert i J) ≤ K J := fun y hy => (Submodule.mem_iInf _).mpr fun j => ((Submodule.mem_iInf _).mp hy) ⟨j.val,Finset.mem_insert_of_mem j.property⟩
  have hh : K J = K (insert i J) := Eq.symm (he.eq_of_not_lt fun hv => hmin _ ⟨insert i J,rfl⟩ (Submodule.finrank_lt_finrank_of_lt hv))
  exact ((Submodule.mem_iInf _).mp (hh ▸ hJ : x∈K (insert i J))) ⟨i,Finset.mem_insert_self ..⟩

variable (H : Hol G) (V : Split G d)

structure Slice (k : Level d) where
  addresses : Finset Position
  Z : (↥addresses → G.Color) →ₗ[ℝ] Taylor G k.val
  lower (A : Snap G d) : A∈cutSpace G k → Z (fun i => linearSample H d i.val A)=V.N k (A k)
  color (u : G.El) (a : ↥addresses → G.Color) : Z (colorAction u a)=Taylor.paint u (Z a)

/-- Endomorphism convention so the finite choice can be made in the already-defined Snap. -/
def through (k : Level d) : Module.End ℝ (Snap G d) := LinearMap.pi fun i => if i≤k then LinearMap.proj i else 0

lemma through_hit (k : Level d) (A : Snap G d) : through k A∈cutSpace G k := by
  intro i hi; simp only [through,LinearMap.pi_apply,if_neg (not_le.mpr hi),LinearMap.zero_apply]

lemma through_fix (k : Level d) (A : Snap G d) (ha : A∈cutSpace G k) : through k A=A := by
  funext i; unfold through; rw [LinearMap.pi_apply]; split
  · rfl
  rename_i hv
  have he := (show ∀ i : Level d, k < i → A i=0 from ha) i (lt_of_not_ge hv); exact he.symm

lemma through_natural (k : Level d) (u : G.El) (A : Snap G d) : through k (Cast u A)=Cast u (through k A) := by
  funext i; unfold through Cast
  rw [LinearMap.pi_apply,LinearMap.pi_apply]; split
  · rfl
  rw [LinearMap.zero_apply,LinearMap.zero_apply,map_zero]

def off (k : Level d) := (V.N k).comp (LinearMap.proj (φ:=fun l : Level d => Taylor G l.val) k)

def used (k : Level d) (i : Position) : Snap G d →ₗ[ℝ] G.Color := (linearSample H d i).toLinearMap.comp (through k)

lemma off_comm (k : Level d) (u : G.El) (x : Snap G d) : off V k (Cast u x)=Taylor.paint u (off V k x) := V.N_comm ..

lemma through_eq (A : Snap G d) (k : Level d) : through k A k = A k := by simp [through]

lemma off_kernel (k : Level d) (A : Snap G d) (h : ∀ i, used H k i A=0) : off V k A=0 := by
  have ht : through k A∈cutSpace G k := through_hit k A
  have he := Div.detects H k ht h
  rw [through_eq] at he
  change A k - V.Q k (A k)=0; rw [V.fixes k _ he,sub_self]

set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 400000 in
lemma choose_panel (k : Level d) :
    ∃ J : Finset Position, LinearMap.ker (LinearMap.pi fun i : J => used H k i.val) ≤ LinearMap.ker (off V k) := by
  exact finite_panel (I:=Position) (X:=Snap G d) (V:=G.Color) (Z:=Taylor G k.val) (used H k) (off V k) (off_kernel H V k)

set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 400000 in
lemma choose_filter (k : Level d) {J : Finset Position} (hh : LinearMap.ker (LinearMap.pi fun i : J => used H k i.val) ≤ LinearMap.ker (off V k)) :
    ∃ C : (↥J → G.Color) →ₗ[ℝ] Taylor G k.val, (∀ x, C ((LinearMap.pi fun i : J => used H k i.val) x)=off V k x) ∧
      ∀ u x, C (colorAction u x)= Taylor.paint u (C x) := by
  have ha (u : G.El) (x : Snap G d) :
      (LinearMap.pi fun i : J => used H k i.val) (castAction u x) = colorAction u ((LinearMap.pi fun i : J => used H k i.val) x) := by
    funext i
    change linearSample H d i.val (through k (Cast u x)) = G.adjoint u (linearSample H d i.val (through k x))
    rw [through_natural,linearSample_natural]
  exact panelFilter (G:=G) (I:=J) (X:=Snap G d) (Y:=Taylor G k.val) _ _ hh (castAction (d:=d)) (Taylor.paint (j:=k.val)) ha (fun u x => off_comm V k u x)

def stage (k : Level d) : Slice H V k := by
  let E := choose_panel H V k
  let D := choose_filter H V k E.choose_spec
  refine ⟨E.choose,D.choose,fun A ha => ?_, D.choose_spec.2⟩
  have he := D.choose_spec.1 A
  change D.choose (fun i => linearSample H d i.val (through k A)) = _ at he
  rw [through_fix k A ha] at he; exact he

structure Machine (H : Hol G) (d : ℕ) extends Windows H d, Split G d where
  filters (k : Level d) : Slice H toSplit k

def machine (d : ℕ) : Machine H d := ⟨windows H d, splitOf (windows H d), stage H _⟩

namespace Machine
variable {H} (M : Machine H d)

def liftLeg (k : Level d) : Snap G d →ₗ[ℝ] Taylor G k.val :=
    (M.filters k).Z.comp (LinearMap.pi fun i => (linearSample H d i.val).toLinearMap)

def liftAll : Module.End ℝ (Snap G d) := LinearMap.pi M.liftLeg

lemma diagonal (k : Level d) (x : Snap G d) (hk : x∈cutSpace G k) :
    M.liftAll x k = M.N k (x k) := (M.filters k).lower x hk

lemma intertwines (u : G.El) (x : Snap G d) :
    M.liftAll (Cast u x) = Cast u (M.liftAll x) := by
  funext k
  change (M.filters k).Z (fun i => linearSample H d i.val (Cast u x)) = Taylor.paint u _
  simp_rw [linearSample_natural]
  exact (M.filters k).color u _

end Machine
end YM.ProjectorNext.Calibration
