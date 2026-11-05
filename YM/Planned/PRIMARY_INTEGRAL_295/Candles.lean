import YM.Planned.PRIMARY_INTEGRAL_295.Hives
import YM.Planned.PRIMARY_INTEGRAL_295.Sparks
/-!
# Compression intertwiners full affine

Doesn't derive H.μ_Q from law, but pays for moving-correlation law proof
exact (also retains tags). Works through singular noncall matrix.inv. Actual
required mast proofs before appointment. H allowed matrix-currency.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Candles
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source
open Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks  Hives
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}
variable {α β γ X W T V : Type*} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]

-- R laws. Curried around matrices exact both colors occurrences only.
def Crown (H:Hive G X α) (J:Hive G W β) (z : α→ G.El)(w : β→G.El)(A B: Matrix X W ℝ): Prop := H.paint z*A=B*J.paint w

namespace Crown
variable {H:Hive G X α} {J:Hive G W β} {z : α→ G.El} {w : β→G.El} {A B A' B' : Matrix X W ℝ} (h:Crown H J z w A B)
include h
lemma character : B= H.paint z*A*(J.paint w).transpose:=by
    rw [(show H.paint z*A=_ from h),Matrix.mul_assoc,J.reflection,J.cups,Matrix.mul_one]
lemma bounce : Crown H J z⁻¹ w⁻¹ B A:=by
    unfold Crown; rw [h.character, J.reflection]; rw [←Matrix.mul_assoc,←Matrix.mul_assoc,H.polar,Matrix.one_mul]
lemma push : Crown J H w z A.transpose B.transpose:=by
   unfold Crown; rw [h.character,transpose_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc,Matrix.mul_assoc,H.reflection,H.polar, Matrix.mul_one]
lemma donate {D E:Matrix W T ℝ} {K:Hive G T γ}[Fintype T][DecidableEq T] {v:γ→G.El} (hf:Crown J K w v D E) : Crown H K z v (A*D) (B*E) := by
   unfold Crown at *; rw [←Matrix.mul_assoc, h, Matrix.mul_assoc,hf,Matrix.mul_assoc]
lemma add (hA:Crown H J z w A' B'): Crown H J z w (A+A') (B+B') := by
   unfold Crown; rw [Matrix.mul_add,Matrix.add_mul, h,hA] -- rw of reducible Crown
lemma smul (q:ℝ): Crown H J z w (q • A) (q • B):=by
   unfold Crown at *; rw [Matrix.smul_mul,Matrix.mul_smul,h]
lemma miles (v: W→ℝ): H.burn z (A *ᵥ v)= B*ᵥ (J.burn w v):=by
   rw [← H.pigment, ←J.pigment,mulVec_mulVec,mulVec_mulVec,h]

omit h in
lemma earns {A B: Matrix X X ℝ}(hA:Crown H H z z A B): Crown H H z z A⁻¹ B⁻¹:=by
   rw [hA.character,H.reflection]; unfold Crown; simp only [Matrix.mul_inv_rev,H.inverse, inv_inv]
   rw [mul_assoc,mul_assoc,H.polar, Matrix.mul_one]
end Crown

-- preserved compact roster using Link inclusions
structure Tracks (H:Hive G X α) (J:Hive G W α) (e:X→W):Prop where
  law (i:X) : J.entry (e i)=H.entry i

namespace Tracks
variable {H:Hive G X α}{J: Hive G W α}{e:X→W}(h:Tracks H J e)
include h
omit [Fintype X] [Fintype W] [DecidableEq X] [DecidableEq W] in
lemma picks (i:X)(j:G.ColorIndex): J.pick (e i) j=e (H.pick i j):=by
   apply J.entry.injective; rw [h.law,J.hatch,h.law,H.hatch]

omit [Fintype X] [Fintype W] in
lemma pace (z:α→G.El)(i j:X):(H.paint z) i j=(J.paint z) (e i) (e j):=by
   have he i : J.room (e i) = H.room i ∧ J.ink (e i)= H.ink i:=⟨congr_arg Prod.fst (h.law i),congr_arg Prod.snd (h.law i)⟩
   by_cases hp:H.room i=H.room j
   · rw [H.pestle z i j hp,J.pestle z (e i) (e j) ((he i).1.trans (hp.trans (he j).1.symm)),(he i).1,(he i).2,(he j).2]
   rw [H.tone z i j hp,J.tone z (e i) (e j) (by rw [(he i).1,(he j).1]; exact hp)]

lemma tap {z:α→G.El}{w:β→G.El} [Fintype T] [Fintype V] [DecidableEq T] [DecidableEq V] {P:Hive G T β}{Q:Hive G V β}
    {g:T→V} (hs:Tracks P Q g) {A B:Matrix W V ℝ} (hA:Crown J Q z w A B): Crown H P z w (A.submatrix e g) (B.submatrix e g):=by
   unfold Crown at *; ext i j
   have hv : (J.paint z * A) (e i) (g j)=(B * Q.paint w) (e i) (g j):= congr_fun (congr_fun hA _) _
   rw [J.pins,Q.paws] at hv; rw [H.pins, P.paws]
   simp_rw [h.picks,hs.picks, ← h.pace, ← hs.pace] at hv; exact hv
omit [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W] in
lemma list (A:W→ℝ)(z:α→G.El): (J.burn z A) ∘ e = H.burn z (A∘e) :=by
   have he i:J.room (e i) = H.room i ∧ J.ink (e i)= H.ink i:=⟨congr_arg Prod.fst (h.law i),congr_arg Prod.snd (h.law i)⟩
   have ht(i): H.bunch (A ∘e) i = J.bunch A (e i) :=by
        apply PiLp.ext; intro j; change A _=A (J.pick (e i) j); rw [h.picks]
   ext i; change G.adjoint (z (J.room (e i))) (J.bunch A (e i)) (J.ink (e i))= G.adjoint _ _ _; rw [(he i).1,(he i).2,ht]
end Tracks

section Cluster
variable {H:Hive G X α}
-- vow along a V.Cluster. Build sub.Hive
variable (H) (s:Finset X)
def Full := ∀ i∈s,∀ j,H.room j=H.room i → j∈s
variable (h:Full H s)
def interior : Hive G s α where
    entry:= (Function.Embedding.subtype (fun i=>i∈s)).trans H.entry
    pick i j:=⟨H.pick i.val j,h i.val i.property _ (H.room_pick ..)⟩
    hatch i j:= H.hatch i.val j
omit [Fintype X] [DecidableEq X] in
lemma literal : Tracks (interior H s h) H Subtype.val:=⟨fun _=>rfl⟩
end Cluster
end YM.Planned.PrimaryIntegral295.Candles
