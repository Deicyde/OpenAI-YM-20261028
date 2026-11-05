import YM.UVExtension.Projection.Rail

/-! Exact leader read and decaying wave equivalence; submodule comparisons. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Precision Tree Exterior Bloch Laurent Wilson Stationary Filter Function Finset Matrix
open scoped Matrix Topology BigOperators ContDiff Classical
variable {G : Gauge} (P : Rates G) (B : Bed) {x y: Cube G}

def painted : Submodule ℝ (Cube G × ℝ):=
    (P.seamᗮ ⊓ P.valid).prod ⊤
lemma paints_iff (z : Cube G × ℝ): z∈painted P ↔ P.Lodge z.1:= ⟨fun h=> show _ ∧ _ from h.1, fun h=> show _ ∧ _ from ⟨show _ ∧ _ from h,trivial⟩⟩

def traceHead : Cube G × ℝ →ₗ[ℝ] Head P where
    toFun x:= stroke P x.1
    map_add' x y:=by
      funext i j v; unfold stroke; obtain ⟨L,hL⟩:=P.hat_cost j i v
      exact Eq.trans (congr_fun hL (x.1+y.1)) ((map_add L _ _).trans (congr_arg₂ _ (congr_fun hL x.1).symm (congr_fun hL y.1).symm))
    map_smul' a x:=by
      funext i j v; unfold stroke; obtain ⟨L,hL⟩:= P.hat_cost j i v
      exact Eq.trans (congr_fun hL (a • x.1)) ((map_smul L a x.1).trans (congr_arg _ (congr_fun hL x.1).symm))

def loopHead : Cube G →ₗ[ℝ] Stamp P where
    toFun:= quick P
    map_add' x y:=by
      funext i v; unfold quick style; obtain ⟨L,hL⟩:= P.e_cost 2 i v
      exact Eq.trans (congr_fun hL (x+y)) ((map_add L _ _).trans (congr_arg₂ _ (congr_fun hL x).symm (congr_fun hL y).symm))
    map_smul' a x:=by
      funext i v; unfold quick style; obtain ⟨L,hL⟩:= P.e_cost 2 i v
      exact Eq.trans (congr_fun hL (a • x)) ((map_smul L a x).trans (congr_arg _ (congr_fun hL x).symm))

def amount : Cube G × ℝ→ₗ[ℝ] Stamp P:= (LinearMap.snd ℝ (Cube G) ℝ).smulRight (reading P B)+(loopHead P).comp (LinearMap.fst ..)
lemma amount_eq (x:Cube G)(a:ℝ):amount P B (x,a)=priceLoop P B (x,a):=rfl

def mist : Submodule ℝ (Stamp P) where
    carrier := {f|Neglect P f}
    zero_mem' := ⟨fun _=> 0,tendsto_const_nhds,fun i p q u v _ _=>by simp⟩
    add_mem' := by
      rintro f g ⟨b,hb,h⟩ ⟨a,ha,h'⟩
      refine ⟨fun i=> b i+a i,by simpa using hb.add ha,fun i p q u v hu hv=> ?_⟩
      rw [mul_add]; exact (norm_add_le ..).trans (add_le_add (h i p q u v hu hv) (h' i p q u v hu hv))
    smul_mem' := by
      rintro a f ⟨b,hb,h⟩
      refine ⟨fun i=> ‖a‖*b i,by simpa using hb.const_mul ‖a‖,fun i p q u v hu hv=> ?_⟩
      simp only [Pi.smul_apply,norm_smul]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (h i p q u v hu hv) (norm_nonneg _)
structure Aligns (w: Cube G × ℝ) (H : Head P) (F : Stamp P): Prop where
    ink : w ∈ painted P
    hat : traceHead P w=H
    wave : amount P B w - F ∈ mist P
variable {P B}
namespace Aligns
variable {x y z: Cube G×ℝ} {H V:Head P}{F W:Stamp P}
lemma add (h:Aligns P B x H F)(he:Aligns P B y V W):Aligns P B (x+y) (H+V) (F+W):=by
  refine ⟨Submodule.add_mem _ h.ink he.ink,by rw [map_add,h.hat,he.hat],?_⟩; rw [map_add,add_sub_add_comm]; exact Submodule.add_mem _ h.wave he.wave
lemma scale (h:Aligns P B x H F)(b:ℝ):Aligns P B (b • x) (b • H) (b • F):=by
  refine ⟨Submodule.smul_mem _ b h.ink,by rw [map_smul,h.hat],?_⟩; rw [map_smul,← smul_sub]; exact Submodule.smul_mem _ b h.wave
lemma unicity (h:Aligns P B x H F)(hh:Aligns P B y H F)(i : G.ColorIndex)(he:Toned P)(hp:Keyline P B): x=y:= by
  suffices H:x-y=0 from sub_eq_zero.mp H
  have hv:= h.add (hh.scale (-1))
  rw [neg_one_smul, neg_one_smul, neg_one_smul,add_neg_cancel,add_neg_cancel,← sub_eq_add_neg] at hv
  obtain ⟨hr,hE⟩:= annihilate P i he B hp _ _ ((paints_iff P _).mp hv.ink) hv.hat (by simpa only [sub_zero] using! hv.wave)
  exact Prod.ext hr hE
lemma join {I:Type}(P : Rates G)(B)(s:Finset I) (f:I→ Cube G×ℝ)(g:I→ Head P)(h:I→ Stamp P)(he:∀ i∈s,Aligns P B (f i) (g i) (h i)) : Aligns P B (∑ i∈s,f i) (∑ i∈s,g i) (∑ i∈s,h i):=by
  induction s using Finset.induction with
  | empty=> simp only [sum_empty]; exact ⟨Submodule.zero_mem _,map_zero _,by rw [map_zero,sub_zero]; exact Submodule.zero_mem _⟩
  | insert i s hi ih=> simp_rw [sum_insert hi]; exact (he i (mem_insert_self ..)).add (ih fun j hj=> he j (mem_insert_of_mem hj))
end Aligns
end YM.UVExtension.Projection
