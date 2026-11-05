import YM.FullVolume.Nectar.BerylN
import YM.FullVolume.Spiral.Neum
/- Beam valuation in individual marks.NO need change R.r through Hose.H.Entity. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat.Luna.Aank Paint.Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal
variable {X I E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][CompleteSpace E]
def Tint (E X:Type)[NormedAddCommGroup E]: Type:= ↥(lp (fun _:X=>E) ∞)
namespace Tint
local notation "Y" => lp (fun _:X=>E) ∞
abbrev wear (x:Y): Tint E X:=x
abbrev cast (x:Tint E X):Y:=x
instance : NormedAddCommGroup (Tint E X):= inferInstanceAs (NormedAddCommGroup (lp (fun _:X=>E) ∞))
instance: NormedSpace ℝ (Tint E X):= by exact (inferInstanceAs (NormedSpace ℝ (lp (fun _:X=>E) ∞)))
instance: CompleteSpace (Tint E X):= by exact (inferInstanceAs (CompleteSpace (lp (fun _:X=>E) ∞)))
variable (E) in
def see (i:X): Tint E X→L[ℝ] E:=lp.evalCLM ℝ (fun _:X=>E) ∞ i
lemma liftEqual {f g:Tint E X}(h:∀ i,see E i f=see E i g):f=g:= Subtype.ext (funext h)
end Tint
open Tint
-- timestamp WITHOUT ∀ y Direction; analytic in **sup norm** on true points.
structure Feel (f: sun→ X→E)(b:ℝ):Prop where
    costs : ∃ u:sun→ Tint E X, (∀ t i,see E i (u t)= f t i)∧ PaidBeam u b
variable {f g:sun→X→E}{v a b:ℝ}
namespace Feel
lemma positives (h:Feel f a):0≤a:=h.costs.choose_spec.2.price
lemma earns (h:Feel f a)(hs:a≤b):Feel f b:=by obtain ⟨u,hx,h⟩:=h.costs; exact ⟨u,hx,h.larger hs⟩
lemma staticC (f:X→E) (hv:0≤a)(hp:∀ x,‖f x‖≤a): Feel (fun _=> f) a:=by
   let p:↥(lp (fun _:X=>E) ∞):=⟨f,memℓp_infty ⟨a,Set.forall_mem_range.mpr hp⟩⟩
   exact ⟨fun _=>wear p,fun _ _=>rfl,(PaidBeam.static (wear p)).larger (show ‖p‖≤a from lp.norm_le_of_forall_le hv hp)⟩
lemma worth (h:Feel f a) (p:sun)(x:X): ‖f p x‖ ≤ a:=by
    obtain ⟨u,hx,⟨z,hz,h⟩⟩:= h.costs; rw [←hx]; have hu:‖u p‖≤a:=by rw [h p]; exact (show ‖Beam.read (Tint E X) p z‖≤a from (Beam.price z p).trans hz)
    exact (lp.norm_apply_le_norm (by simp) (Tint.cast (u p)) x).trans hu
lemma scales (h:Feel f a)(c:ℝ):Feel (fun i y=> c • f i y) (|c| *a):= by
   obtain ⟨u,hx,h⟩:= h.costs; obtain ⟨z,hz,hp⟩:=h.arrives
   refine ⟨c • u,fun t i=>?_,c • z,(norm_smul ..).trans_le (mul_le_mul_of_nonneg_left hz (norm_nonneg _)),fun s=>?_⟩
   · rw [Pi.smul_apply,map_smul,hx]
   rw [map_smul,Pi.smul_apply,hp]
lemma united (h:Feel f a)(hp:Feel g b):Feel (fun i=> f i+g i) (a+b):=by
    obtain ⟨u,hx,h⟩:=h.costs; obtain ⟨v,hV,hp⟩:=hp.costs; refine ⟨u+v,fun i x=> ?_,h.plus hp⟩; rw [Pi.add_apply,map_add,hx,hV];rfl
section lpCost
variable [Fintype I]
local notation "K" => Glacial I E X
local notation "Y" => Tint E X
variable (E X) in
def ahead (i:I): Glacial I E X →L[ℝ] Tint E X:= lp.evalCLM ℝ (fun _:I=> lp (fun _:X=>E) ∞) 1 i
lemma mont (x: Glacial I E X): ‖x‖=∑ i:I,‖ahead X E i x‖:= (Glacier.footage (show Glacier I E X from x)).symm
variable (V:sun→ I→ X→E) (u:sun→Glacial I E X)
lemma factored (ha:PaidBeam u v)(h:∀ i:I,∀ y x,Glacial.evalP E i x (u y)= V y i x):∃ a:I→ℝ,∑ i,a i ≤ v ∧∀ i,Feel (fun t=>V t i) (a i):=by
    obtain ⟨P,hp,hx⟩:=ha.arrives
    let a(i:I):=∑' n:ℕ, ‖ahead X E i (P n)‖; have ht(i):Summable fun n:ℕ=>‖ahead X E i (P n)‖:=(togg P).2.1.of_nonneg_of_le (fun i=>norm_nonneg _) fun n=>lp.norm_apply_le_norm (by simp) (show Glacier I E X from P n) i
    refine ⟨a,?_,fun i=>⟨fun t=>ahead X E i (u t),fun x p=>h i x p,?_⟩⟩
    · apply le_trans _ hp; unfold a; rw [← Summable.tsum_finsetSum (hf:=fun i _=>ht i)]; simp_rw [← mont]; exact le_of_eq (paid P).tsum_eq
    let B: Beam (Tint E X):=⟨fun n=>ahead X E i (P n),memℓp_gen (by simpa using ht i)⟩; refine ⟨B,(paid B|>.tsum_eq.symm).le,fun s=>?_⟩
    rw [hx]; refine ((ahead X E i).hasSum (P.spar (abs_le.mpr s.property))).unique (show _ from (?_: HasSum (fun n=>ahead X E i (s.val ^ n • P n)) _)) -- function B.spar convert
    simp_rw [map_smul]; exact B.spar (abs_le.mpr s.property)
-- Up from parts. Enough to avoid constants across poses scale.
lemma arrays {v:I→ℝ}(h:∀ i,Feel (fun t=>V t i) (v i)):∃ u:sun→Glacial I E X,(∀ i:I,∀ y x,Glacial.evalP E i x (u y)=V y i x)∧ PaidBeam u (∑ i,v i):=by
    choose g hg P hp hP using fun i=> show ∃ g:sun→ Tint E X, (∀ t x, see E x (g t)=V t i x)∧ ∃ P:Beam (Tint E X), ‖P‖≤v i∧∀ t,g t=Beam.read _ t P from (h i).costs.imp (fun x ⟨h,hx⟩=>⟨h,hx.arrives⟩)
    let f(i:ℕ): Glacial I E X:= Glacial.fold ⟨fun j:I=> (P j i: lp (fun _:X=>E) ∞),memℓp_gen (by apply Summable.of_finite)⟩
    have he(i): ‖f i‖=∑ j:I,‖P j i‖:=mont (f i)
    let B:Beam (Glacial I E X):=⟨f,memℓp_gen (by simp only [ENNReal.toReal_one,Real.rpow_one,he]; exact summable_sum fun i _=> (paid (P i)).summable)⟩
    let u(s:sun):=Beam.read _ s B; refine ⟨u,fun i y x=> ?_,B,?_,fun _=>rfl⟩
    · suffices he:ahead X E i (u y)= g i y from ((congr_arg (see E x) he).trans (hg ..))
      rw [hP]; have hx:=(ahead X E i).hasSum (B.spar (abs_le.mpr y.property)); simp_rw [map_smul] at hx; exact hx.unique ((P i).spar (abs_le.mpr y.property))
    rw [← (paid B).tsum_eq, show (fun i:ℕ=> ‖B i‖)=_ from funext he];rw [Summable.tsum_finsetSum]; exact sum_le_sum fun i _=> (paid (P i)|>.tsum_eq).trans_le (hp i); exact fun i _=> (paid (P i)).summable
end lpCost
end Feel
end YM.FullVolume.Nectar
