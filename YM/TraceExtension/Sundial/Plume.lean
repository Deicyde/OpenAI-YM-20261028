import YM.TraceExtension.Sundial.Elven
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot Pith
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)
set_option quotPrecheck false
local notation "Act"=> (Bel C.book).Field 4
variable (P P': change S 4)
structure Tilt (P P':change S 4)(x y:ℝ): Prop where
    portrait (f): P' f=P (peel H h x y f)
variable {x y:ℝ}(hE:Tilt H h P P' x y)
include hE
lemma Tilt.stress (i j:Axis): P' (standard4 C i j)= y • P (standard4 C i j):=by rw[hE.portrait _, vest]; exact (P.toLinearMap.restrictScalars ℝ).map_smul ..
include hp in
lemma Tilt.lands : P' (stepField C)=x • P (stepField C):=by rw[hE.portrait _, mere F H h hp]; exact (P.toLinearMap.restrictScalars ℝ).map_smul ..

include hp
local instance (n:ℕ): ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
variable (χ:E4→ℝ)(t:ℝ)(ht:0<t)
open Work.A05
include ht
lemma cocore {Y:Act}{u:ℝ}(hV:P' Y=u • P Y)(b:Axis) : pron b (P' Y) (P' ∘ dial C) sail t= (u*x) • pron b (P Y) (P ∘ dial C) sail t:=by
    let s:=stepField C; let v:= P∘dial C;let f(z):= (S.classMoment S (fun _: Fin 2=>4) (t • z));
    let g(z):= f z (Fin.cons (P Y) v)
    let F'(z):= f z (Fin.cons (P' Y) (P' ∘ dial C))
    have hX(c):Fin.cons (α:=fun _:Fin (1+1)=>S.Field 4) (P' Y) (P' ∘ dial C) c = (![↑u,↑x]:Fin 2→ℂ) c • Fin.cons (α:=fun _:Fin (1+1)=>S.Field 4) (P Y) v c:= by
         fin_cases c
         · exact hV.trans (RCLike.real_smul_eq_coe_smul ..)
         exact (hE.lands F H h hp P P').trans (RCLike.real_smul_eq_coe_smul ..)
    have hh: F'= fun z=>(u*x) • g z:= by
         ext1 z; unfold F' g; rw [show Fin.cons _ _=_ from funext hX,(f z).map_smul_univ]; simp [Fin.prod_univ_two, Complex.real_smul]
    let V(i:Fin 2):S.Tag:=⟨4,Fin.cons (α:=fun _:Fin (1+1)=>S.Field 4) (P Y) v i⟩
    have hf : DifferentiableAt ℝ g sail:=by
        let p:= F.room.kernel; have ht:= smul_conf ht sail_at; have H: DifferentiableAt ℝ (fun x'=> Ward.disc V x') (t • sail):= ((S.class_smooth S p.smooth V).contDiffAt ((conf_open _).mem_nhds ht)).differentiableAt (by simp)
        let D: Points 2→L[ℝ] Points 2:= t • ContinuousLinearMap.id ℝ _; exact DifferentiableAt.comp (f:=⇑D) _ H D.differentiableAt
    change fderiv ℝ F' sail _=_; rw [hh,fderiv_fun_const_smul hf];rfl
lemma total_p : E (fun _=> P') t=(y*x) • E (fun _=> P) t ∧ B (fun _=> P') t=(x*x) • B (fun _=> P) t:=by
   constructor
   · unfold E divRead post; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> cocore F H h hp _ _ hE t ht (hE.stress ..) _
   unfold B; rw[div_cross F sail sail_at ht,div_cross F sail sail_at ht]; exact cocore F H h hp _ _ hE t ht (hE.lands F H h hp P P') _
omit ht
lemma huzzy (Y:(Bel C.book).Stress)(u:ℝ)(hV:∀ i j,P' (Y i j)=u • P (Y i j))(i b:Axis):
       say (C:=C) sail χ i Y b (stepField C) (dial C) t P'= (u*x*x) • say (C:=C) sail χ i Y b (stepField C) (dial C) t P:= by
   let r (Q:change S 4): Fin 3→ S.Field 4:= ![Q (Y i b),Q (stepField C),Q (stepField C)]
   have hr (Q:change S 4): Fin.cons (α:=fun _:Fin (1+2)=> S.Tag) (⟨4,Q (Y i b)⟩:S.Tag) (Fin.cons (α:=fun _: Fin 2=> S.Tag) ⟨4,Q (stepField C)⟩ (fun j:Fin 1=>⟨4,Q (dial C j)⟩))=fun k=>⟨4,r Q k⟩:=by funext i; fin_cases i<;> rfl
   unfold say
   rw [smul_neg,← integral_smul]; congr! 1; refine integral_congr_ae (ae_of_all _ fun z=> ?_)
   unfold sheet; rw [hr,hr]; let w:= Work.A05.weight χ i (fun _=>1) z; let M:= S.classMoment S (fun _:Fin 3=>4) (t • Points.cons z sail)
   have ht : r P' = fun i=> (![↑u,↑x,↑x]:Fin 3→ℂ) i • (r P i):=by
      funext j; fin_cases j
      · exact (hV i b).trans (RCLike.real_smul_eq_coe_smul ..)
      all_goals exact (hE.lands F H h hp _ _).trans (RCLike.real_smul_eq_coe_smul ..)
   change w*M (r P')=(u*x*x) • (w*(M (r P)))
   rw[ht,M.map_smul_univ]; simp [Fin.prod_univ_succ,Complex.real_smul];ring
lemma shells : R (C:=C) (fun _=>P') χ t= (y*x*x) • R (fun _=>P) χ t ∧ Q (fun _=>P') χ t=(x*x*x) • Q (fun _=>P) χ t:=by
   constructor
   · unfold R flair; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> huzzy F H h hp _ _ hE χ t _ _ (Tilt.stress H h _ _ hE) i _
   unfold Q flair; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=> huzzy F H h hp _ _ hE χ t _ _ ?_ i _
   intro i j; by_cases hb:i=j
   · simp only [Pith.erase,if_pos hb]; exact hE.lands F H h hp P P'
   simp[Pith.erase,hb]
end YM.Trace.Sundial
