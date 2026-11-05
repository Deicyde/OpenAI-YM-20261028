import YM.TraceExtension.Atlas.Center
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}{C: Family G}{X:Extraction.Order}{L:Register G}
variable {S T: Table L}
open LinearMap
abbrev Bi(E:Type*)[NormedAddCommGroup E][NormedSpace ℂ E] := E→L[ℂ] E→L[ℂ] ℂ
abbrev Carpet (S:Table L):= Bi ↥(Active S)

lemma packV {E: Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] (M:E→E→ℂ) (L:E→ E→L[ℂ] ℂ)(hL:∀ u v,L u v=M u v)(ht:∀ w:E,∃ K:E→L[ℂ] ℂ,∀ v,K v=M v w): ∃ f:E→L[ℂ] E→L[ℂ] ℂ,∀ v w,f v w=M v w:=by
    let f: E→ₗ[ℂ] E→L[ℂ] ℂ:={
        toFun:=L
        map_add':= fun i j=> ContinuousLinearMap.ext (fun x=> by change L (i+j) x=L i x+L j x; rw[hL,hL,hL, ← (ht x).choose_spec (i+j),← (ht x).choose_spec i, ← (ht x).choose_spec j]; rw [map_add])
        map_smul':= fun c i=> ContinuousLinearMap.ext (fun x=> by change L (c • i) x=c • L i x; rw [hL,hL,← (ht x).choose_spec (c • i), ← (ht x).choose_spec i]; rw [map_smul]) }
    let B:E→L[ℂ] E→L[ℂ] ℂ:= { f with cont:= by change Continuous (⇑f); exact f.continuous_of_finiteDimensional}; exact ⟨B,fun v w=> (show L v w=M v w from hL _ _)⟩
lemma press(H:S.Hierarchy)(x:Points 2): ∃ M: Carpet S, ∀ v w, M v w= S.classMoment S (fun _=>4) x ![(swingA H (Signed.mirror 0) v).val, w.val]:=by
    let P:=S.classMoment S (fun _ : Fin 2=>4) x
    -- curry deploy
    let M(v w:Active S):= P ![(swingA H (Signed.mirror 0) v).val,w.val]
    have he(v): ∃ L:Active S→L[ℂ] ℂ,∀ w,L w=M v w:=by
       let w:= (swingA H (Signed.mirror 0) v).val; let X:= P.toLinearMap ![w,0] 1
       refine ⟨LinearMap.toContinuousLinearMap (X.comp (Active S).subtype), fun i=> ?_⟩
       change P (update ![w,0] 1 i.val)= _; congr 1; funext a; fin_cases a<;>rfl
    choose L hL using he
    have ht(w): ∃ K:Active S→L[ℂ] ℂ,∀ v,K v=M v w:=by
       let X:= P.toLinearMap ![0,w.val] 0; let V:=(Active S).subtype.comp (swingA H (Signed.mirror 0)); refine ⟨LinearMap.toContinuousLinearMap (X.comp V),fun i=>?_⟩; change P (update ![0,w.val] 0 (V i))=_; unfold M; congr 1; funext a; fin_cases a<;> rfl
    exact packV M L hL ht
def cine(H:S.Hierarchy) (r:ℝ): Carpet S:= (press H (r • camera 0)).choose
lemma cine_pay(H:S.Hierarchy) (r:ℝ)(v w): cine H r v w=S.classMoment S (fun _=>4) (r • camera 0) ![(swingA H (Signed.mirror 0) v).val, w.val]:= (press ..).choose_spec v w

namespace LoomX
local notation "F₀"=> Bel C.book
-- construct basis

def PBasis (h:G.Simple): Module.Basis Face ℂ (Active (Bel C.book)):= Module.Basis.mk (page_ind h) <| by
    intro v _; obtain ⟨u,hu⟩:= page_basis h v; rw[hu]; exact Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _)))
lemma basis_at (h:G.Simple)(i): PBasis (C:=C) h i=page C i:=by rw [PBasis,Module.Basis.mk_apply]
variable (h:G.Simple)
variable {H:(Climb.Bel C.book).Hierarchy}
-- Bilinear diagnostic on these actual graded fields.

def heft (p:Plane):= Mask.maskA 0 p
lemma coat_eq(p:Plane): coat 0 p= (Mask.maskA 0 p:ℝ)*(4*Maxwell.normal):=by unfold coat Mask.maskA; split <;> push_cast <;> ring

def brightness(G:Gauge)(p:Face): ℝ:= G.lieDim*(4*Maxwell.normal)^2*(if p.val.1=p.val.2 then 2 else 1)
include h
lemma alive(p:Face):0<brightness G p:=by
    have ht:0 < (G.lieDim:ℝ):= Nat.cast_pos.mpr (by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := h.nontrivial_color; exact Module.finrank_pos)
    unfold brightness; have hz:= Maxwell.normal_pos; split<;>positivity
include h
set_option maxHeartbeats 500000 in
lemma bills (p q:Face): cine H 1 (page C q) (page C p)= if p=q then (↑(brightness G p):ℂ) else 0:=by
    rw [cine_pay,one_smul, swing_act,show (Bel C.book).mirror H.spin 4 (Signed.mirror 0) (page C q).val =_ from axis_e ..]
    let F:= C.book.grid; let a:= Mask.marks 0 q; let w:= modulator p; let U:=portLine F (some p);let B:=reader F 0 p.val.1 p.val.2
    let k:= (G.lieDim:ℂ)*(coat 0 p.val.1:ℂ)*(coat 0 p.val.2:ℂ)
    have hu : U= w • (k⁻¹ • negative F 0 p.val.1 p.val.2):= rfl
    let g:= negative F 0 p.val.1 p.val.2; let x:=petal F q
    have hp': g ((a:ℂ) • x)=(F₀).classMoment (F₀) _ (camera 0) ![((a:ℂ) • x), (page C p).val]:=by
       let t:Fin 2→ (Bel C.book).Field 4:= ![((a:ℂ) • x),(page C p).val]
       let v:Fin 2→ (Bel C.book).Tag:=fun i=>⟨4,t i⟩
       have he: (Fin.cons (α:=fun _ : Fin (1+1)=>(Bel C.book).Tag) ⟨4,(a:ℂ) • x⟩ (negs F p.val.1.val.1 p.val.1.val.2 p.val.2.val.1 p.val.2.val.2))=v:=by funext i; fin_cases i<;>rfl
       change negative F _ _ _ _= (Bel C.book).useAt (Bel C.book) _ v; unfold negative; rw[listens,he]
    change _=_; rw[← hp', g.map_smul, smul_eq_mul]; have he:= separates F h (some p) (some q);simp only [Option.some.injEq] at he
    change U x=_ at he; rw[hu] at he
    change w*(k⁻¹*g x)=(if p=q then 1 else 0) at he
    have hk: k≠0:= mul_ne_zero (mul_ne_zero (by norm_cast; exact (by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := h.nontrivial_color; exact Module.finrank_pos.ne')) (Complex.ofReal_ne_zero.mpr (coat_ne _ _))) (Complex.ofReal_ne_zero.mpr (coat_ne _ _))
    have hw:w≠0:=by unfold w modulator;split<;>norm_num
    have hc: g x = k * w⁻¹ * (if p=q then 1 else 0):=by rw [← he];field_simp
    rw [hc]; split_ifs with h'; swap; · rw[mul_zero,mul_zero];
    subst p
    have ha : (a:ℂ)*(a:ℂ)=1:=by exact_mod_cast flag_sq 0 q
    have hv : k=(G.lieDim:ℂ)*(↑((4*Maxwell.normal)^2:ℝ):ℂ)*(a:ℂ):=by unfold k a Mask.marks; rw[coat_eq,coat_eq]; push_cast; ring
    rw [mul_one,← mul_assoc, hv,mul_left_comm (a:ℂ),ha,mul_one]; unfold brightness w modulator; split_ifs <;> push_cast <;> ring

end LoomX
end YM.Trace.Pilot
