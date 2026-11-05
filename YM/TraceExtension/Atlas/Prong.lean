import YM.TraceExtension.Atlas.Walls
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(h:G.Simple)
open LinearMap LoomX
local notation "F₀"=> Bel C.book
variable {H:(Climb.Bel C.book).Hierarchy}
section general
variable {I E: Type*}[Fintype I][DecidableEq I][NormedAddCommGroup E][NormedSpace ℂ E]
variable (P:Bi E)(S:E→ₛₗ[starRingEnd ℂ] E)(B:I→E) (hB:∀ x:E,∃ f:I→ℂ,x=∑ i,f i • B i)(L:I→ℝ)(hL:∀ i,0 < L i)(ht:∀ i j,P (B i) (B j)=if j=i then (↑(L j):ℂ) else 0)(hp:∀ i,S (B i)=B i)
include hB ht hp
private lemma bino(v w:E): P v w=P w v ∧ P (S v) (S w)=star (P v w):=by
    obtain ⟨f,hf⟩:=hB v; obtain ⟨g,hg⟩:=hB w; rw[hf,hg];
    have he(i j):P (B i) (B j)=P (B j) (B i):=by by_cases h:i=j;subst i;rfl; rw[ht,ht,if_neg (Ne.symm h),if_neg h]
    have hH(i j): star (P (B i) (B j))=P (B i) (B j):=by rw[ht];split<;>simp
    constructor
    · simp only [map_sum, map_smul, _root_.sum_apply,_root_.smul_apply,Finset.smul_sum]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by rw[he j i,smul_comm]
    simp only [map_sum, map_smul,map_smulₛₗ, _root_.sum_apply,_root_.smul_apply,hp, star_sum,star_smul,hH];rfl
include hL in
private lemma bino2(v:E)(hv:v≠0):0 < (P (S v) v).re:=by
    obtain ⟨f,hf⟩:= hB v; have hg : ∃ i,f i≠0:=by by_contra! hh; apply hv; simp [hf,hh]
    have hw : (P (S v) v).re=∑ i,‖f i‖^2 * L i:=by
       rw[hf]; simp only [map_sum,map_smul,map_smulₛₗ,hp,_root_.sum_apply,_root_.smul_apply, Finset.smul_sum]; rw[Complex.re_sum]
       refine Finset.sum_congr rfl fun i _=> ?_; rw[Finset.sum_eq_single i];
       · rw [ht,if_pos rfl,smul_eq_mul,smul_eq_mul,← mul_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq,← Complex.ofReal_mul];rfl
       · intro j hj he; rw [ht, if_neg (Ne.symm he),smul_zero,smul_zero]
       simp
    rw[hw]; obtain ⟨i,hi⟩:= hg; refine Finset.sum_pos' (fun i _=>mul_nonneg (sq_nonneg _) (hL i).le) ⟨i,Finset.mem_univ _,mul_pos (by positivity) (hL i)⟩
end general
include h in
private lemma braid(v w:Active (Bel C.book)): cine H 1 v w=cine H 1 w v ∧ cine H 1 (starA H v) (starA H w)=star (cine H 1 v w):= bino (cine H 1) (starA H) (page C) (page_basis h) (brightness G) (fun i j=> bills h j i) page_real v w
lemma lace_sym(P:laceC H)(i j):P.val i j=P.val j i:=P.property.1 ..
lemma lace_turn(P:laceC H)(s i j) :P.val (swingA H s i) (swingA H s j) = P.val i j:= P.property.2.2 ..
lemma lace_star(P:laceC H)(i j):P.val (starA H i) (starA H j)=star (P.val i j):=P.property.2.1 ..
include h
set_option maxHeartbeats 500000 in
lemma active_formula(v w): (scannerX H 1).val v w=4* HBasis H (cine H 1) v w:=by
    change Hmean H _ _ _=_; let P:= cine H 1; let Y:= P+P.flip; let Z:=Y+flipC (starA H) Y
    have hm: Z=(4:ℂ) • P:=by
        ext1 x;ext1 y; change P x y+P y x+flipC _ Y x y = 4*P x y; rw [(braid h y x).1,flipC_apply]; change P x y+P x y+star (P _ _+P _ _) = _; rw[(braid h x y).2,(braid h y x).2,(braid h y x).1]; simp only [star_add,star_star]; ring
    unfold Hmean; unfold Z Y P at hm; rw [hm]; rw[hbasis_smul];rfl
set_option maxHeartbeats 500000 in
lemma positive_turn (v:Active (Bel C.book))(hw:v≠0): 0 < ((scannerX H 1).val (starA H v) v).re:=by
    rw [active_formula h]; refine (fun (x:ℂ) (hx:0<x.re)=> (show 0 < ((4:ℂ)*x).re from by norm_num; linarith)) _ (hbasis_pos H (cine H 1) v hw (fun p h'=> ?_))
    exact bino2 (cine H 1) (starA H) (page C) (page_basis h) (brightness G) (alive h) (fun i j=>bills h j i) page_real p h'
end YM.Trace.Pilot
