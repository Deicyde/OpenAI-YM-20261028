import YM.TraceExtension.Cask.Poetry
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L K J:Type}[DecidableEq V][DecidableEq L][DecidableEq K][DecidableEq J]{n:Side}[Fintype V][Fintype L][Fintype K][Fintype J]{G:Gauge}
set_option quotPrecheck false
local notation "M!"=> Rain V G
local notation "μ"=>freq V G
local notation "u!"=>prior G n
local notation "E"=> Config G n
local notation "I!"=>Grain L K J
variable {P:Staff V (Grain L K J) n}(R:Rep G n) (x:J→V)(B: K→Box n)(F:Grain L K J→ Config G n → Rain V G → ℂ)
variable {w:Duel V→ℝ}{e u:ℝ}(M:Decked P R F w e u)(H:Roles P x B)
variable (p q: V→ Config G n → Rain V G→ℂ)(φ: Finset V→ Rain V G→ Config G n→ Config G n)
-- copy demands:
def tuft (p q:V → Config G n→ Rain V G→ℂ)(S:Finset V)(U:Config G n)(v : Rain V G):ℂ:= (∏ i∈S,p i U v)*(∏ j∈univ \ S,q j U v)
def plebe (i:V) (U:Config G n):= ∫ v,q i U v-p i U v∂freq V G
def brush (P:Staff V (Grain L K J) n) (U: Config G n) (v : Rain V G)(S:Finset V):= (Real.exp (R.exponent U):ℂ)*clothW x (fun i=>F i U v)*trump P B (flags R.p.threshold U) (fun i=> F i U v) S
structure Brant (P:Staff V (Grain L K J) n):Prop where
    native S : Measurable (uncurry (φ S))
    turns S v : MeasurePreserving (φ S v) (prior G n) (prior G n)
    stem i : Envelope (uncurry (p i))
    shape i : Envelope (uncurry (q i))
    neck i U : rule {i} (fun v=> q i U v-p i U v)
    wind U v S: brush R x B F P U v S = (R.eval (φ S v U):ℂ)*tuft p q S (φ S v U) v
local notation "l!"=>shore P R (lyrics P F)
variable {p q φ} {a b σ δ t:ℝ}(hp:R.Lawful a b σ δ t)(W:Brant R x B F p q φ P)
include W hp H M
lemma rigour (U:E): (shore P R (lyrics P F) U).part (Stock.final (Duel V))= ∫ v, ∑ S:Finset V, (-1:ℂ)^S.card*((R.eval (φ S v U):ℂ)*tuft p q S (φ S v U) v)∂freq V G:=by
    rw[full_line x B R F M H]; simp_rw [← W.wind]; refine congr_arg (fun f:M!→ℂ=>∫ v,f v∂μ) (funext fun v=> ?_)
    rw [mul_sum]; apply sum_congr rfl; intro i _; unfold brush; ring
lemma cove : (∫ U,(shore P R (lyrics P F) U).part (Stock.final (Duel V))∂prior G n)=∫ U,(R.eval U:ℂ)*(∏ i,plebe p q i U)∂prior G n:=by
    let f(U:E)(v:M!)(S: Finset V):ℂ:= (-1:ℂ)^ S.card*((R.eval U:ℂ)*tuft p q S U v); let l(U:E)(v:M!):=∏ i,(q i U v-p i U v)
    have hl U v:(R.eval U:ℂ)*l U v=∑ S:Finset V, f U v S:=by
       have h': l U v=∑ S:Finset V, ((-1:ℂ)^S.card)*tuft p q S U v:=by
          unfold l; simp_rw [sub_eq_add_neg,add_comm _ (-(p _ _ _))]; rw [prod_add,Finset.powerset_univ]; refine sum_congr rfl fun i _=>?_
          unfold tuft; simp_rw [show ∀ j, - p j U v=(-1:ℂ)*p j U v from fun i=> by ring, Finset.prod_mul_distrib,Finset.prod_const,mul_assoc]
       rw [h', mul_sum]; exact sum_congr rfl fun i _=> (mul_left_comm ..)
    have hx(s:Finset V): Envelope (uncurry (fun U v=>f U v s)):=by
       have hy:Envelope (uncurry (tuft p q s)):= envUmul (envUprod s (fun i=>uncurry (p i)) (fun i _=>W.stem i)) (envUprod (univ\ s) (fun i=>uncurry (q i)) (fun i _=> W.shape i))
       have hv:=based (fromR (R.envelope hp)) (fun i:E × M!=>i.1) measurable_fst
       exact envUmul (constV _) (envUmul hv hy)
    let g (U:E)(v:M!)(s:Finset V):= f (φ s v U) v s
    have hz(s:Finset V): Envelope (uncurry (fun U v=>g U v s)):= based (hx s) (fun i:E × M!=> (φ s i.2 i.1,i.2)) (Measurable.prodMk ((W.native s).comp (Measurable.prodMk measurable_snd measurable_fst)) measurable_snd)
    let G' := fun U v=>∑ i,g U v i; let F':=fun U v=> ∑ i,f U v i
    have hF: Envelope (uncurry F'):= envUsum univ (fun i=>uncurry (fun U v=>f U v i)) (fun i _=> hx i)
    have hG: Envelope (uncurry G'):= envUsum univ (fun i=>uncurry (fun U v=>g U v i)) (fun i _=> hz i)
    have he(v): (∫ U,G' U v∂u!) = ∫ U,F' U v∂u!:=by
       unfold G' F'; rw [integral_finsetSum _ (fun i _=> show Integrable (fun U=>g U v i) _ from capped (based (hz i) (fun k : E=>(k,v)) (Measurable.prodMk measurable_id measurable_const)) u!), integral_finsetSum _ (fun i _=> show Integrable (fun U=>f U v i) _ from capped (based (hx i) (fun k:E=>(k,v)) (Measurable.prodMk measurable_id measurable_const)) u!)]; refine sum_congr rfl fun s _=>?_
       let F (U:E):= f U v s; let V':=φ s v; have hm:Measurable F := show Measurable ((uncurry fun U v=> f U v s) ∘ (fun k:E=>(k,v))) from (hx s).meas.comp (Measurable.prodMk measurable_id measurable_const)
       calc
          _ = ∫ x,F x∂Measure.map V' u!:= (integral_map (W.turns s v).measurable.aemeasurable hm.aestronglyMeasurable).symm
          _ = _:=by rw [(W.turns s v).map_eq]
    have hy(U:E): (∫ v,F' U v∂μ)=(R.eval U:ℂ)*(∏ i,plebe p q i U):=by
       unfold F'; simp_rw[← hl]; rw [integral_const_mul]; apply congr_arg (_ * ·)
       exact harvest _ (fun i=> {i}) (fun i v=> q i U v-p i U v) (by simp [Set.PairwiseDisjoint,Set.Pairwise,Function.onFun]) (fun i _=> W.neck i U)
    simp_rw [← hy]; simp_rw [rigour R x B F M H hp W]; change (∫ U, (∫ v,G' U v∂μ) ∂prior G n)=_
    rw [integral_integral_swap (capped hG _),integral_integral_swap (f:=F') (capped hF _)]; simp_rw [he]
end YM.Trace.Cask
