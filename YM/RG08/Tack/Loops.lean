import YM.RG08.Tack.Gloss

/-! # Positive-order block penalty, issued in uniform actual minimizing patch. RHS of
 real price uses unchanged choices and finite registry. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Tack
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03
open AnalyticNext.QuarticMatch.Radius Articles Model
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius NNReal

variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}

def ask (S:StepData c f)(t:S.Choices)(i:Axis)(q:Site c):Still (Epic S.patch G c):= fun w=> S.kernel.penalty* G.price (represent (high S w) (q,i)*(S.prediction (represent (low S w)) t (q,i))⁻¹)
lemma ask_real (h:S.patch.Branches S.kernel G)(t:S.Choices)(i:Axis)(q:Site c): ask (G:=G) S t i q=ᶠ[𝓝 0] mold S.patch S.kernel G (guard h).tag i ∘ roll (glance q (slink S.patch i)):=by
 unfold ask; simp_rw [Work.F03.represent_link];exact when h t i q
lemma ask_pace (h:S.patch.Branches S.kernel G)(t:S.Choices)(i:Axis)(q:Site c):Pace (ask (G:=G) S t i q):= by
 apply ContDiffAt.congr_of_eventuallyEq _ (ask_real h t i q) -- orientation
 have hh := roll_pace (glance_pace q (slink S.patch i (G:=G)))
 have he :roll (glance q (slink S.patch i (G:=G))) (0:Cellar (Epic S.patch G c))=0:=rfl
 exact ContDiffAt.comp (0:Cellar (Epic S.patch G c)) (g:=mold S.patch S.kernel G (guard h).tag i) (by rw [he];exact mold_pace h _ _) hh


def parade (h:P.Branches K G) (n:ℕ):Flake n (Market (Head P G)):=∑ i:Axis,trace n (mold P K G (guard h).tag i) (slink P i)
def park (h:P.Branches K G)(n:ℕ)(σ:ℝ):=∑ i:Axis,price n σ (mold P K G (guard h).tag i) (slink P i)

theorem parade_bill (h:P.Branches K G)(n:ℕ){σ:ℝ}: Held (carpet _) σ (park h n σ) (parade h n) ∧ Sym (parade h n) ∧ Cohort (parade h n):=
 ⟨Held.sum _ _ _ (fun _ _=>price_nn ..) (fun _ _=> (trace_bill ..).1), show Sym (parade h n) from fun r=>funext fun i=>by
    unfold parade woven; simp only [Finset.sum_apply,trace]; simp_rw [← show ∀ (f:Flake n (Market (Head P G))), woven (bleach f) r i=bleach f (i ∘ ⇑r) from fun f=>rfl, symmetric _ r], Cohort.sum _ _ (fun _ _=> (trace_bill (σ:=0) n _ _).2.2)⟩

def fair (S:StepData c f)(t:S.Choices) :Still (Epic S.patch G c):=∑ i:Axis, ∑ x:Site c,ask S t i x
lemma Pace.metal {I J:Type}[Fintype I](s:Finset J)(F:J→Still I)(h:∀ j∈s,Pace (F j)):Pace (s.sum F):=by simpa only [← Finset.sum_apply] using (ContDiffAt.sum (s:=s) (f:=F) h) -- parameter

lemma fair_pace (h:S.patch.Branches S.kernel G)(t:S.Choices): Pace (fair (G:=G) S t):= Pace.metal univ _ fun _ _=>Pace.metal _ _ fun _ _=>ask_pace h t _ _

variable {n:ℕ}

-- general addition bill to use here + Haar. promote to Tack/Plain
lemma flow {I:Type}{c:Side}{ι:Type}(o:Fin n)(s:Finset ι)(F:ι→Flake n (Market I))(p:ι→ℝ)(σ:ℝ)(hh:0≤σ)(ht:∀ i∈s,Held (carpet _) σ (p i) (F i)):
    pour (P:=c) (s.sum F) o=s.sum fun i=>pour (F i) o:=by
 ext v :1;rw [pour_at];simp_rw [Finset.sum_apply];rw [Summable.tsum_finsetSum]
 · simp_rw [pour_at]
 intro i hi; apply Summable.of_norm;exact ((cell_sum (ht i hi) hh o (reach (v o))).comp_injective (Subtype.val_injective (p:=fun x=>x∈ lantern o v))).congr (by intro x; rw [comp_apply,if_pos x.property.1,Real.norm_eq_abs])

lemma accord (h:S.patch.Branches S.kernel G)(t:S.Choices)(i:Axis)(q:Site c): tap n (flask (ask (G:=G) S t i q))=MvPolynomial.rename (fun j=>(wrap _ (slink _ i j).1+q,(slink _ i j (G:=G)).2)) (tap n (flask (mold _ _ G (guard h).tag i))):=by
 let W:=AnyHead S.patch G
 let m (j:W):Epic S.patch G c:=(wrap _ (slink _ i j).1+q,(slink _ i j).2)
 let v := glance q (slink S.patch i (G:=G)) -- invalid binder
 let f:Still W:=mold S.patch S.kernel G (guard h).tag i
 have hR:Camera.roll v 0=0:=rfl
 rw [flask_same (ask_real h t i q),flask_comp (glance_pace q (slink _ i (G:=G))) hR (mold_pace h _ i)]
 have ht:rescaleFields v = fun i=>rod (m i):=by
   funext j; unfold rescaleFields v; rw [show glance q (slink S.patch i (G:=G)) j = fun x:Cellar (Epic S.patch G c)=>x (m j) from rfl, Camera.lamp];ext e:1;change tap _ _=tap _ _;rw [look,hopper]
 change tap n (spool (Room.lug (rescaleFields v)) _)=_
 rw [ht];change tap n (spool (Room.lug (fun i=>rod (m i))) (flask f))=MvPolynomial.rename m _
 have he(p:Inn W):Room.lug (fun i=>rod (m i)) p=liftInn (MvPolynomial.rename m p):=by
   induction p using MvPolynomial.induction_on with
   | C b=>unfold Room.lug;rw [MvPolynomial.aeval_C,MvPolynomial.rename_C,PowerSeries.algebraMap_apply];rfl
   | add _ _ ha hb=>simp only [map_add,ha,hb]
   | mul_X p j hp=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp,MvPolynomial.rename_X,Room.lug,MvPolynomial.aeval_X]
 rw [Room.ships]; simp_rw [he]; rw [Finset.sum_eq_single n (fun b hb hbn=> by rw [tap,PowerSeries.coeff_C,if_neg (by simp only [mem_range] at hb;omega)]) (by simp)]; simp [tap]; rfl

open MvPolynomial in
set_option maxHeartbeats 450000 in
theorem parade_read (h:S.patch.Branches S.kernel G)(t:S.Choices)(o:Fin n):
  parley (pour (P:=c) (parade h n) o)=tap n (flask (fair S t (G:=G))):=by
 rw [parade,flow _ _ _ (fun i=>price _ 1 _ _) 1 (by norm_num) (by intros;exact (trace_bill ..).1),parley_sum,fair,slurry _ _ (fun i hi=>show Pace _ from Pace.metal _ _ fun _ _=>ask_pace h ..)]
 unfold tap;rw [map_sum]
 apply Finset.sum_congr rfl; intro i _;rw [slurry _ _ (fun j _=>ask_pace h t i j),map_sum]
 apply MvPolynomial.funext;intro w;rw [map_sum,picture]
 apply Finset.sum_congr rfl;intro x _; rw [←show ∀(p:Port (Epic S.patch G c)), tap n p=PowerSeries.coeff n p from fun _=>rfl,accord h,eval_rename];rfl
end YM.RG08.Tack
