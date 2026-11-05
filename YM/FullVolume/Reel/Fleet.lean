import YM.MergeProof.Cashew
import YM.MergeProof.Decaf
import YM.FullVolume.Nectar.Farey
/-!
# Color chart refinement for Mellin walls

Retain the *actual* leaf itinerary as a wing payroll and the rebate profile it certifies. Need not pick a common indexation of unboundedly many incoming regular or forced summands. Hinge readings and momentum spent on the real contours.Fleet reports essence, always on ALL supports (never quotienting K values). Finiteness later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f: Side}{E:Rep G c}{R:Rep G f}{o:Site f}{p:Site c}
variable {D:GaugeDoor R E}{X:Set Wing}
variable {β: Res G c}{α: Config G f→ℂ}{ζ: Res G f}{v δ:ℂ}{t u:ℝ}
abbrev Essence (G:Gauge)(f:Side):= Wing→ Config G f→ℂ
variable {y: Essence G f}{x: Response G c}
variable {I J:Type}
def deposit (r:I→ℂ)(F:I→Lotus.Leaf R)(U:Config G f)(p:Wing)(i:I):ℂ:=if (F i).turn=p then r i*(F i).ingredient U else 0
def Net (r:I→ℂ)(F:I→Lotus.Leaf R)(Y:Essence G f):Prop:= ∀ i U, HasSum (deposit r F U i) (Y i U)
structure Fleet (R:Rep G f)(E:Rep G c)(D:GaugeDoor R E)(X:Set Wing)(o:Site f)(p:Site c)(v δ:ℂ)(α:Config G f→ℂ)(ζ:Res G f)(β:Res G c)(u v':ℝ)(y: Essence G f)(x:Response G c):Prop where
   buys: ∃ (ι:Type), Countable ι∧ ∃ M s, Odyssey (ι:=ι) X o p v α ζ β δ u v' D M s x∧Net s M y
section prices
variable (r:I→ℂ)(F:I→Lotus.Leaf R)
lemma weightFuse (h:SumBudget (fun i=> ‖r i‖*load (F i)) t): Summable (fun i => ‖r i‖*(F i).weight):=h.2.1.of_nonneg_of_le (fun i=>mul_nonneg (norm_nonneg _) (F i).profit) (fun i=>mul_le_mul_of_nonneg_left (R.p.loMass _ _ (Leaf.profit _)) (norm_nonneg _))
lemma loadFuse (U:Config G f)(j i): ‖deposit r F U j i‖ ≤ ‖r i‖*(F i).weight:=by
    unfold deposit; split
    next=> rw [norm_mul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (Leaf.earn ..) (norm_nonneg _)
    next=> rw [norm_zero]; exact mul_nonneg (norm_nonneg _) (Leaf.profit _)
lemma troop (U:Config G f)(u:ℂ) (j i): u*deposit r F U j i=deposit (u • r) F U j i:=by
    unfold deposit; split_ifs; exact (mul_assoc ..).symm; exact mul_zero _
lemma potF (j:Wing) (h:Net r F y)(hp:Summable fun i=> ‖r i‖*(F i).weight)(U:Config G f): ∑' i:{i // (F i).turn=j},r i.val*( ((F i.val).ingredient U:ℝ):ℂ)= y j U:=by
    rw [←(h j U).tsum_eq]; have he (i:{i // (F i).turn=j}): deposit r F U j i.val=r i.val*(((F i.val).ingredient U:ℝ):ℂ):= if_pos i.2
    exact (tsum_congr (fun i=> (he i).symm)).trans (tsum_subtype_eq_of_support_subset (s:={i| (F i).turn=j}) (f:=deposit r F U j) fun i hi=> of_not_not (fun h=> hi (if_neg (by exact h)))) -- relation iff
lemma Net.flush (hn:Net r F y)(h:SumBudget (fun i=> ‖r i‖*load (F i)) t) (X: Finset Wing):∃ a:Wing→ℝ,0≤ a ∧ (∑ j∈X, R.p.mass (j.support R) (a j)) ≤ t ∧∀ j U, ‖y j U‖ ≤ a j:=by
   let k(i):= ‖r i‖*(F i).weight; let p(i:I):=(F i).turn; let P:=cram p k; have hk i: k i≥0:=mul_nonneg (norm_nonneg _) (F i).profit; have hK:= weightFuse r F h
   have ha(i:Wing):0≤P i:= tsum_nonneg fun j=>hk _
   let u₀(i:I):= ‖r i‖*load (F i)
   have hA i : R.p.mass (i.support R) (P i)=cram p u₀ i:=by
       unfold P cram BudgetPoint.mass; rw [← tsum_mul_left]; refine tsum_congr fun v=>?_; unfold k u₀ load BudgetPoint.mass
       rw [show (F v.val).crest=i.support R from congr_arg (fun j'=>j'.support R) v.property];ring -- p
   refine ⟨P,ha,?_,fun j U=>?_⟩
   · have he:= heavy p h.2.1
     simp_rw [hA]; exact (he.summable.sum_le_tsum _ (fun i _=>tsum_nonneg (fun v=>h.1 _))).trans (he.tsum_eq.trans_le h.2.2)
   let W:={i:I // p i=j}; rw [← potF r F j hn hK U]; let f(i:W):= r i.val*(((F i.val).ingredient U:ℝ):ℂ); have hv:Summable (fun i:W=> k i.val):=hK.comp_injective Subtype.val_injective; have hx(i:W): ‖f i‖≤k i.val:= calc
       _=‖r i.val‖* ‖(F i.val).ingredient U‖:=by unfold f; rw [norm_mul,Complex.norm_real]
       _ ≤ _ :=mul_le_mul_of_nonneg_left (Leaf.earn ..) (norm_nonneg _)
   have H:= hv.of_nonneg_of_le (fun i=>norm_nonneg _) hx; exact (norm_tsum_le_tsum_norm H).trans (H.tsum_le_tsum hx hv)
-- packed route.EQUIV
end prices
def travelW (s: Motion)(b:Site f)(M:R.activities.Moves s.1 b): Wing≃ Wing where
  toFun:= Wing.labelRoute M
  invFun(i):= match i with
    | .logKey j=>.logKey (M.ep.symm j)
    | .gasKey j=>.gasKey (M.kp.symm j)
  left_inv:=fun i=> by cases i <;> simp [Wing.labelRoute]
  right_inv:=fun i=> by cases i <;> simp [Wing.labelRoute]
def dials (s:Motion) (b:Site f) (M:Wing≃Wing) (Y: Essence G f)(i: Wing) := stepUp s b (Y (M.symm i))
namespace Fleet
variable (h:Fleet R E D X o p v δ α ζ β t u y x)
include h
lemma dice (s:ℂ): Fleet R E D X o p v (s*δ) (s•α) (s•ζ) (s•β) (‖s‖*t) (‖s‖*u) (s • y) (s • x):=by
    obtain ⟨I,hI,M,c,h,H⟩:= h.buys
    exact ⟨I,hI,_,_,h.quaver s,fun i U=>((H i U).mul_left s).congr_fun fun j=> (troop c M U s i j).symm⟩
lemma altoP {b s:ℂ}(hx:b=v*s): Fleet R E D X o p 1 (b*δ) (b•α) (b•ζ) (s•β) (‖b‖*t) (‖s‖*u) (b • y) (s • x):=by
   obtain ⟨I,hI,M,c,h,H⟩:= h.buys; have hz:= h.quaver b
   refine ⟨I,hI,M,b • c,⟨hz.member,hz.purchase,stack_of h.cost s,hz.lyric,hz.old,fun j U=>?_⟩,fun i U=> ((H i U).mul_left b).congr_fun fun j=> (troop c M U b i j).symm⟩
   simp only [hook_scale,one_mul,Pi.smul_apply,smul_eq_mul, ← mul_sub,hx]
   exact ((h.grants j U).mul_left s).congr_fun fun i=> by ring
lemma mobile (m:Motion)(b:Site c){S:StepData c f}(hs: SoundDoor S D)(M:R.activities.Moves m.1 (S.ratio.embed b))(hv:scalar m v=v): Fleet R E D ((Wing.labelRoute M) '' X) (affine m.1 (S.ratio.embed b) o) (affine m.1 b p) v (scalar m δ) (stepUp m (S.ratio.embed b) α) (floatUp m (S.ratio.embed b) ζ) (floatUp m b β) t u (dials m (S.ratio.embed b) (travelW m (S.ratio.embed b) M) y) (upwards m b x):=by
    obtain ⟨I,hI,Q,z,h',H⟩:=h.buys; let j:=S.ratio.embed b; refine ⟨I,hI,_,_,Odyssey.dancing m b h' hs M hv,?_ ⟩
    intro i U; let P:=travelW m j M; obtain ⟨i,rfl⟩:=P.surjective i
    let V:=pull m.1 j U; rw [dials,show _=i from P.symm_apply_apply _]; apply (seriesScalar m (H i V)).congr_fun; intro t;
    unfold deposit; rw [show ((Leaf.route M ∘ Q) t).turn=P (Q t).turn from rfl]; by_cases he : (Q t).turn=i
    · rw [if_pos (P.injective.eq_iff.mpr he),if_pos he, scalar_mul,scalar_real]; rfl
    rw [if_neg (fun h=> he (P.injective h)),if_neg he,scalar_z]
lemma loosen {Y:Set Wing}{t' u':ℝ}(he:X ⊆ Y)(ht:t≤t')(hu:u≤u'): Fleet R E D Y o p v δ α ζ β t' u' y x:=by obtain ⟨I,hI,Q,z,h,H⟩:=h.buys; exact ⟨I,hI,Q,z,h.elevate he ht hu,H⟩
lemma prudence : 0≤t∧0≤u ∧ Attainment E.p p x u:=by
   obtain ⟨I,hI,Q,z,h,H⟩:=h.buys
   refine ⟨(tsum_nonneg h.purchase.1).trans h.purchase.2.2,?_,h.cost⟩; obtain ⟨e,h,_⟩:=h.cost.toll; exact (tsum_nonneg h.1).trans h.2.2
lemma darkness (i:Wing)(he:i∉X) : y i=0:=by
   obtain ⟨I,hI,Q,z,h,H⟩:= h.buys; funext U; rw [← (H i U).tsum_eq]; have he i':deposit z Q U i i'=0:= if_neg (show (Q i').turn ≠ i from fun hp=> he (hp ▸ (show _ from (h.member i').2))); simp_rw [he]; exact tsum_zero
omit h
lemma waters : Fleet R E D X o p v δ (fun _=>δ) 0 0 0 0 0 0:=by
   refine ⟨Empty,inferInstance,Empty.elim,fun _=>0,⟨fun i=>i.elim,⟨fun i=>i.elim,Summable.of_finite,by simp⟩,Attainment.blank _,fun _=>by simp,fun _ _=> ?_,fun _ _=> ?_⟩,fun _ _=>?_⟩
   all_goals simp [hook]
open Sigma Extra.Multi
lemma amassed [Countable I] {Q:I→ Config G f→ℂ}{K:I→Res G f}{P:I→Res G c}{t' u':I→ℝ}{δ':I→ℂ}{F:I→ Essence G f}{Y:I→ Response G c}{S:StepData c f} (hS:SoundDoor S D) (hz:∀ i,Fleet R E D X o p v (δ' i) (Q i) (K i) (P i) (t' i) (u' i) (F i) (Y i))(hq:∀ i, HasSum (fun j=> Q j i) (α i))(hk:∀ i W, HasSum (fun j=>K j i W) (ζ i W))(hp:∀ i W,HasSum (fun j=>P j i W) (β i W))(he:HasSum δ' δ)(hT: Summable t')(hU: Summable u'): Fleet R E D X o p v δ α ζ β (∑' i,t' i) (∑' i,u' i) (fun i b=> ∑' j,F j i b) (band Y):=by
    choose T h M s ht hX using fun i=> (hz i).buys
    have h := symbolize D hS ht hq hk hp he ⟨fun i=>(hz i).prudence.1,hT,le_rfl⟩ ⟨fun i=>(hz i).prudence.2.1,hU,le_rfl⟩
    let Z':=Sigma.uncurry M; let f':=Sigma.uncurry s
    refine ⟨Σ i,T i,inferInstance,Z',f',h,?_⟩
    intro i W; let f:=deposit f' Z' W i; have hp : Summable f:= (weightFuse f' Z' h.purchase).of_norm_bounded (loadFuse f' Z' W i) -- edit
    have hh(i':I): ∑' j: T i',f ⟨i',j⟩= F i' i W:= (hX i' i W).tsum_eq; have hb: ∑' i', f i'=∑' j,F j i W:=by rw [hp.tsum_sigma]; simp_rw [hh]
    change HasSum f _; simp only; rw [← hb]; exact hp.hasSum
end Fleet
end YM.MergeProof.Matric
