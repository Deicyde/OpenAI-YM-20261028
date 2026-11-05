import YM.FullVolume.Reel.Split
import YM.FullVolume.Nectar.Award
/-!
 # shared assets. finite.L.Further.Top Rotations and closing charts across TIME.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint.Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof Marker Push Extra.Histories
variable {I J X E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F]
variable {q t v s a:ℝ}{w:I→ℝ}{f g:sun→ I→ X→E}
variable [Fintype I][cJ:Fintype J]
-- finite now. charge in abstract charts Glacial. LP helpers; no lowering per recursion. positivity from Feel • supports anchors.True.Neur.
structure Treasure (w:I→ℝ) (F:sun→ I→X→E) (t:ℝ): Prop where
    coins : ∃ a:I→ℝ,∑ i,w i*a i≤ t∧∀ i,Feel (fun s=> F s i) (a i)
def lattice (w:I→ℝ)(f:I→X→E): I→ X→E:=fun i=> w i • f i
local notation "W"=> Glacial I E X
def haul (w:I→ℝ)(f:I→X→E):Glacial I E X:= Glacial.fold (Glacier.castle (lattice w f))
namespace Treasure
variable (hp:Treasure w f v)
omit cJ
include hp
lemma addsP (hv:Treasure w g t) : Treasure w (fun s=>f s+g s) (v+t):=by
    obtain ⟨a,h,hF⟩:=hp.coins; obtain ⟨b,hb,hx⟩:=hv.coins; refine ⟨a+b,?_,fun i=> Feel.united (hF i) (hx i)⟩; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add h hb
lemma grows (h:v≤t):Treasure w f t:=by obtain ⟨a,hA,hx⟩:=hp.coins; exact ⟨a,hA.trans h,hx⟩
lemma positive (hw:∀ i,0≤w i):0≤v:=by obtain ⟨a,hA,hX⟩:=hp.coins; exact (sum_nonneg fun i _=>mul_nonneg (hw i) (hX i|>.positives)).trans hA
omit hp
lemma subdued {f:I→X→E}{a:I→ℝ}(h:0≤ a) (hw:∑ i,w i*a i≤v)(hp:∀ i U,‖f i U‖≤a i):Treasure w (fun _=>f) v:=⟨a,hw,fun i=> Feel.staticC (f i) (h i) (hp i)⟩
variable (hw:∀ i,0<w i)
include hp hw
lemma taxes (z:sun) : Glacier.Bagged (lattice w (f z)) ∧ ‖haul w (f z)‖≤ v:=by
    obtain ⟨a,h,hA⟩:= hp.coins; let C₀:=fun i=> w i*a i
    have hc:C₀≥0:=fun i=>mul_nonneg (hw _|>.le) (hA i|>.positives)
    have he(i:I)(U:X):‖lattice w (f z) i U‖ ≤ C₀ i:= (norm_smul (w i) (f z i U)|>.trans_le (by rw [Real.norm_eq_abs,abs_of_pos (hw _)]; exact mul_le_mul_of_nonneg_left (hA i|>.worth z U) (hw _|>.le)))
    refine ⟨fun i=>⟨C₀ i,hc i,he i⟩,(Glacier.rent hc he).trans h⟩
lemma salvo : PaidBeam (fun s=> haul w (f s)) v:=by
   obtain ⟨u,hu,hx⟩:=hp.coins; let a(i):=w i*u i; let F(s):=lattice w (f s)
   have hr(i): Feel (fun s=>F s i) (a i):=by
       have ht:= (hx i).scales (w i); rw [abs_of_pos (hw _)] at ht; exact ht
   obtain ⟨b,hb,h⟩:= Feel.arrays F hr;
   apply PaidBeam.larger _ hu; apply h.stamp; intro s; let p:= f s
   exact Glacier.equal (f:=Glacier.castle (F s)) (g:=(b s:Glacier I E X)) (fun i U=>(Glacier.unity _ (hp.taxes hw s).1 i U).trans (hb i s U).symm)
omit hp
lemma pay (hr:PaidBeam (fun s=> haul w (f s)) v)(h:∀ i,Glacier.Bagged (lattice w (f i))): Treasure w f v:=by
    let F(s:sun):=lattice w (f s)
    obtain ⟨a,ha,hA⟩:= Feel.factored F (fun s=>haul w (f s)) hr (fun i y u=>Glacier.unity _ (h y) _ _)
    let v' i:= (w i)⁻¹ *a i; have he(i):w i*v' i=a i:= mul_inv_cancel_left₀ (hw i).ne' _
    refine ⟨v',?_,fun i=>?_⟩; simp_rw [he]; exact ha
    have hh:= (hA i).scales (w i)⁻¹; rw [abs_of_pos (inv_pos.mpr (hw i))] at hh; apply Eq.mp (congr_arg (fun f' =>Feel f' (v' i)) (funext fun s=> funext fun z=>?_)) hh; exact inv_smul_smul₀ (hw i).ne' _
omit hw
lemma hoisted {f g:I→X→E}(h:Glacier.Bagged (lattice w f))(hz:Glacier.Bagged (lattice w g)) (hp:Glacier.Bagged (lattice w (f-g))):haul w (f-g)=haul w f-haul w g:=by
   apply Glacier.equal; intro i v; let V(h:I→ X→E):= Glacier.castle (lattice w h); change Glacier.seesG E i v (V (f-g))= Glacier.seesG E i v (V f- V g); rw [map_sub]; unfold V;simp_rw [Glacier.unity _ h,Glacier.unity _ hz, Glacier.unity _ hp]; exact smul_sub ..
lemma foraged {f:sun→ℂ}(h:PaidBeam f v): Feel (fun i=> fun _:X=> f i) v:=by
    let g(s:ℂ): Tint ℂ X:=Tint.wear ⟨fun _=>s,memℓp_infty ⟨‖s‖, Set.forall_mem_range.mpr fun _=> le_rfl⟩⟩
    have he : ∀ x y,g (x-y)=g x-g y:=fun x y=> Tint.liftEqual fun _=> rfl
    have hp (x): ‖g x‖≤1*‖x‖:=by rw [one_mul]; exact (lp.norm_le_of_forall_le (f:=Tint.cast (g x)) (norm_nonneg x) (fun _=>le_rfl))
    have hv:= PaidBeam.transit g he zero_le_one hp f h; rw [one_mul] at hv; exact ⟨fun i=> g (f i),fun _ _=> rfl,hv⟩
lemma coal {f:sun→I→X→ℂ}(h:Treasure w f v){g:sun→ℂ}(hp:PaidBeam g t): Treasure w (fun i=> g i • f i) (t*v):=by
    obtain ⟨a,ha,hA⟩:=h.coins; refine ⟨fun i=>t*a i,?_ ,fun i=>Feel.times (foraged (X:=X) hp) (hA i)⟩
    simp_rw [mul_left_comm _ t,← mul_sum]; exact mul_le_mul_of_nonneg_left ha hp.price
lemma silence : Treasure w (fun (_:sun) (_:I) (_:X)=> (0:E)) 0:= by
   refine ⟨0,?_,fun u=> ?_⟩; simp
   exact Feel.staticC (fun _ : X=> 0) le_rfl (fun _=>norm_zero.le)
include cJ
lemma gang (p:J→ sun→ I→ X→E)(s:Finset J){b:J→ℝ}(h:∀ i∈ s,Treasure w (p i) (b i)):Treasure w (fun t=> ∑ i∈s,p i t) (∑ i∈s,b i):=by
   classical
   induction s using Finset.induction_on with
   | empty=> simp only [sum_empty]; exact silence
   | insert i r hi ht=> simp_rw [sum_insert hi]; exact addsP (h i (mem_insert_self ..)) (ht fun i hi=>h i (mem_insert_of_mem hi))
include hp
lemma shows (e:I≃J){u:J→ℝ}(hu:∀ i:I,u (e i)=w i)(T:E→L[ℝ] F)(g:X→X)(he:∀ v,‖T v‖ ≤ ‖v‖) (x:sun→ J→ X→ F) (h :∀ t i U, x t (e i) U=T (f t i (g U))): Treasure u x v:=by
    obtain ⟨a,hA,hp⟩:=hp.coins; refine ⟨(a∘ e.symm),?_,fun j=>?_⟩; rw [← Equiv.sum_comp e]; simp only [hu,Function.comp_apply, e.symm_apply_apply];exact hA
    obtain ⟨i,rfl⟩:= e.surjective j; have ht:=Feel.transit T g (hp i) (fun z=>by rw [one_mul]; exact he z) zero_le_one; simp_rw [Function.comp_apply,e.symm_apply_apply]; rw [one_mul] at ht; change Feel (fun t x₀=> _) (a i); simp_rw [h]; exact ht
end Treasure
section Motion
open Extra.Histories.Motion Lattice Wilson Push.Local
variable {G:Gauge}{n:Side}{R:Rep G n}{P:BudgetPoint}
def LensC (m:Motion):ℂ→L[ℝ] ℂ:=if m.2 then (starL' ℝ (A:=ℂ)).toContinuousLinearMap else ContinuousLinearMap.id ℝ ℂ
lemma lens (m:Motion)(x): LensC m x= scalar m x:=by unfold LensC scalar; split<;>rfl
lemma lensN (m:Motion)(x): ‖LensC m x‖ ≤ ‖x‖:=by rw [lens]; exact (Motion.norm_scalar ..).le
omit [Fintype I][Fintype J] in
lemma Treasure.spin {ψ:sun→ Response G n}(h:Treasure (fun i=> Real.exp (a*coverNumber P.B i)) ψ v)(m:Motion)(x:Site n):Treasure (fun i=>Real.exp (a*coverNumber P.B i)) (fun i=>upwards m x (ψ i)) v:=by
    let y:=sky m x; apply h.shows y (fun i=>?_) (LensC m) (pull m.1 x) (lensN m) _ (fun i j U=> ?_);
    · unfold y; simp_rw [shading,cover_map _ (turn_sep m.1 x)]
    unfold upwards y; rw [(sky m x).symm_apply_apply,lens]; rfl
open PhysicalNext.Repeat.Lotus MergeProof.Matric
-- Wing carries equivalence over subdomains. basis budgets migrated.
variable {u v':Set Wing}
omit [Fintype I][Fintype J] in
lemma Treasure.turning (f:sun→ Essence G n)(m:Motion)(x:Site n)(K:R.activities.Moves m.1 x) [Fintype (u:Set Wing)] [Fintype (v':Set Wing)](hc:v'=(Wing.labelRoute K) '' u)(h: Treasure (fun i:↥u=>Real.exp (a*coverNumber R.p.B (i.val.support R))) (fun s=> f s ∘ Subtype.val) t):
     Treasure (fun i:↥v'=>Real.exp (a*coverNumber R.p.B (i.val.support R))) (fun s:sun=> dials m x (travelW m x K) (f s)∘ Subtype.val) t:=by
    let e:= travelW m x K; have he(i): i∈u↔e i∈v':=by
        rw [hc]; refine ⟨fun h=> ⟨_,h,rfl⟩,fun ⟨i,hi,hp⟩=> ?_⟩; exact e.injective hp ▸ hi
    let V:= Equiv.subtypeEquiv e he
    refine h.shows V (fun i=>?_) (LensC m) (pull m.1 x) (lensN m) _ (fun s i U=> ?_)
    · change Real.exp (_*coverNumber _ ((Wing.labelRoute K i.val).support R)) = _; rw [Wing.supRoute K, show affine m.1 x= turnSites m.1 x from rfl,cover_map _ (turn_sep m.1 x)] -- ↑ co
    change stepUp m x ((f s) (e.symm (e _))) U=_; rw [e.symm_apply_apply,lens]; rfl
-- when union supports bigger.Y flag close.Trimming true if none.P Ingredient.
end Motion
end YM.FullVolume.Nectar
