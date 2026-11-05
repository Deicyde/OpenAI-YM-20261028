import YM.MergeProof.Flavor
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}{B:SectionData F}
    {R:Rep G n}{P:BudgetPoint}(m:Motion) (x:Site n)(U:Config G n)
def stepUp (p:Config G n→ℂ)(U:Config G n):=Motion.scalar m (p (pull m.1 x U))
def sky (m:Motion) (x:Site n): Equiv.Perm (Support n):=(turnSites m.1 x).finsetCongr
lemma shading (p): sky m x p=p.image (turnSites m.1 x):=by simp [sky,Finset.map_eq_image]
def puff (m:Motion) (x:Site n): Equiv.Perm (Box n):=Equiv.prodCongr (sky m x) (sky m x)
def upwards (p:Response G n):Response G n:= fun i=> stepUp m x (p ((sky m x).symm i))
def floatUp (f:Box n→Config G n→ℂ):Box n→Config G n→ℂ:= fun i=>stepUp m x (f ((puff m x).symm i))
lemma scalar_z : Motion.scalar m 0=0:=by unfold Motion.scalar;split <;> simp
variable (π : R.activities.Moves m.1 x)
lemma location (p:ℕ): barcode R.activities (π.kp p)= puff m x (barcode R.activities p):=by
  unfold puff barcode; change (_,_)=(sky m x _,sky m x _);simp_rw [shading]; exact Prod.ext (π.forced_support _) (π.forced_inventory _)
lemma roam {f f':ℕ→Config G n→ℂ}(h:∀ i U,f' (π.kp i) U = stepUp m x (f i) U): profile R.activities f'= floatUp m x (profile R.activities f):=by
  funext p U; obtain ⟨q,rfl⟩:= (puff m x).surjective p; let P:= R.activities
  rw [profile,expand_eq]; rw [← π.kp.tsum_eq]; unfold floatUp stepUp; rw [(puff m x).symm_apply_apply];rw [profile,expand_eq,Motion.scalar_tsum]; refine tsum_congr fun i=> ?_
  simp only [location m x π,Equiv.apply_eq_iff_eq,h];split <;> simp [stepUp,scalar_z m]
lemma foyer (u:Coefficient F n): profile R.activities (audition π u).forced=floatUp m x (profile R.activities u.forced):=by
  apply roam m x π; intro i U; unfold audition stepUp Motion.scalar; split;next h=> simp only [barAll,forced_reorient,Pi.star_apply,Function.comp_apply]
  next=>rw [forced_reorient]; rfl
lemma rise {f:Response G n}{t:ℝ}(h: Attainment P o f t): Attainment P (affine m.1 x o) (upwards m x f) t:=by
   let r:= sky m x; obtain ⟨e,hH,hq⟩:= h.toll; let f':= upwards m x f
   have he p: f' (r p)=stepUp m x (f p):= by unfold f' upwards;dsimp only [r]; rw [ Equiv.symm_apply_apply] -- rwa
   have hC: Measurable (Motion.scalar m):=by unfold Motion.scalar; split_ifs; exact continuous_star.measurable; exact measurable_id
   refine ⟨fun i=> ?_,fun i hi=> ?_,fun i=> e (r.symm i),Local.sumBudget_pass r.toEmbedding _ ?_ (fun i hi=> (hi (r.surjective i)).elim),fun i=> ⟨(hq _).1,fun U=> (Motion.norm_scalar ..).trans_le ((hq _).2 _)⟩⟩
   · obtain ⟨p,rfl⟩:= r.surjective i; let j:= h.shaped p
     rw [show upwards m x f (r p)=_ from he p]; have hp:r p=p.image (turnSites m.1 x):= shading ..; rw [hp]
     exact ⟨fun U V hX ht=> congr_arg (Motion.scalar m) (uses_pull j.sites m.1 x U V hX ht),fun g U=>congr_arg (Motion.scalar m) (invariant_pull j.symmetry m.1 x g U),hC.comp (j.borel.comp (continuous_pull ..).measurable),fun U hU=>by unfold stepUp; rw [j.healthy_zero _ ((healthy_pull ..).mp hU),scalar_z]⟩
   · obtain ⟨p,rfl⟩:= r.surjective i; rw [show r p=_ from shading ..]
     exact Finset.mem_image_of_mem (turnSites m.1 x) (h.marked _ (fun hz=> hi (by change f' _= _; rw [he,hz]; exact funext fun _=> scalar_z m)))
   simp_rw [Equiv.coe_toEmbedding,r.symm_apply_apply]; simpa only [r,reservedMass,shading,cover_map _ (turn_sep m.1 x)] using! hH
open Push
local notation "Q" => R.activities
lemma meet_sky (p q: Support n): Disjoint (sky m x p) (sky m x q)↔ Disjoint p q :=by simp only [shading]; exact Finset.disjoint_image (turnSites m.1 x).injective
lemma bloc (q: Finset ℕ)(f:ℕ→Support n)(h:∀ i,f (π.kp i)= sky m x (f i)): (q.map π.kp.toEmbedding).biUnion f= sky m x (q.biUnion f):=by
   rw [Finset.map_eq_image,Finset.image_biUnion]; change (q.biUnion fun a=> f (π.kp a))=_; simp_rw [h,shading, Finset.biUnion_image]
lemma packed (i:Support n)(q:Finset ℕ) : Packs (Q) (sky m x i) (q.map π.kp.toEmbedding) ↔ Packs (Q) i q:=by
   have hp(k): Local.patch (Q) (π.kp k)= sky m x (Local.patch (Q) k):= congr_arg Prod.fst (location m x π k)
   have hf: Local.Separate (Q) (q.map π.kp.toEmbedding)↔ Local.Separate (Q) q:=by
      unfold Local.Separate Set.PairwiseDisjoint Function.onFun Set.Pairwise -- names
      simp only [Finset.mem_coe, Finset.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,Equiv.toEmbedding_apply,ne_eq,Equiv.apply_eq_iff_eq,hp,meet_sky]
   have hh:(∀ j∈ q.map π.kp.toEmbedding, ¬Disjoint (sky m x i) (Local.patch (Q) j))↔ ∀ j ∈q,¬ Disjoint i (Local.patch (Q) j):=by
      simp only [Finset.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,Equiv.toEmbedding_apply,hp,meet_sky]
   exact ⟨fun h=>⟨Finset.map_nonempty.mp h.1,hf.mp h.2,hh.mp h.3⟩,fun h=>⟨Finset.map_nonempty.mpr h.1,hf.mpr h.2,hh.mpr h.3⟩⟩
lemma boxturn (i:Support n)(q:Finset ℕ): fusionBox Q (sky m x i) (q.map π.kp.toEmbedding)= puff m x (fusionBox Q i q):=by
   refine Prod.ext ?_ (bloc m x π q _ (fun j=> congr_arg Prod.snd (location m x π j)))
   unfold fusionBox; change _ ∪ _=sky m x (i ∪ _)
   rw [bloc m x π q (Local.patch Q) (fun j=> congr_arg Prod.fst (location m x π j))]; simp only [shading,Finset.image_union]
lemma swept (t:ℝ)(i:Support n)(b:Finset ℕ)(p:Box n): grasp (Q) t (sky m x i) (b.map π.kp.toEmbedding) (puff m x p) U = Motion.scalar m (grasp Q t i b p (pull m.1 x U)):=by
   have hx : (puff m x p).1 ∩ flags t U=(puff m x p).2↔ p.1∩flags t (pull m.1 x U)=p.2:=by
      change sky m x _ ∩ _= sky m x _ ↔ _; nth_rw 1 [← Work.H03.flags_send m.1 x t U] -- order
      simp_rw [shading]; exact (show (p.fst.image (turnSites m.1 x)) ∩ _= _↔ _ from by rw [show affine m.1 x=⇑(turnSites m.1 x) from rfl, ← Finset.image_inter _ _ (turnSites m.1 x).injective]; exact (Finset.image_injective (turnSites m.1 x).injective).eq_iff)
   simp_rw [grasp,packed m x π,boxturn m x π, Equiv.apply_eq_iff_eq,hx]; split_ifs
   · unfold Motion.scalar;split_ifs <;>simp [π.valuesK,star_prod]
   rw [scalar_z]
include π
lemma hooked (t:ℝ)(p:Response G n): hook Q t (upwards m x p)= floatUp m x (hook Q t p):=by
   funext i U; obtain ⟨i,rfl⟩:= (puff m x).surjective i
   unfold hook floatUp upwards -- typo
   rw [(puff m x).symm_apply_apply,← Equiv.sum_comp (sky m x)] -- control
   unfold stepUp; have hq (V:Support n→ℂ): Motion.scalar m (∑ p,V p)=∑ p,Motion.scalar m (V p):=by unfold Motion.scalar; split_ifs; exact star_sum ..;rfl
   rw [hq]; refine Finset.sum_congr rfl fun p _=>?_
   simp only [Equiv.symm_apply_apply,Motion.scalar_mul]; rw [portion,portion,Motion.scalar_tsum]; congr 1
   nth_rw 1 [← π.kp.finsetCongr.tsum_eq]; exact tsum_congr fun j=>swept m x U π _ p j i
end YM.MergeProof
