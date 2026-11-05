import YM.MergeProof.North.Ally
import YM.MergeProof.Wreath


set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
open Equiv
variable {s:Signed}{b:Site c}
variable (π:R.activities.Moves s (S.ratio.embed b))(B:Equiv.Perm ι) (U:Config G c) (r:ι→ℝ)
lemma booklets (t:ℝ)(i: Molecule S)(z:Finset ι)(he:∀ i∈z,M (B i)=(M i).route π ∧ r (B i)=r i):
     color M Y χ U (ways r t (z.image B)) (Turn.caravan R π i)= color M Y χ (pull s b U) (ways r t z) i:=by
    let A:= Tickets (sign M S); let j:= z.image B; let f (z:Finset ι)(i:A):=∏ l∈i.val,ways r t z l
    let g l V (m:Molecule S) (i:A):= f l i * act M Y χ V m i
    have hp (z:Finset ι)(V:Config G c)(i:Molecule S): color M Y χ V (ways r t z) i=∑ u : {s:A//s.val⊆z},g z V i u.val:=by
       change ∑ i:A, _=_; symm; apply Finset.sum_of_injOn Subtype.val (fun _ _ _ _=>Subtype.ext) (fun _ _=> mem_univ _) (fun k _ hk=> ?_) (fun _ _=>rfl)
       by_contra hz; apply hk; refine ⟨⟨k,?_⟩,mem_univ _,rfl⟩; intro l hl; by_contra hn; exact left_ne_zero_of_mul hz (prod_eq_zero hl (show ways r t z l=0 from if_neg hn))
    let W:=Turn.badge R π; have hz i (hi:i∈z): sign M S (B i)=W (sign M S i):=by unfold sign;rw [(he i hi).1]; exact Leaf.cardRoute ..
    have hk (p:Finset ι)(hp:p⊆z) : Draft (sign M S) (p.image B)↔ Draft (sign M S) p:=by
       constructor
       · intro h l hl v hv hx; exact B.injective (h (mem_image_of_mem _ hl) (mem_image_of_mem _ hv) ((hz l (hp hl)).trans ((congr_arg W hx).trans (hz v (hp hv)).symm)))
       intro h l hl u hu hx; obtain ⟨i,hi,rfl⟩:=mem_image.mp hl; obtain ⟨b,hb,rfl⟩:=mem_image.mp hu; rw [hz i (hp hi),hz b (hp hb)] at hx; exact congr_arg B (h hi hb (W.injective hx))
    let e:{s:A//s.val⊆z}→{s:A//s.val⊆j}:=fun s=> ⟨⟨s.val.val.image B,(hk _ s.property).2 s.val.property⟩,image_subset_image s.property⟩
    have hE: Bijective e:=by
       refine ⟨fun i j he=>Subtype.ext (Subtype.ext (Finset.image_injective B.injective (congr_arg (fun i=>i.val.val) he))),fun s=>?_⟩
       let p:= s.val.val.image B.symm; have hh:p.image B=s.val.val:=by unfold p; rw [image_image];simp
       have hP: p⊆z:= (Finset.image_subset_image_iff B.injective).mp (hh ▸ s.property)
       exact ⟨⟨⟨p,(hk _ hP).1 (hh ▸ s.val.property)⟩,hP⟩,Subtype.ext (Subtype.ext hh)⟩
    rw [hp,hp,← Equiv.sum_comp (Equiv.ofBijective e hE)]
    refine sum_congr rfl fun v _=>?_ ; unfold g f; apply congr_arg₂ (·*·)
    · change ∏ i∈v.val.val.image B,_=_; rw [prod_image B.injective.injOn]; refine prod_congr rfl fun i hi=>?_ ; unfold ways; rw [if_pos (v.property hi),if_pos (mem_image_of_mem _ (v.property hi)),(he i (v.property hi)).2]
    let H:= team M v.val
    have hv: team M (e v).val=H.route π:=by
       have ht (i j:Lotus.Team R)(h:i.own=j.own):i=j:=by cases i;cases j;congr
       apply ht; change (v.val.val.image B).image M=(v.val.val.image M).image _;rw [image_image,image_image]; exact image_congr (fun i hi=> (he i (v.property hi)).1)
    change (team M (e v).val).lotus ..= _; rw [hv]; exact (H.sails π Y χ U i).symm
end YM.Merge.Palette
