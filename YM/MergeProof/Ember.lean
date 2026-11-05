import YM.MergeProof.Flax
import YM.MergeProof.Heap

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories
variable [Fintype ι] [Fintype V](q:ι→ Hat B R)(U : Config G f)
-- sum expansions using logs including empty. more comps
local notation "ι'"=> Mound q
lemma faithful (k:Wing): rush q k U=∑ i∈ atKey q k,amount (q i) U:=by rw [rush,← Finset.sum_filter]; rfl
set_option maxHeartbeats 400000 in
lemma rolled_up (k:Wing): Poly.pass (rush q k U)=1+rush q k U+∑ j:Rock q k,amount (rise q k j.val) U:=by
   rw [faithful]; let X:= atKey q k; let l(i):= amount (q i) U
   have hv(i):l i=Poly.send (hatMode q i) ((↑((q i).M.ingredient U):ℂ)*(q i).charge):= varnish ..
   let L(p:Finset ι):= ∏ i∈p,l i
   have ht : Poly.pass (∑ i∈ X,l i)=∑ i∈ X.powerset,L i:=by unfold L; rw [← Finset.prod_one_add]; simp_rw [hv]; exact Extra.Trajectories.pass_sum X _ (fun i _=> (q i).shiny) _
   change Poly.pass (∑ i∈X,l i)=1+_+_
   rw [ht,← add_sum_erase _ _ (empty_mem_powerset X),show L ∅=1 from Finset.prod_empty,add_assoc]; refine congr_arg (1+·) ?_
   let d:= X.image (fun i=>({i}:Finset ι)); have hy:d⊆ X.powerset.erase ∅:= by intro i he; obtain ⟨i,hi,rfl⟩:= mem_image.mp he; exact mem_erase.mpr ⟨by simp,by simpa using hi⟩
   let A:= X.powerset.erase ∅; let S:=A\d
   have hS(i:Finset ι):i∈ S↔ i⊆X ∧ 2≤ i.card:=by
      rw [show i∈S↔ i∈ A∧ i∉d from mem_sdiff]; constructor
      · rintro ⟨hp,h⟩; have hs:= mem_erase.mp hp; have hc:= card_pos.mpr (nonempty_iff_ne_empty.mpr hs.1); have ha:= mem_powerset.mp hs.2
        refine ⟨ha,?_⟩; by_contra hx; obtain ⟨j,hj⟩:=card_eq_one.mp (show i.card=1 from by omega); subst i; exact h (mem_image.mpr ⟨j,ha (mem_singleton_self _),rfl⟩)
      rintro ⟨hx,hp⟩; refine ⟨mem_erase.mpr ⟨fun h=> by subst i; simp at hp,mem_powerset.mpr hx⟩,?_⟩
      intro he; obtain ⟨j,_,rfl⟩:= mem_image.mp he; simp at hp
   change ∑ i∈A,L i = _; rw [← show (∑ i∈d,L i)+(∑ i∈S,L i)= ∑ i∈A,L i from (by rw [add_comm]; exact Finset.sum_sdiff hy)] -- sum_sdiff? edit
   refine congr_arg₂ (·+·) ?_ ?_
   · unfold d; rw [Finset.sum_image (fun _ _ _ _ h=> Finset.singleton_inj.mp h)]; exact sum_congr rfl fun i _=> Finset.prod_singleton ..
   simp_rw [flaunt]; symm; let e(i:Rock q k):=i.val.val; let R:=Rock q k
   change ∑ i,L (e i)= _; have hu:Injective e:= Subtype.val_injective.comp Subtype.val_injective; rw [← Finset.sum_image hu.injOn]
   apply Finset.sum_subset ?_ (fun i hi hh=> ?_)
   · intro i hi; obtain ⟨j,_,rfl⟩:= mem_image.mp hi; exact (hS _).2 ⟨j.val.property.2.1,j.property⟩
   by_contra hn; unfold L at hn; simp_rw [hv] at hn
   have ht := fits_of_tagged_prod _ hn; have hk := (hS i).1 hi
   let v:Rock q k := ⟨⟨i,card_pos.mp (show 0 < i.card from by linarith only [hk.2]),hk.1,ht⟩,hk.2⟩; exact hh (mem_image.mpr ⟨v,mem_univ _,rfl⟩)

lemma gold (k:logDeck q): 1+rush (heap q) (.logKey k.val) U=Poly.pass (rush q (.logKey k.val) U):=by
   rw [rolled_up,add_assoc]; congr 1; unfold rush Mound
   rw [Fintype.sum_sum_type]; refine congr_arg₂ (·+·) rfl ?_
   rw [Fintype.sum_sigma, sum_eq_single k]
   · apply sum_congr rfl; intro i _; exact if_pos rfl
   · intro i _ hi; exact sum_eq_zero fun j _=> if_neg fun h=> hi (Subtype.ext (Wing.logKey.inj h))
   simp

def roll (U:Config G f): Poly B:=∑ i∈logDeck q,rush q (.logKey i) U
lemma golden : jets (heap q) U=Poly.pass (roll q U):=by
   unfold jets roll; rw [logs_kept]; let X i:=1+rush (heap q) (.logKey i) U; let f i:= rush q (.logKey i) U
   have he(p:Finset ℕ) (hx:p⊆ logDeck q): ∏ i∈p,X i=Poly.pass (∑ i∈p,f i):=by
      induction p using Finset.induction with
      | empty => simp
      | insert i p hi ih=> rw [sum_insert hi,Finset.prod_insert hi,show X i=Poly.pass (f i) from gold q U ⟨i,hx (mem_insert_self ..)⟩,Extra.Trajectories.pass_add (by unfold f; rw [still]) (by unfold f; simp [Poly.part_sum,still q _ U]),ih ((subset_insert ..).trans hx)]
   exact he _ (Finset.Subset.refl _)
end YM.MergeProof.Menu
