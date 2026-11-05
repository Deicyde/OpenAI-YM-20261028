import Mathlib.RingTheory.Nilpotent.Exp
import YM.Extra.SOURCE_HISTORIES.Pencil

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Set
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n:Side} {G:Gauge}{A:Type*}[MeasurableSpace A][Zero A]
-- agree saturated quotient.Analytic. F naturally gauges orbit as support extension. equality cases closed. 
lemma tofu (t:ℝ)(s: Support n)(F:Config G n→A)(hm:Measurable F)(ht:UsesFinal t s F)(hi: GaugeInvariant F): ∃ f : Config G n→A, Measurable f ∧ LocalOn s f ∧ GaugeInvariant f ∧ ∀ U, Healthy t s U → f U=F U:=by
    let p: Set (Config G n):= {x|Healthy t s x}; have hp:IsClosed p:= healthy_closed ..
    letI : CompactSpace p:=isCompact_iff_compactSpace.mp hp.isCompact
    haveI : PolishSpace G.El:=by
       letI : PolishSpace (Matrix (Fin G.repDim) (Fin G.repDim) ℂ):= inferInstanceAs (PolishSpace (Fin G.repDim → Fin G.repDim → ℂ))
       letI : PolishSpace (GaugeU G.n):= isClosed_unitary.polishSpace
       exact G.closed_imageGroup.polishSpace
    haveI : PolishSpace (Config G n):= inferInstance
    haveI : PolishSpace p:=hp.polishSpace
    let r (U:Config G n) :Config G n:=fun e=> if e.1∈s∧e.1+step e.2∈s then U e else 1
    have he U V: Agrees s U V ↔ r U=r V:=by
       constructor
       · intro h; funext e; unfold r;split;next hg=> exact h e hg.1 hg.2
         next=>rfl
       intro h i hv hc; have he:= congr_fun h i; unfold r at he; rw [if_pos (show i.1∈s∧i.1+step i.2∈s from ⟨hv,hc⟩),if_pos ⟨hv,hc⟩] at he; exact he
    have hP U V (hk:r U=r V)(hu:U∈p)(hv:V∈p): F U=F V:= ht U V ((he U V).mpr hk) (Eq.trans (Finset.disjoint_iff_inter_eq_empty.mp hu) (Finset.disjoint_iff_inter_eq_empty.mp hv|>.symm))
    have hG U V (k : Site n→ G.El) (h:r U=r V): r (Lattice.gauge k U)=r (Lattice.gauge k V):=(he ..).mp (fun i hx hv=> by simp only [Lattice.gauge]; rw [(he U V).mpr h i hx hv]) -- Lattice.gauge
    have hg k U: Lattice.gauge k U∈p↔ U∈p:=by unfold p; simp [Healthy] -- Lattice.gauge
    have hr: Continuous r:= by apply continuous_pi;intro i; unfold r;split; exact continuous_apply i; exact continuous_const
    let g: ↥p→Config G n:= r∘Subtype.val
    have hy:Continuous g :=hr.comp continuous_subtype_val
    have hs:IsClosed (Set.range g):= (isCompact_range hy).isClosed
    let v:=extend g (F ∘ Subtype.val) (fun _=> (0:A)); have hx(u: ↥p): v (r u.val)=F u.val:=by -- extend API: apply'?
       unfold v Function.extend;split
       next h=> exact hP h.choose.val u.val h.choose_spec h.choose.property u.property
       next h=>exact (h ⟨u,rfl⟩).elim
    have ha:Measurable v:=by
       have hh:v ∘ g=F ∘ Subtype.val:= funext hx
       intro s h; by_cases hs':0 ∈ s
       · rw [← MeasurableSet.compl_iff]; have ht: v⁻¹'sᶜ⊆Set.range g:= fun U hu=> Classical.byContradiction fun hq=> hu (show v U∈ s from by change extend _ _ _ _∈ _;rw [extend_apply' _ _ _ hq]; exact hs')
         rw [← Set.preimage_compl,← Set.inter_eq_left.mpr ht]; exact (hy.measurable.measurableSet_preimage_iff_inter_range hs.measurableSet).mp (show MeasurableSet ((v∘g)⁻¹' sᶜ) from hh.symm ▸ (hm.comp measurable_subtype_coe) h.compl)
       have ht: v⁻¹'s⊆Set.range g:= fun U hu=> Classical.byContradiction fun hq=> hs' (show (0:A)∈s from Eq.subst (motive:=fun v=> v∈s) (show v U=0 from extend_apply' _ _ _ hq) hu)
       rw [← Set.inter_eq_left.mpr ht]; exact (hy.measurable.measurableSet_preimage_iff_inter_range hs.measurableSet).mp (show MeasurableSet ((v∘g)⁻¹'s) from hh.symm ▸ (hm.comp measurable_subtype_coe) h)
    refine ⟨v∘r,ha.comp hr.measurable,fun U V h=>congr_arg v ((he U V).mp h),?_, fun U h=>hx ⟨U,h⟩⟩
    intro k U; change v _=v _; by_cases hg' : r U∈Set.range g
    · obtain ⟨a',Ha⟩:=hg'; have HV:r a'.val=r U:=Ha
      rw [show r (Lattice.gauge k U)=_ from (hG _ _ k HV).symm,← HV,hx ⟨Lattice.gauge k a', (hg k a').mpr a'.property⟩,hx,hi]
    have hx' : r (Lattice.gauge k U)∉Set.range g:=by
       rintro ⟨a',ha⟩
       apply hg'; let b:= Lattice.gauge k U; have hp : Lattice.gauge (k⁻¹) (Lattice.gauge k U)=U:=by funext i; simp only [Lattice.gauge,Pi.inv_apply]; group
       exact ⟨⟨Lattice.gauge (k⁻¹) a',(hg (k⁻¹) a').mpr a'.property⟩,(hG _ _ _ (show r a'.val=r (Lattice.gauge k U) from ha)).trans (congr_arg r hp)⟩
    unfold v; rw [extend_apply' _ _ _ hx',extend_apply' _ _ _ hg']
end YM.MergeProof
