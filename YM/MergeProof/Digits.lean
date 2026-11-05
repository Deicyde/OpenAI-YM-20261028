import YM.MergeProof.SwitchCost
/-! # Restrictions to absence of one marker. Measurability & coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Switch
open Function Finset Filter MeasureTheory
open scoped Topology BigOperators Classical
variable {ι U A V : Type}[Fintype ι] {b : ℝ}

lemma vane {x:ℝ} (h:0<x): ∃ f: Score ι ≃ₗ[ℝ] Score ι, f.toFun=value x:=by
  let F : Score ι→ₗ[ℝ] Score ι:={
    toFun:=value x
    map_add' := fun p q=> by ext i; simp [value,mul_add,sum_add_distrib]
    map_smul':= fun r p=> by ext i; simp [value,Finset.mul_sum,mul_left_comm] }
  exact ⟨LinearEquiv.ofBijective F ⟨entire h,(LinearMap.injective_iff_surjective.mp (show Injective F from entire h))⟩,rfl⟩
lemma decodes {X : Ways ι} (x:ℝ)(hp:0<x): value x (decode X x)= X x:= by
  obtain ⟨F,h⟩:=vane (ι:=ι) hp; exact rightInverse_invFun (f:=value x) (show Surjective (value (ι:=ι) x) from h ▸ F.surjective) (X x) -- edit
omit [Fintype ι] in
lemma subtract (r : ℝ) (g : Score ι) {x : ι} {p : Finset ι}(_hp:x∈p):
    value r g p-value r g (p.erase x) = ∑ i∈p.powerset.filter (fun i=>x∈i), r^i.card*g i:=by
  unfold value; rw [sub_eq_iff_eq_add]; nth_rw 1 [show p.powerset=p.powerset.filter (fun i=>x∈i) ∪ (p.erase x).powerset from ?_]
  · exact sum_union (Finset.disjoint_left.mpr fun i hi hu=> Finset.notMem_erase _ _ (mem_powerset.mp hu ((mem_filter.mp hi).2)))
  ext u; constructor
  · intro h; by_cases hh:x∈u; exact mem_union_left _ (mem_filter.mpr ⟨h,hh⟩); exact mem_union_right _ (mem_powerset.mpr fun i hi=> mem_erase.mpr ⟨fun h=>hh (h ▸ hi), mem_powerset.mp h hi⟩)
  intro h; rcases mem_union.mp h with hx|hx; exact (mem_filter.mp hx).1; exact mem_powerset.mpr ((mem_powerset.mp hx).trans (erase_subset ..))

omit [Fintype ι] in
lemma jet_erase {f g: Ways ι} {i:ι} (h:Models f g)(ht:∀ x∈ Set.Icc (0:ℝ) 1,∀ p,f x p=f x (p.erase i))(p:Finset ι)(hp:i∈p): jet f p=0:= by
  rw [h.exact]; suffices H:∀ᶠ x in 𝓝[>] (0:ℝ), (fun x=>g x p) x=0 by exact tendsto_nhds_unique_of_eventuallyEq (h.converge p) tendsto_const_nhds H
  refine approached.mono fun x hx=>?_ ; have hv : value x (g x)= f x:= h.current x ⟨hx.1.le,hx.2⟩
  change g x p=0; induction p using Finset.strongInductionOn with
  | _ p ih=>
    have he:(∑ j∈p.powerset.filter (fun j=> i∈j), x^j.card*g x j)=0:=by rw [← Switch.subtract _ _ hp,hv]; exact sub_eq_zero.mpr (ht x ⟨hx.1.le,hx.2⟩ p)
    rw [sum_eq_single p] at he; exact (mul_eq_zero.mp he).resolve_left (pow_pos hx.1 _|>.ne')
    · intro b hb hn; obtain ⟨h,hp⟩:= mem_filter.mp hb; rw [ih b (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp h,hn⟩) hp,mul_zero]
    intro hz; exact False.elim (hz (mem_filter.mpr ⟨mem_powerset.mpr (Finset.Subset.refl _),hp⟩))

lemma Paid.jet_meas [MeasurableSpace U] {f: U→Ways ι} (hp: Paid f b) (h:∀ x∈Set.Icc (0:ℝ) 1,∀ i, Measurable (fun u=> f u x i))(i:Finset ι) : Measurable (fun u=> jet (f u) i):= by
   let g (x:ℝ):U→ℝ:= if x∈ Set.Ioc (0:ℝ) 1 then fun u=> decode (f u) x i else fun _=> 0
   have hg(x):Measurable (g x):= by
     unfold g;split; next hv=>
       obtain ⟨F,hF⟩:=vane (ι:=ι) hv.1
       have hx u:decode (f u) x= F.symm (f u x) := by apply F.injective; change F.toFun _=_; rw [hF,decodes x hv.1]; exact (F.apply_symm_apply _).symm
       simp_rw [hx]
       exact (measurable_pi_apply i).comp (F.symm.continuous_of_finiteDimensional.measurable.comp (measurable_pi_iff.mpr fun j=> h _ ⟨hv.1.le,hv.2⟩ j))
     next hz=> exact measurable_const
   refine measurable_of_tendsto_metrizable' (g:=fun u=>jet (f u) i) (𝓝[>] (0:ℝ)) hg (tendsto_pi_nhds.mpr ?_); intro u
   obtain ⟨p,H⟩:=hp.works u; rw [H.exact]; refine (H.converge i).congr' (approached.mono (fun x hx=> ?_))
   change p x i=g x u; unfold g; rw [if_pos (show x∈Set.Ioc 0 1 from hx)]; rw [decode,← H.current x ⟨hx.1.le,hx.2⟩, leftInverse_invFun (entire hx.1)]
end YM.Merge.Switch
