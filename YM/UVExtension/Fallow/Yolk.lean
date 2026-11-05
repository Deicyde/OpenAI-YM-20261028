import YM.UVExtension.Fallow.Fodder
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth Metric
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels) {d N p:ℕ}
open Extra.Histories Motion Next.Extract Harvest
variable {T: Cuts C d} (Y:Yards C d p T) (K: Extraction.Wcmain C) (h: Slicing C d p)
include H Y K
lemma scanMaps {k:ℕ→ℕ} (hk:Tendsto k atTop atTop)(I:Finset (Shot C.book)) (hI:∀ i∈I,suitable C.S p i.f): ∃ t :Extraction.Sequence, ∃ A:I→ C.label d →L[ℂ] ℂ,∀ i, Tendsto (fun j=> Dash.Shot.scan i.val d (k (t j)) p) atTop (𝓝 (A i)):=by
   apply cover_maps (fun i (j:I)=> Dash.Shot.scan j.val (C:=C) d (k i) p); intro i x; obtain ⟨r,hr⟩:= sustained H K i.val x (hI _ i.property); exact ⟨r,hk.eventually hr⟩
lemma spare (x:C.label d) : Spar (fun i=> x-T i x):=by
   obtain ⟨r,hr⟩:=Y.spends; refine ⟨‖x‖+r*‖x‖,?_⟩; filter_upwards [hr] with i hi; exact (norm_sub_le ..).trans (add_le_add_right (((T i).le_opNorm _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))) _)
lemma household (I:Finset (Shot C.book))(hI:∀ i∈I,suitable C.S p i.f)(t:ℕ→ℕ)(ht:Tendsto t atTop atTop)(A:I→ C.label d→L[ℂ]ℂ)(hA:∀ i,Tendsto (fun j=> Dash.Shot.scan i.val d (t j) p) atTop (𝓝 (A i)))(X: CoordMap C d)(hP:Tendsto (fun n=> T (t n)) atTop (𝓝 X))(U:Submodule ℂ (C.label d))(hu:Module.finrank ℂ U+Harvest.charge G d= Module.finrank ℂ (C.label d))(c:ℝ)(hc:0<c)(hz: ∀ᶠ N in atTop, ∀ x∈U,c*‖x‖ ≤ ∑ i∈I,‖Dash.Shot.scan i d N p x‖) : ∀ x:C.label d,(∀ i,A i x=0) → X x=0 := by
   apply cleft _ U A (by rw [rank_home Y hP,Nat.add_comm]; exact hu) (fun i x hx=>?_) (fun x hx hh=>?_)
   · let v j:= x-T j x
     have hp:Tendsto (fun i=> v (t i)) atTop (𝓝 x):=by simpa only [v,hx,sub_zero] using tendsto_const_nhds (x:=x) |>.sub (Dash.arcing hP (tendsto_const_nhds (x:=x)))
     have he : ∀ᶠ i in atTop,v i∈LinearMap.ker (T i).toLinearMap:= Eventually.of_forall fun i=> by change T i (x-T i x)=0; rw [map_sub,Y.changes,sub_self]
     exact tendsto_nhds_unique (Dash.arcing (hA i) hp) ((Y.nullTest H K (Bleak.physical H p (spare H Y K x)) he i.val (hI i.val i.property)).comp ht) -- param binder hK
   have hv:= tendsto_finsetSum (Finset.univ (α:=I)) fun i _=> (((Dash.arcing (hA i) (tendsto_const_nhds (x:=x)))).norm)
   have hS : c*‖x‖ ≤ ∑ i:I,‖A i x‖:=ge_of_tendsto hv (by
      filter_upwards [ht.eventually hz] with k hk; exact (hk x hx).trans_eq (Finset.sum_attach I _).symm) -- `sum_attach`
   simp only [hh,norm_zero,Finset.sum_const_zero] at hS; by_contra he; exact (mul_pos hc (norm_pos_iff.mpr he)).not_ge hS
-- Output all late N, by contradiction. Unit rank r could zero.
lemma certain {I:Finset (Dash.Shot C.book)}(hI:∀ i∈I,suitable C.S p i.f)(t:Submodule ℂ (C.label d))(ht:Module.finrank ℂ t +Harvest.charge G d=Module.finrank ℂ (C.label d)){c:ℝ}(hc:0 < c)(h:∀ᶠ N in atTop,∀ x∈t,c*‖x‖ ≤ ∑ i∈I, ‖snapshots i d (N,p) x‖) : ∃ q:ℝ,0<q ∧∀ᶠ N in atTop,∀ x:C.label d,T N x=x → q*‖x‖ ≤ ∑ i∈I, ‖snapshots i d (N,p) x‖:=by
   by_contra he
   have hf (r:ℝ)(hr:0<r):∀ m:ℕ,∃ N:ℕ,m ≤ N ∧∃ x:C.label d, T N x=x ∧ (∑ i∈I,‖snapshots i d (N,p) x‖)<r*‖x‖:=by
      have he : ¬ ∀ᶠ N in atTop,∀ x:C.label d,T N x=x → r*‖x‖ ≤ ∑ i∈I, ‖snapshots i d (N,p) x‖:= fun h=> he ⟨r,hr,h⟩
      simpa using he
   let r (i:ℕ):ℝ:= (↑i+1)⁻¹; have hr i:0 < r i:= by unfold r; positivity
   have hR:Tendsto r atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
   choose k hk x hx hp using fun i=> hf (r i) (hr i) i
   have hK:Tendsto k atTop atTop:= tendsto_atTop_mono (f:=id) hk tendsto_id -- implicit
   let l i:ℂ:= ‖x i‖⁻¹; let v i:= l i • x i
   have hb i: 0 < ‖x i‖:=by
       have hv:= lt_of_le_of_lt (Finset.sum_nonneg (f:= fun z=>‖snapshots z d (k i,p) (x i)‖) (fun _ _=> norm_nonneg _)) (hp i)
       exact pos_of_mul_pos_right hv (hr i).le -- left?
   have hl i:‖l i‖=‖x i‖⁻¹:=by unfold l; simp
   have hv(i): ‖v i‖=1:=by unfold v; rw [norm_smul,hl,inv_mul_cancel₀ (hb _|>.ne')]
   have hh(i): T (k i) (v i)=v i:=by unfold v; rw [map_smul,hx]
   have hT (i): ∑ j∈I, ‖snapshots j d (k i,p) (v i)‖≤ r i:=by
      unfold v; simp_rw [map_smul,norm_smul,hl,← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (hp _|>.le) (by positivity)).trans_eq (by field_simp [hb i|>.ne'])
   have hs: Spar (fun j=> T (k j)):=by obtain ⟨b,hb⟩:= Y.spends; exact ⟨b,hK.eventually hb⟩
   obtain ⟨u,Z,hZ⟩:=subsequence hs; obtain ⟨ζ,y,hy⟩:= subsequence (x:=fun j=> v (u j)) ⟨1, Eventually.of_forall fun i=> (hv (u i)).le⟩; let M i:= u (ζ i)
   obtain ⟨a,X,hA⟩:= scanMaps H Y K (hK.comp (u.cofinal.comp ζ.cofinal)) I hI
   let L i:= M (a i); have hL:Tendsto L atTop atTop:= (u.cofinal.comp ζ.cofinal).comp a.cofinal; have hw : Tendsto (fun i=>v (L i)) atTop (𝓝 y):=hy.comp a.cofinal; have hl : Tendsto (fun i=> T (k (L i))) atTop (𝓝 Z):= hZ.comp (ζ.cofinal.comp a.cofinal)
   have hY : ‖y‖ = 1:= tendsto_nhds_unique_of_eventuallyEq hw.norm tendsto_const_nhds (Eventually.of_forall fun i=> hv _)
   have he: Z y=y:= tendsto_nhds_unique_of_eventuallyEq (Dash.arcing hl hw) hw (Eventually.of_forall fun i=> hh _)
   suffices hx: ∀ i, X i y=0 by rw [← he,household H Y K I hI _ (hK.comp hL) X hA Z hl t ht _ hc h _ hx,norm_zero] at hY; exact zero_ne_one hY
   intro i; have he:= le_of_tendsto_of_tendsto ((Dash.arcing (hA i) hw).norm) (hR.comp hL) (Eventually.of_forall fun j=> ((Finset.single_le_sum (s:=I) (f:=fun x=>‖snapshots x d (k (L j),p) (v (L j))‖) (fun _ _=> norm_nonneg _) i.property).trans (hT _)))
   exact norm_le_zero_iff.mp he
end YM.UVExtension.Fallow
