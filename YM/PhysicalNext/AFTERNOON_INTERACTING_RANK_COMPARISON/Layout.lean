import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Sailing
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Sight


/-!
# Weighted accounting in sector calendar

Finish ticket compensation: *include* tag sums together with held
coordinates in the dependency check across disjoint X. `inter_spec`
used on physical A sectors after Ward tests. Deriving product in the
reference law used for the reweighting only, NOT independence in
normalized interacting law. `drawer`, `towards`: locality tests
for reference-sector data when changing V or adding more computation
far away.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Marker Value
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
    AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.RelativeLogdet AnalyticBridge.Sharp AnalyticBridge.Sharp.Tags
    GaugeRoute
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x τ : ℝ} {P : Teller G} {F : Orchard S} {U V : Config G c} {A B : Stores S}
    {k k' : S.Choices} {X : Support c}
abbrev vouchers (_S : StepData c f) := Finset (Cell f) × Finset (Bond c)

def stapled (x : ℝ) (D : vouchers S) (U : Config G c) : Stores S := ⟨D.1,D.2,RG.flags (temp x) U⟩
lemma position (x : ℝ) (D : vouchers S) (U : Config G c) : Positioned x (stapled x D U) U:=rfl
lemma drawer (D : vouchers S) (hU : Agrees X U V) (k : Streak F) : Nearby X U V (stapled x D U) (stapled x D V) k k := by
  refine ⟨hU,fun p hp=>?_,⟨fun _ _=>rfl,fun _ _ _=>rfl⟩,(Set.eqOn_refl ..),fun _ _=>Iff.rfl,fun _ _=> Iff.rfl⟩
  simp only [stapled, Stores.place,Finset.mem_union]
  refine or_congr Iff.rfl ?_
  let B : Support c :={p}
  have ht : ↑(RG.inspected B) ⊆ (X:Set (Site c)) := by
    intro i hi; obtain ⟨j,hj,hv⟩:= halo_spec.mp (Thirst.inspect B hi); rw [Finset.mem_singleton] at hj; exact hp i (by rw [hj] at hv; exact hv)
  have he:=flags_agree (temp x) U V B (agrees_mono hU ht)
  have h0 : p∈B∩flags (temp x) U ↔ p∈B∩flags (temp x) V:= by rw [he]
  simpa only [B,Finset.mem_inter,Finset.mem_singleton, true_and,eq_self] using h0

def wards (D : vouchers S) := D.1.biUnion (startPos S) ∪ D.2.biUnion pinPos
lemma towards (L N : vouchers S) (h : Disjoint X (wards N)) (x : ℝ) (U : Config G c) (k : Streak F) :
    Nearby X U U (stapled x L U) (stapled x (L⊔N) U) k k := by
  refine ⟨fun _ _ _=>rfl,fun i hi=> ?_,⟨fun _ _=>rfl,fun _ _ _=>rfl⟩,(Set.eqOn_refl ..),fun i hi=>?_,fun i hi=>?_⟩
  · have hz : i ∉ wards N:= Finset.disjoint_left.mp h hi.center
    change i∈wards L∪RG.flags (temp x) U↔ i∈wards (L⊔N)∪RG.flags (temp x) U
    have hp : wards (L⊔N)=wards L∪ wards N:= by
      change (L.1∪N.1).biUnion (startPos S)∪(L.2∪N.2).biUnion pinPos=_
      unfold wards; rw [Finset.union_biUnion, Finset.union_biUnion]; ext i
      simp only [Finset.mem_union]; tauto
    rw [hp]; simp only [Finset.mem_union,hz,or_false]
  · change _ ↔ i∈L.2∪N.2; rw [Finset.mem_union]; refine ⟨Or.inl, fun H=> H.resolve_right fun hz=>hi ?_⟩
    exact Disjoint.mono_left ((show pinPos i ⊆ wards N from fun t ht=>Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_,hz,ht⟩))) h.symm
  change _ ↔ i∈L.1∪N.1; rw [Finset.mem_union]; refine ⟨Or.inl, fun H=> H.resolve_right fun hz=>hi ?_⟩
  exact Disjoint.mono_left (show startPos S i ⊆ wards N from fun t ht => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨_,hz,ht⟩)) h.symm

section Avg
open Dictionary.Arbor
private lemma ticket_prices {ι : Type} [Fintype ι] (hm : S.patch.Branches S.kernel G)
    (X : ι → Support c) (g : ι→ S.Choices→ℂ) (hr : Pairwise (fun i j=> Disjoint (X i) (X j)))
    (h : ∀ i k l,Synchronized (X i) k l → g i k=g i l):
    (∑ k,tagRef k • ∏ i,g i k)= ∏ i,∑ k,tagRef k • g i k:= by
  let w:= (↑(Fintype.card S.Choices):ℝ)⁻¹
  have he (u : S.Choices→ℂ) : ∑ k,tagRef k • u k = (w:ℂ)*∑ k,u k:= by
    unfold tagRef; simp_rw [← Finset.smul_sum]; change w • _=_; rw [Complex.real_smul]
  rw [he _]; simp_rw [he (g _)]
  have ha (x : Bool) (j : ι) : peek x ((w:ℂ)*∑ k,g j k) = Tags.average (fun k=>peek x (g j k)) := by
    unfold peek Tags.average; dsimp only [w]; cases x <;> simp only [↓reduceIte,reduceCtorEq,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,Complex.re_sum,Complex.im_sum]
  let f(i:ι→Bool) (k : S.Choices) := ∏ j,peek (i j) (g j k)
  have hp (x : ι→Bool) : ∏ i,Tags.average (fun k=>peek (x i) (g i k)) = Tags.average (f x):=
    (Tags.uses hm X (fun i k=> peek (x i) (g i k)) (fun i k l p => congr_arg _ (h i k l p)) hr).symm
  conv_rhs=> rw [depart]
  simp_rw [ha,hp]
  simp_rw [fun k : S.Choices=> depart (fun i : ι=>g i k)]
  rw [Finset.sum_comm,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_
  unfold Tags.average f w; push_cast; rw [← Finset.mul_sum,mul_left_comm]
private lemma localSeeds {ι : Type} [Fintype ι] (X : ι → Support c) (g : ι→ F.Seeds → ℂ) (hr : Pairwise (fun i j=> Disjoint (X i) (X j)))
    (h : ∀ i k l, Set.EqOn k l ↑(X i)→g i k=g i l) :
    (∑ k:F.Seeds,F.solo • ∏ i,g i k)=∏ i,∑ k:F.Seeds,F.solo • g i k:=by
  -- product location splitting at selector tags (not assuming after-density law)
  let S' (u : F.Seeds→ℂ) := ∑ k,F.solo • u k
  have hx (t:ℂ): S' (fun _=>t)=t:= by dsimp only [S']; rw [←Finset.sum_smul,F.solo_one,one_smul]
  have hz (i) (L : F.Seeds→ℂ) (hl : ∀ k l:F.Seeds,Set.EqOn k l (X i:Set (Site c))ᶜ → L k=L l): S' (fun t=>g i t*L t)=S' (g i)*S' L:= by
    let E:=Equiv.piEquivPiSubtypeProd (fun x=>x∈(X i:Set (Site c))) (fun _=>Fin (F.put+1))
    let A:= ↥(X i:Set (Site c)) → Fin (F.put+1); let B:=↥((X i:Set (Site c))ᶜ) → Fin (F.put+1)
    let a (t:A):= g i (E.symm (t,Classical.ofNonempty)); let b (t:B):= L (E.symm (Classical.ofNonempty,t))
    have he (x:A) (y:B): g i (E.symm (x,y))=a x:= h _ _ _ (fun j hj=> by simp [E, Equiv.piEquivPiSubtypeProd_symm_apply,hj])
    have hβ (x:A) (y:B): L (E.symm (x,y))=b y:= hl _ _ (fun j hj=>by simp [E,Equiv.piEquivPiSubtypeProd_symm_apply,(show j∉X i from hj)])
    have hc (u : F.Seeds → ℂ) : S' u=(F.solo:ℂ)*∑ x:A,∑ y:B, u (E.symm (x,y)):=by dsimp only [S']; rw [← Finset.smul_sum,Complex.real_smul,← Equiv.sum_comp E.symm u,Fintype.sum_prod_type]; rfl
    have hr : (F.solo:ℂ)*∑ _x:A,∑ _y:B, (1:ℂ)=1:= Eq.trans (hc (fun _=>1)).symm (hx 1)
    rw [hc _,hc (g i),hc L]; simp_rw [he,hβ, ← Finset.mul_sum,← Finset.sum_mul]
    simp only [Finset.sum_const, card_univ,nsmul_eq_mul,mul_one] at hr ⊢
    rw [← Finset.mul_sum]; linear_combination -((∑ x:A, a x)*(∑ y:B,b y)*(F.solo:ℂ))*hr
  suffices H : ∀ s : Finset ι,S' (fun k=>∏ i∈s,g i k)=∏ i∈s,S' (g i) from H univ
  intro t; induction t using Finset.induction_on with
  | empty => simp only [prod_empty]; exact hx _
  | @insert i s hi ih=>
    let L : F.Seeds→ℂ := fun k =>∏ i∈s,g i k
    simp_rw [Finset.prod_insert hi]; rw [← ih]
    exact hz i L (fun u v he=> Finset.prod_congr rfl fun j hj=> h j u v (he.mono (by intro x hx ht; exact Finset.disjoint_left.mp (hr (ne_of_mem_of_not_mem hj hi)) hx ht)))

private lemma ticket_full {ι : Type} [Fintype ι] (hm : S.patch.Branches S.kernel G)
    (X : ι→Support c) (g : ι→ Streak F→ℂ) (hr : Pairwise (fun i j=> Disjoint (X i) (X j)))
    (h : ∀ i (k l : Streak F),Synchronized (X i) k.tag l.tag → Set.EqOn k.roots l.roots ↑(X i) → g i k=g i l):
    (∑ k:Streak F,k.share • ∏ i,g i k)=∏ i,∑ k:Streak F,k.share • g i k:=by
  have he (u : Streak F → ℂ) : ∑ k:Streak F,k.share • u k=∑ t:F.Seeds,F.solo • ∑ j:S.Choices, tagRef j • u ⟨t,j⟩ := by
    rw [← Equiv.sum_comp (Streak.entered S F).symm (fun k=> k.share • u k),Fintype.sum_prod_type]
    simp_rw [Finset.smul_sum,smul_smul]; rfl
  rw [he _]; simp_rw [he (g _)]
  let f i (t:F.Seeds) := ∑ j:S.Choices,tagRef j • g i ⟨t,j⟩
  refine Eq.trans ?_ (localSeeds X f hr fun i k l hz=> Finset.sum_congr rfl fun j _=> congr_arg ((tagRef j) • ·) (h _ _ _ ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩ hz))
  exact Finset.sum_congr rfl fun t _=> congr_arg ((F.solo:ℝ) • ·) (ticket_prices hm X (fun i j=>g i ⟨t,j⟩) hr (fun i k l hk=> h _ _ _ hk (Set.eqOn_refl ..)))
end Avg

section Shader
variable {D : Prop}

def glance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : Tube G S) (r : Shader G S x F E) (L : vouchers S) (U : Config G c) := ∑ k,Streak.share k • ∫ b,r (stapled x L U) k U b ∂viewer T (stapled x L U) x k.wood k.tag U
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma lamp_eq {g : Shader G S x F E} (hr : Sees g X D τ) (ht : Boosted T P x) (L : vouchers S) (h : Agrees X U V) (h' : auditFlags D τ X U V) : glance T g L U=glance T g L V := by
  exact Finset.sum_congr rfl fun k _=> congr_arg ((Streak.share k) • ·) (integrate_beam hr ht (position ..) (position ..) (drawer L h k) h').2
lemma lamp_meas {g : Shader G S x F E} (hr : Sees g X D τ) (ht : Boosted T P x) (L : vouchers S) : Measurable (glance T g L) := by
  apply Finset.measurable_fun_sum _ _; intro k _
  have hk (k : Streak F) : Measurable fun U=> ∫ b,g (stapled x L U) k U b ∂viewer T (stapled x L U) x k.wood k.tag U := by
    let a (i : Support c) : Stores S := ⟨L.1,L.2,i⟩
    choose w hw H using fun i=> shell_beacons ht (hr.placed (a i) k) k.tag
    let p (U : Config G c) := RG.flags (temp x) U
    have he U: (∫ b,g (stapled x L U) k U b ∂viewer T (stapled x L U) x k.wood k.tag U) =∑ i, ({u | p u=i} : Set (Config G c)).indicator (w i) U := by
      rw [Finset.sum_eq_single (p U)]
      · rw [Set.indicator_of_mem (by rfl : U∈{u|p u=p U})]; exact H _ U (position x L U)
      · intro i _ hi; exact Set.indicator_of_notMem (show U∉{u|p u=i} from fun e=> hi (Eq.symm e)) _
      simp
    simp_rw [he]; exact Finset.measurable_fun_sum _ fun i _=> (hw i).indicator (flags_measurable_eq ..)
  exact (measurable_const (a:=Streak.share k)).smul (hk k)
lemma lamp_turn {g : Shader G S x F E} (hr : Sees g X D τ) (ht : Boosted T P x) (L : vouchers S) : GaugeInvariant (glance T g L) := by
  intro v U; unfold glance
  have hh : stapled x L (Lattice.gauge v U) = stapled x L U:=by unfold stapled; rw [gauge_flags]
  rw [hh]
  exact Finset.sum_congr rfl fun k _=> congr_arg ((Streak.share k) • ·) (turn_beam hr ht (position ..) k _)

lemma inter_spec {ι : Type} (K : Finset ι) (X : ι→Support c) (p : ι→Shader G S x F ℂ) (ht : Boosted T P x) {Y : ι→Prop}
    (hr : ∀ i∈K,Sees (p i) (X i) (Y i) τ) (h : (K:Set ι).PairwiseDisjoint X) {L : vouchers S} {U : Config G c} {A : Stores S} (ha : A=stapled x L U)
    (hm : ∀ i∈K,∀ k,Integrable (p i A k U) (viewer T A x k.wood k.tag U)) :
    (∀ k : Streak F,Integrable (fun y=>∏ i∈K,p i A k U y) (viewer T A x k.wood k.tag U)) ∧
      glance T (fun A k U y=> ∏ i∈K,p i A k U y) L U=∏ i∈K,glance T (p i) L U := by
  subst A
  let A := stapled x L U; let w (i:K):= p i; let v (k : Streak F) := viewer T A x k.wood k.tag U
  have he (k : Streak F) y: (∏ i∈K,p i A k U y) =∏ i:K, w i A k U y:= by rw [← Finset.prod_coe_sort K]
  have hg: Pairwise (fun i j:K=> Disjoint (X i) (X j)) := fun i j hx=> h i.property j.property (mt Subtype.ext hx)
  let g(i:K) (k : Streak F):=∫ y,w i A k U y∂v k
  have hs k := peer_beams (fun i:K=>X i) w (fun i=>hr _ i.property) ht hg (position ..) k (fun i=>hm _ i.property k)
  have H i (k l:Streak F) (h : Synchronized (X (i:↥K)) k.tag l.tag) (h₂ : Set.EqOn k.roots l.roots ↑(X i)): g i k=g i l:= (integrate_beam (hr i i.property) ht (position x L U) (position ..) (Nearby.tickets h h₂) (fun _=>rfl)).2
  refine ⟨fun k=> (hs k).1.congr (Eventually.of_forall fun y=> (he _ _).symm),?_⟩
  rw [← Finset.prod_coe_sort K]
  change (∑ k,Streak.share k • ∫ y, (∏ i∈K,p i A k U y) ∂ v k) = ∏ i:K,∑ k,Streak.share k • g i k
  refine Eq.trans ?_ (ticket_full ht.produced.branched (fun i:K=>X i.val) g hg H)
  apply Finset.sum_congr rfl; intro k _
  exact congr_arg _ ((integral_congr_ae (μ:=v k) (Eventually.of_forall (he k))).trans (hs k).2)
end Shader
end YM.PhysicalNext.InteractingRank
